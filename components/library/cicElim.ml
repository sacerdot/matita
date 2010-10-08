(* Copyright (C) 2004, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://helm.cs.unibo.it/
 *)

(* $Id$ *)

open Printf

exception Elim_failure of string Lazy.t
exception Can_t_eliminate

let debug_print = fun _ -> ()
(*let debug_print s = prerr_endline (Lazy.force s) *)

let counter = ref ~-1 ;;

let fresh_binder () =  Cic.Name "matita_dummy"
(*
 incr counter;
 Cic.Name ("e" ^ string_of_int !counter) *)

  (** verifies if a given inductive type occurs in a term in target position *)
let rec recursive uri typeno = function
  | Cic.Prod (_, _, target) -> recursive uri typeno target
  | Cic.MutInd (uri', typeno', [])
  | Cic.Appl (Cic.MutInd  (uri', typeno', []) :: _) ->
      UriManager.eq uri uri' && typeno = typeno'
  | _ -> false

  (** given a list of constructor types, return true if at least one of them is
  * recursive, false otherwise *)
let recursive_type uri typeno constructors =
  let rec aux = function
    | Cic.Prod (_, src, tgt) -> recursive uri typeno src || aux tgt
    | _ -> false
  in
  List.exists (fun (_, ty) -> aux ty) constructors

let unfold_appl = function
  | Cic.Appl ((Cic.Appl args) :: tl) -> Cic.Appl (args @ tl)
  | t -> t

let rec split l n =
 match (l,n) with
    (l,0) -> ([], l)
  | (he::tl, n) -> let (l1,l2) = split tl (n-1) in (he::l1,l2)
  | (_,_) -> assert false

  (** build elimination principle part related to a single constructor
  * @param paramsno number of Prod to ignore in this constructor (i.e. number of
  * inductive parameters)
  * @param dependent true if we are in the dependent case (i.e. sort <> Prop) *)
let rec delta (uri, typeno) dependent paramsno consno t p args =
  match t with
  | Cic.MutInd (uri', typeno', []) when
    UriManager.eq uri uri' && typeno = typeno' ->
      if dependent then
        (match args with
        | [] -> assert false
        | [arg] -> unfold_appl (Cic.Appl [p; arg])
        | _ -> unfold_appl (Cic.Appl [p; unfold_appl (Cic.Appl args)]))
      else
        p
  | Cic.Appl (Cic.MutInd (uri', typeno', []) :: tl) when
    UriManager.eq uri uri' && typeno = typeno' ->
      let (lparams, rparams) = split tl paramsno in
      if dependent then
        (match args with
        | [] -> assert false
        | [arg] -> unfold_appl (Cic.Appl (p :: rparams @ [arg]))
        | _ ->
            unfold_appl (Cic.Appl (p ::
              rparams @ [unfold_appl (Cic.Appl args)])))
      else  (* non dependent *)
        (match rparams with
        | [] -> p
        | _ -> Cic.Appl (p :: rparams))
  | Cic.Prod (binder, src, tgt) ->
      if recursive uri typeno src then
        let args = List.map (CicSubstitution.lift 2) args in
        let phi =
          let src = CicSubstitution.lift 1 src in
          delta (uri, typeno) dependent paramsno consno src
            (CicSubstitution.lift 1 p) [Cic.Rel 1]
        in
        let tgt = CicSubstitution.lift 1 tgt in
        Cic.Prod (fresh_binder (), src,
          Cic.Prod (Cic.Anonymous, phi,
            delta (uri, typeno) dependent paramsno consno tgt
              (CicSubstitution.lift 2 p) (args @ [Cic.Rel 2])))
      else  (* non recursive *)
        let args = List.map (CicSubstitution.lift 1) args in
        Cic.Prod (fresh_binder (), src,
          delta (uri, typeno) dependent paramsno consno tgt
            (CicSubstitution.lift 1 p) (args @ [Cic.Rel 1]))
  | _ -> assert false

let rec strip_left_params consno leftno = function
  | t when leftno = 0 -> t (* no need to lift, the term is (hopefully) closed *)
  | Cic.Prod (_, _, tgt) (* when leftno > 0 *) ->
      (* after stripping the parameters we lift of consno. consno is 1 based so,
      * the first constructor will be lifted by 1 (for P), the second by 2 (1
      * for P and 1 for the 1st constructor), and so on *)
      if leftno = 1 then
        CicSubstitution.lift consno tgt
      else
        strip_left_params consno (leftno - 1) tgt
  | _ -> assert false

let delta (ury, typeno) dependent paramsno consno t p args =
  let t = strip_left_params consno paramsno t in
  delta (ury, typeno) dependent paramsno consno t p args

let rec add_params binder indno ty eliminator =
  if indno = 0 then
    eliminator
  else
    match ty with
    | Cic.Prod (name, src, tgt) ->
       let name =
        match name with
           Cic.Name _ -> name
         | Cic.Anonymous -> fresh_binder ()
       in
        binder name src (add_params binder (indno - 1) tgt eliminator)
    | _ -> assert false

let rec mk_rels consno = function
  | 0 -> []
  | n -> Cic.Rel (n+consno) :: mk_rels consno (n-1)

let rec strip_pi ctx t = 
  match CicReduction.whd ~delta:true ctx t with
  | Cic.Prod (n, s, tgt) -> strip_pi (Some (n,Cic.Decl s) :: ctx) tgt
  | t -> t

let strip_pi t = strip_pi [] t

let rec count_pi ctx t = 
  match CicReduction.whd ~delta:true ctx t with
  | Cic.Prod (n, s, tgt) -> count_pi (Some (n,Cic.Decl s)::ctx) tgt + 1
  | t -> 0

let count_pi t = count_pi [] t

let rec type_of_p sort dependent leftno indty = function
  | Cic.Prod (n, src, tgt) when leftno = 0 ->
      let n =
       if dependent then 
        match n with
           Cic.Name _ -> n
         | Cic.Anonymous -> fresh_binder ()
       else
        n
      in
       Cic.Prod (n, src, type_of_p sort dependent leftno indty tgt)
  | Cic.Prod (_, _, tgt) -> type_of_p sort dependent (leftno - 1) indty tgt
  | t ->
      if dependent then
        Cic.Prod (Cic.Anonymous, indty, Cic.Sort sort)
      else
        Cic.Sort sort

let rec add_right_pi dependent strip liftno liftfrom rightno indty = function
  | Cic.Prod (_, src, tgt) when strip = 0 ->
      Cic.Prod (fresh_binder (),
        CicSubstitution.lift_from liftfrom liftno src,
        add_right_pi dependent strip liftno (liftfrom + 1) rightno indty tgt)
  | Cic.Prod (_, _, tgt) ->
      add_right_pi dependent (strip - 1) liftno liftfrom rightno indty tgt
  | t ->
      if dependent then
        Cic.Prod (fresh_binder (),
          CicSubstitution.lift_from (rightno + 1) liftno indty,
          Cic.Appl (Cic.Rel (1 + liftno + rightno) :: mk_rels 0 (rightno + 1)))
      else
        Cic.Prod (Cic.Anonymous,
          CicSubstitution.lift_from (rightno + 1) liftno indty,
          if rightno = 0 then
            Cic.Rel (1 + liftno + rightno)
          else
            Cic.Appl (Cic.Rel (1 + liftno + rightno) :: mk_rels 1 rightno))

let rec add_right_lambda dependent strip liftno liftfrom rightno indty case =
function
  | Cic.Prod (_, src, tgt) when strip = 0 ->
      Cic.Lambda (fresh_binder (),
        CicSubstitution.lift_from liftfrom liftno src,
        add_right_lambda dependent strip liftno (liftfrom + 1) rightno indty
          case tgt)
  | Cic.Prod (_, _, tgt) ->
      add_right_lambda true (strip - 1) liftno liftfrom rightno indty
        case tgt
  | t ->
      Cic.Lambda (fresh_binder (),
        CicSubstitution.lift_from (rightno + 1) liftno indty, case)

let rec branch (uri, typeno) insource paramsno t fix head args =
  match t with
  | Cic.MutInd (uri', typeno', []) when
    UriManager.eq uri uri' && typeno = typeno' ->
      if insource then
        (match args with
        | [arg] -> Cic.Appl (fix :: args)
        | _ -> Cic.Appl (fix :: [Cic.Appl args]))
      else
        (match args with
        | [] -> head
        | _ -> Cic.Appl (head :: args))
  | Cic.Appl (Cic.MutInd (uri', typeno', []) :: tl) when
    UriManager.eq uri uri' && typeno = typeno' ->
      if insource then
        let (lparams, rparams) = split tl paramsno in
        match args with
        | [arg] -> Cic.Appl (fix :: rparams @ args)
        | _ -> Cic.Appl (fix :: rparams @ [Cic.Appl args])
      else
        (match args with
        | [] -> head
        | _ -> Cic.Appl (head :: args))
  | Cic.Prod (binder, src, tgt) ->
      if recursive uri typeno src then
        let args = List.map (CicSubstitution.lift 1) args in
        let phi =
          let fix = CicSubstitution.lift 1 fix in
          let src = CicSubstitution.lift 1 src in
          branch (uri, typeno) true paramsno src fix head [Cic.Rel 1]
        in
        Cic.Lambda (fresh_binder (), src,
          branch (uri, typeno) insource paramsno tgt
            (CicSubstitution.lift 1 fix) (CicSubstitution.lift 1 head)
            (args @ [Cic.Rel 1; phi]))
      else  (* non recursive *)
        let args = List.map (CicSubstitution.lift 1) args in
        Cic.Lambda (fresh_binder (), src,
          branch (uri, typeno) insource paramsno tgt
          (CicSubstitution.lift 1 fix) (CicSubstitution.lift 1 head)
            (args @ [Cic.Rel 1]))
  | _ -> assert false

let branch (uri, typeno) insource liftno paramsno t fix head args =
  let t = strip_left_params liftno paramsno t in
  branch (uri, typeno) insource paramsno t fix head args

let elim_of ~sort uri typeno =
  counter := ~-1;
  let (obj, univ) = (CicEnvironment.get_obj CicUniv.oblivion_ugraph uri) in
  match obj with
  | Cic.InductiveDefinition (indTypes, params, leftno, _) ->
      let (name, inductive, ty, constructors) =
        try
          List.nth indTypes typeno
        with Failure _ -> assert false
      in
      let ty = Unshare.unshare ~fresh_univs:true ty in
      let constructors = 
        List.map (fun (name,c)-> name,Unshare.unshare ~fresh_univs:true c) constructors 
      in
      let paramsno = count_pi ty in (* number of (left or right) parameters *)
      let rightno = paramsno - leftno in
      let dependent = (strip_pi ty <> Cic.Sort Cic.Prop) in
      let head =
       match strip_pi ty with
          Cic.Sort s -> s
        | _ -> assert false
      in
      let conslen = List.length constructors in
      let consno = ref (conslen + 1) in
      if
       not
        (CicTypeChecker.check_allowed_sort_elimination uri typeno head sort)
      then
       raise Can_t_eliminate;
      let indty =
        let indty = Cic.MutInd (uri, typeno, []) in
        if paramsno = 0 then
          indty
        else
          Cic.Appl (indty :: mk_rels 0 paramsno)
      in
      let mk_constructor consno =
        let constructor = Cic.MutConstruct (uri, typeno, consno, []) in
        if leftno = 0 then
          constructor
        else
          Cic.Appl (constructor :: mk_rels consno leftno)
      in
      let p_ty = type_of_p sort dependent leftno indty ty in
      let final_ty =
        add_right_pi dependent leftno (conslen + 1) 1 rightno indty ty
      in
      let eliminator_type =
        let cic =
          Cic.Prod (Cic.Name "P", p_ty,
            (List.fold_right
              (fun (_, constructor) acc ->
                decr consno;
                let p = Cic.Rel !consno in
                Cic.Prod (Cic.Anonymous,
                  (delta (uri, typeno) dependent leftno !consno
                    constructor p [mk_constructor !consno]),
                  acc))
              constructors final_ty))
        in
        add_params (fun b s t -> Cic.Prod (b, s, t)) leftno ty cic
      in
      let consno = ref (conslen + 1) in
      let eliminator_body =
        let fix = Cic.Rel (rightno + 2) in
        let is_recursive = recursive_type uri typeno constructors in
        let recshift = if is_recursive then 1 else 0 in
        let (_, branches) =
          List.fold_right
            (fun (_, ty) (shift, branches) ->
              let head = Cic.Rel (rightno + shift + 1 + recshift) in
              let b =
                branch (uri, typeno) false
                  (rightno + conslen + 2 + recshift) leftno ty fix head []
              in
              (shift + 1,  b :: branches))
            constructors (1, [])
        in
        let shiftno  = conslen + rightno + 2 + recshift in
        let outtype =
         if dependent then
          Cic.Rel shiftno
         else
          let head =
           if rightno = 0 then
            CicSubstitution.lift 1 (Cic.Rel shiftno)
           else
            Cic.Appl
             ((CicSubstitution.lift (rightno + 1) (Cic.Rel shiftno)) ::
              mk_rels 1 rightno)
          in
           add_right_lambda true leftno shiftno 1 rightno indty head ty
        in
        let mutcase =
          Cic.MutCase (uri, typeno, outtype, Cic.Rel 1, branches)
        in
        let body =
          if is_recursive then
            let fixfun =
              add_right_lambda dependent leftno (conslen + 2) 1 rightno
                indty mutcase ty
            in
            (* rightno is the decreasing argument, i.e. the argument of
             * inductive type *)
            Cic.Fix (0, ["aux", rightno, final_ty, fixfun])
          else
            add_right_lambda dependent leftno (conslen + 1) 1 rightno indty
              mutcase ty
        in
        let cic =
          Cic.Lambda (Cic.Name "P", p_ty,
            (List.fold_right
              (fun (_, constructor) acc ->
                decr consno;
                let p = Cic.Rel !consno in
                Cic.Lambda (fresh_binder (),
                  (delta (uri, typeno) dependent leftno !consno
                    constructor p [mk_constructor !consno]),
                  acc))
              constructors body))
        in
        add_params (fun b s t -> Cic.Lambda (b, s, t)) leftno ty cic
      in
(*
debug_print (lazy (CicPp.ppterm eliminator_type));
debug_print (lazy (CicPp.ppterm eliminator_body));
*)
      let eliminator_type = 
	FreshNamesGenerator.mk_fresh_names [] [] [] eliminator_type in
      let eliminator_body = 
	FreshNamesGenerator.mk_fresh_names [] [] [] eliminator_body in
(*
debug_print (lazy (CicPp.ppterm eliminator_type));
debug_print (lazy (CicPp.ppterm eliminator_body));
*)
      let (computed_type, ugraph) =
        try
          CicTypeChecker.type_of_aux' [] [] eliminator_body
          CicUniv.oblivion_ugraph
        with CicTypeChecker.TypeCheckerFailure msg ->
          raise (Elim_failure (lazy (sprintf 
            "type checker failure while type checking:\n%s\nerror:\n%s"
            (CicPp.ppterm eliminator_body) (Lazy.force msg))))
      in
      if not (fst (CicReduction.are_convertible []
        eliminator_type computed_type ugraph))
      then
        raise (Failure (sprintf
          "internal error: type mismatch on eliminator type\n%s\n%s"
          (CicPp.ppterm eliminator_type) (CicPp.ppterm computed_type)));
      let suffix =
        match sort with
        | Cic.Prop -> "_ind"
        | Cic.Set -> "_rec"
        | Cic.Type _ -> "_rect"
        | _ -> assert false
      in
      (* let name = UriManager.name_of_uri uri ^ suffix in *)
      let name = name ^ suffix in
      let buri = UriManager.buri_of_uri uri in
      let uri = UriManager.uri_of_string (buri ^ "/" ^ name ^ ".con") in
      let obj_attrs = [`Class (`Elim sort); `Generated] in
       uri,
       Cic.Constant (name, Some eliminator_body, eliminator_type, [], obj_attrs)
  | _ ->
      failwith (sprintf "not an inductive definition (%s)"
        (UriManager.string_of_uri uri))
;;

let generate_elimination_principles ~add_obj ~add_coercion uri obj =
 match obj with
  | Cic.InductiveDefinition (indTypes,_,_,attrs) ->
     let _,inductive,_,_ = List.hd indTypes in
     if not inductive then []
     else
      let _,all_eliminators =
        List.fold_left
          (fun (i,res) _ ->
            let elim sort =
              try Some (elim_of ~sort uri i)
              with Can_t_eliminate -> None
            in
             i+1,
              HExtlib.filter_map 
               elim [ Cic.Prop; Cic.Set; (Cic.Type (CicUniv.fresh ())) ] @ res
          ) (0,[]) indTypes
      in
      List.fold_left
        (fun lemmas (uri,obj) -> add_obj uri obj @ uri::lemmas) 
        [] all_eliminators
  | _ -> []
;;


let init () = 
  LibrarySync.add_object_declaration_hook generate_elimination_principles;;
