(*
Copyright (C) 1999-2006, HELM Team.

This file is part of HELM, an Hypertextual, Electronic
Library of Mathematics, developed at the Computer Science
Department, University of Bologna, Italy.

HELM is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

HELM is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
02110-1301 USA.

For details, see the HELM web site: http://helm.cs.unibo.it/
*)

open Printf
module Ast = CicNotationPt

let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s) else ()

let rec string_context_of_context =
 List.map
  (function
   | Cic.Name n -> Some n
   | Cic.Anonymous -> Some "_")
;;

let refine_term metasenv subst context uri ~use_coercions
 term expty ugraph ~localization_tbl =
(*   if benchmark then incr actual_refinements; *)
  assert (uri=None);
  debug_print (lazy (sprintf "TEST_INTERPRETATION: %s" (CicPp.ppterm term)));
  let saved_use_coercions = !CicRefine.insert_coercions in
  try
    CicRefine.insert_coercions := use_coercions;
    let term = 
      match expty with
      | None -> term
      | Some ty -> Cic.Cast(term,ty)
    in
    let term', _, metasenv',ugraph1 = 
	    CicRefine.type_of_aux' metasenv context term ugraph ~localization_tbl
    in
    let term' = 
      match expty, term' with
      | None,_ -> term'
      | Some _,Cic.Cast (term',_) -> term'
      | _ -> assert false 
    in
     CicRefine.insert_coercions := saved_use_coercions;
     (Disambiguate.Ok (term', metasenv',[],ugraph1))
  with
   exn ->
    CicRefine.insert_coercions := saved_use_coercions;
    let rec process_exn loc =
     function
        HExtlib.Localized (loc,exn) -> process_exn loc exn
      | CicRefine.Uncertain msg ->
          debug_print (lazy ("UNCERTAIN!!! [" ^ (Lazy.force msg) ^ "] " ^ CicPp.ppterm term)) ;
          Disambiguate.Uncertain (lazy (loc,Lazy.force msg))
      | CicRefine.RefineFailure msg ->
          debug_print (lazy (sprintf "PRUNED!!!\nterm%s\nmessage:%s"
            (CicPp.ppterm term) (Lazy.force msg)));
          Disambiguate.Ko (lazy (loc,Lazy.force msg))
     | exn -> raise exn
    in
     process_exn Stdpp.dummy_loc exn

let refine_obj metasenv subst context uri ~use_coercions obj _ ugraph
 ~localization_tbl =
   assert (context = []);
   assert (metasenv = []);
   assert (subst = []);
   debug_print (lazy (sprintf "TEST_INTERPRETATION: %s" (CicPp.ppobj obj))) ;
   let saved_use_coercions = !CicRefine.insert_coercions in
   try
     CicRefine.insert_coercions := use_coercions;
     let obj', metasenv,ugraph =
       CicRefine.typecheck metasenv uri obj ~localization_tbl
     in
      CicRefine.insert_coercions := saved_use_coercions;
      (Disambiguate.Ok (obj', metasenv,[],ugraph))
   with
     exn ->
      CicRefine.insert_coercions := saved_use_coercions;
      let rec process_exn loc =
       function
          HExtlib.Localized (loc,exn) -> process_exn loc exn
        | CicRefine.Uncertain msg ->
            debug_print (lazy ("UNCERTAIN!!! [" ^ 
              (Lazy.force msg) ^ "] " ^ CicPp.ppobj obj)) ;
            Disambiguate.Uncertain (lazy (loc,Lazy.force msg))
        | CicRefine.RefineFailure msg ->
            debug_print (lazy (sprintf "PRUNED!!!\nterm%s\nmessage:%s"
              (CicPp.ppobj obj) (Lazy.force msg))) ;
            Disambiguate.Ko (lazy (loc,Lazy.force msg))
       | exn -> raise exn
      in
       process_exn Stdpp.dummy_loc exn
;;

let interpretate_term ~mk_choice ?(create_dummy_ids=false) ~context ~env ~uri
 ~is_path ast ~localization_tbl ~obj_context
=
  (* create_dummy_ids shouldbe used only for interpretating patterns *)
  assert (uri = None);
  let rec aux ~localize loc context = function
    | CicNotationPt.AttributedTerm (`Loc loc, term) ->
        let res = aux ~localize loc context term in
         if localize then Cic.CicHash.add localization_tbl res loc;
         res
    | CicNotationPt.AttributedTerm (_, term) -> aux ~localize loc context term
    | CicNotationPt.Appl (CicNotationPt.Symbol (symb, i) :: args) ->
        let cic_args = List.map (aux ~localize loc context) args in
        Disambiguate.resolve ~mk_choice ~env 
          (DisambiguateTypes.Symbol (symb, i)) (`Args cic_args)
    | CicNotationPt.Appl terms ->
       Cic.Appl (List.map (aux ~localize loc context) terms)
    | CicNotationPt.Binder (binder_kind, (var, typ), body) ->
        let cic_type = aux_option ~localize loc context (Some `Type) typ in
        let cic_name = CicNotationUtil.cic_name_of_name var in
        let cic_body = aux ~localize loc (cic_name :: context) body in
        (match binder_kind with
        | `Lambda -> Cic.Lambda (cic_name, cic_type, cic_body)
        | `Pi
        | `Forall -> Cic.Prod (cic_name, cic_type, cic_body)
        | `Exists ->
            Disambiguate.resolve ~mk_choice ~env
             (DisambiguateTypes.Symbol ("exists", 0))
             (`Args [ cic_type; Cic.Lambda (cic_name, cic_type, cic_body) ]))
    | CicNotationPt.Case (term, indty_ident, outtype, branches) ->
        let cic_term = aux ~localize loc context term in
        let cic_outtype = aux_option ~localize loc context None outtype in
        let do_branch ((head, _, args), term) =
         let rec do_branch' context = function
           | [] -> aux ~localize loc context term
           | (name, typ) :: tl ->
               let cic_name = CicNotationUtil.cic_name_of_name name in
               let cic_body = do_branch' (cic_name :: context) tl in
               let typ =
                 match typ with
                 | None -> Cic.Implicit (Some `Type)
                 | Some typ -> aux ~localize loc context typ
               in
               Cic.Lambda (cic_name, typ, cic_body)
         in
          do_branch' context args
        in
        let indtype_uri, indtype_no =
          if create_dummy_ids then
            (UriManager.uri_of_string "cic:/fake_indty.con", 0)
          else
          match indty_ident with
          | Some (indty_ident, _) ->
             (match 
               Disambiguate.resolve ~mk_choice ~env 
                (DisambiguateTypes.Id indty_ident) (`Args [])
              with
              | Cic.MutInd (uri, tyno, _) -> (uri, tyno)
              | Cic.Implicit _ ->
                 raise (Disambiguate.Try_again 
                   (lazy "The type of the term to be matched
                  is still unknown"))
              | _ ->
                raise (DisambiguateTypes.Invalid_choice (lazy (loc,"The type of the term to be matched is not (co)inductive!"))))
          | None ->
              let rec fst_constructor =
                function
                   (Ast.Pattern (head, _, _), _) :: _ -> head
                 | (Ast.Wildcard, _) :: tl -> fst_constructor tl
                 | [] -> raise (DisambiguateTypes.Invalid_choice (lazy (loc,"The type of the term to be matched cannot be determined because it is an inductive type without constructors or because all patterns use wildcards")))
              in
              (match Disambiguate.resolve ~mk_choice ~env
                (DisambiguateTypes.Id (fst_constructor branches))
                (`Args []) with
              | Cic.MutConstruct (indtype_uri, indtype_no, _, _) ->
                  (indtype_uri, indtype_no)
              | Cic.Implicit _ ->
                 raise (Disambiguate.Try_again (lazy "The type of the term to be matched
                  is still unknown"))
              | _ ->
                raise (DisambiguateTypes.Invalid_choice (lazy (loc,"The type of the term to be matched is not (co)inductive!"))))
        in
        let branches =
         if create_dummy_ids then
          List.map
           (function
               Ast.Wildcard,term -> ("wildcard",None,[]), term
             | Ast.Pattern _,_ ->
                raise (DisambiguateTypes.Invalid_choice (lazy (loc, "Syntax error: the left hand side of a branch patterns must be \"_\"")))
           ) branches
         else
         match fst(CicEnvironment.get_obj CicUniv.oblivion_ugraph indtype_uri) with
            Cic.InductiveDefinition (il,_,leftsno,_) ->
             let _,_,_,cl =
              try
               List.nth il indtype_no
              with _ -> assert false
             in
              let rec count_prod t =
                match CicReduction.whd [] t with
                    Cic.Prod (_, _, t) -> 1 + (count_prod t)
                  | _ -> 0 
              in 
              let rec sort branches cl =
               match cl with
                  [] ->
                   let rec analyze unused unrecognized useless =
                    function
                       [] ->
                        if unrecognized != [] then
                         raise (DisambiguateTypes.Invalid_choice
                          (lazy (loc,
                            ("Unrecognized constructors: " ^
                             String.concat " " unrecognized))))
                        else if useless > 0 then
                         raise (DisambiguateTypes.Invalid_choice
                           (lazy (loc,
                            ("The last " ^ string_of_int useless ^
                             "case" ^ if useless > 1 then "s are" else " is" ^
                             " unused"))))
                        else
                         []
                     | (Ast.Wildcard,_)::tl when not unused ->
                         analyze true unrecognized useless tl
                     | (Ast.Pattern (head,_,_),_)::tl when not unused ->
                         analyze unused (head::unrecognized) useless tl
                     | _::tl -> analyze unused unrecognized (useless + 1) tl
                   in
                    analyze false [] 0 branches
                | (name,ty)::cltl ->
                   let rec find_and_remove =
                    function
                       [] ->
                        raise
                         (DisambiguateTypes.Invalid_choice
                          (lazy (loc, ("Missing case: " ^ name))))
                     | ((Ast.Wildcard, _) as branch :: _) as branches ->
                         branch, branches
                     | (Ast.Pattern (name',_,_),_) as branch :: tl
                        when name = name' ->
                         branch,tl
                     | branch::tl ->
                        let found,rest = find_and_remove tl in
                         found, branch::rest
                   in
                    let branch,tl = find_and_remove branches in
                    match branch with
                       Ast.Pattern (name,y,args),term ->
                        if List.length args = count_prod ty - leftsno then
                         ((name,y,args),term)::sort tl cltl
                        else
                         raise
                          (DisambiguateTypes.Invalid_choice
                            (lazy (loc,"Wrong number of arguments for " ^
                            name)))
                     | Ast.Wildcard,term ->
                        let rec mk_lambdas =
                         function
                            0 -> term
                          | n ->
                             CicNotationPt.Binder
                              (`Lambda, (CicNotationPt.Ident ("_", None), None),
                                mk_lambdas (n - 1))
                        in
                         (("wildcard",None,[]),
                          mk_lambdas (count_prod ty - leftsno)) :: sort tl cltl
              in
               sort branches cl
          | _ -> assert false
        in
        Cic.MutCase (indtype_uri, indtype_no, cic_outtype, cic_term,
          (List.map do_branch branches))
    | CicNotationPt.Cast (t1, t2) ->
        let cic_t1 = aux ~localize loc context t1 in
        let cic_t2 = aux ~localize loc context t2 in
        Cic.Cast (cic_t1, cic_t2)
    | CicNotationPt.LetIn ((name, typ), def, body) ->
        let cic_def = aux ~localize loc context def in
        let cic_name = CicNotationUtil.cic_name_of_name name in
        let cic_typ =
          match typ with
          | None -> Cic.Implicit (Some `Type)
          | Some t -> aux ~localize loc context t
        in
        let cic_body = aux ~localize loc (cic_name :: context) body in
        Cic.LetIn (cic_name, cic_def, cic_typ, cic_body)
    | CicNotationPt.LetRec (kind, defs, body) ->
        let context' =
          List.fold_left
            (fun acc (_, (name, _), _, _) ->
              CicNotationUtil.cic_name_of_name name :: acc)
            context defs
        in
        let cic_body =
         let unlocalized_body = aux ~localize:false loc context' body in
         match unlocalized_body with
            Cic.Rel n when n <= List.length defs -> `AvoidLetInNoAppl n
          | Cic.Appl (Cic.Rel n::l) when n <= List.length defs ->
             (try
               let l' =
                List.map
                 (function t ->
                   let t',subst,metasenv =
                    CicMetaSubst.delift_rels [] [] (List.length defs) t
                   in
                    assert (subst=[]);
                    assert (metasenv=[]);
                    t') l
               in
                (* We can avoid the LetIn. But maybe we need to recompute l'
                   so that it is localized *)
                if localize then
                 match body with
                    CicNotationPt.AttributedTerm (_,CicNotationPt.Appl(_::l)) ->
                     (* since we avoid the letin, the context has no
                      * recfuns in it *)
                     let l' = List.map (aux ~localize loc context) l in
                      `AvoidLetIn (n,l')
                  | _ -> assert false
                else
                 `AvoidLetIn (n,l')
              with
               CicMetaSubst.DeliftingARelWouldCaptureAFreeVariable ->
                if localize then
                 `AddLetIn (aux ~localize loc context' body)
                else
                 `AddLetIn unlocalized_body)
          | _ ->
             if localize then
              `AddLetIn (aux ~localize loc context' body)
             else
              `AddLetIn unlocalized_body
        in
        let inductiveFuns =
          List.map
            (fun (params, (name, typ), body, decr_idx) ->
              let add_binders kind t =
               List.fold_right
                (fun var t -> CicNotationPt.Binder (kind, var, t)) params t
              in
              let cic_body =
               aux ~localize loc context' (add_binders `Lambda body) in
              let typ =
               match typ with
                  Some typ -> typ
                | None-> CicNotationPt.Implicit `JustOne in
              let cic_type =
               aux_option ~localize loc context (Some `Type)
                (Some (add_binders `Pi typ)) in
              let name =
                match CicNotationUtil.cic_name_of_name name with
                | Cic.Anonymous ->
                    CicNotationPt.fail loc
                      "Recursive functions cannot be anonymous"
                | Cic.Name name -> name
              in
              (name, decr_idx, cic_type, cic_body))
            defs
        in
        let fix_or_cofix n =
         match kind with
            `Inductive -> Cic.Fix (n,inductiveFuns)
          | `CoInductive ->
              let coinductiveFuns =
                List.map
                 (fun (name, _, typ, body) -> name, typ, body)
                 inductiveFuns
              in
               Cic.CoFix (n,coinductiveFuns)
        in
         let counter = ref ~-1 in
         let build_term funs (var,_,ty,_) t =
          incr counter;
          Cic.LetIn (Cic.Name var, fix_or_cofix !counter, ty, t)
         in
          (match cic_body with
              `AvoidLetInNoAppl n ->
                let n' = List.length inductiveFuns - n in
                 fix_or_cofix n'
            | `AvoidLetIn (n,l) ->
                let n' = List.length inductiveFuns - n in
                 Cic.Appl (fix_or_cofix n'::l)
            | `AddLetIn cic_body ->         
                List.fold_right (build_term inductiveFuns) inductiveFuns
                 cic_body)
    | CicNotationPt.Ident _
    | CicNotationPt.Uri _
    | CicNotationPt.NRef _ when is_path -> raise Disambiguate.PathNotWellFormed
    | CicNotationPt.NCic _ -> assert false
    | CicNotationPt.NRef _ -> assert false
    | CicNotationPt.Ident (name,subst)
    | CicNotationPt.Uri (name, subst) as ast ->
        let is_uri = function CicNotationPt.Uri _ -> true | _ -> false in
        (try
          if is_uri ast then raise Not_found;(* don't search the env for URIs *)
          let index =
           Disambiguate.find_in_context name (string_context_of_context context)
          in
          if subst <> None then
            CicNotationPt.fail loc "Explicit substitutions not allowed here";
          Cic.Rel index
        with Not_found ->
          let cic =
            if is_uri ast then  (* we have the URI, build the term out of it *)
              try
                CicUtil.term_of_uri (UriManager.uri_of_string name)
              with UriManager.IllFormedUri _ ->
                CicNotationPt.fail loc "Ill formed URI"
            else
             try
              List.assoc name obj_context
             with
              Not_found ->
               Disambiguate.resolve ~mk_choice ~env
                (DisambiguateTypes.Id name) (`Args [])
          in
          let mk_subst uris =
            let ids_to_uris =
              List.map (fun uri -> UriManager.name_of_uri uri, uri) uris
            in
            (match subst with
            | Some subst ->
                List.map
                  (fun (s, term) ->
                    (try
                      List.assoc s ids_to_uris, aux ~localize loc context term
                     with Not_found ->
                       raise (DisambiguateTypes.Invalid_choice (lazy (loc, "The provided explicit named substitution is trying to instantiate a named variable the object is not abstracted on")))))
                  subst
            | None -> List.map (fun uri -> uri, Cic.Implicit None) uris)
          in
          (try 
            match cic with
            | Cic.Const (uri, []) ->
                let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
                let uris = CicUtil.params_of_obj o in
                Cic.Const (uri, mk_subst uris)
            | Cic.Var (uri, []) ->
                let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
                let uris = CicUtil.params_of_obj o in
                Cic.Var (uri, mk_subst uris)
            | Cic.MutInd (uri, i, []) ->
               (try
                 let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
                 let uris = CicUtil.params_of_obj o in
                 Cic.MutInd (uri, i, mk_subst uris)
                with
                 CicEnvironment.Object_not_found _ ->
                  (* if we are here it is probably the case that during the
                     definition of a mutual inductive type we have met an
                     occurrence of the type in one of its constructors.
                     However, the inductive type is not yet in the environment
                  *)
                  (*here the explicit_named_substituion is assumed to be of length 0 *)
                  Cic.MutInd (uri,i,[]))
            | Cic.MutConstruct (uri, i, j, []) ->
                let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
                let uris = CicUtil.params_of_obj o in
                Cic.MutConstruct (uri, i, j, mk_subst uris)
            | Cic.Meta _ | Cic.Implicit _ as t ->
(*
                debug_print (lazy (sprintf
                  "Warning: %s must be instantiated with _[%s] but we do not enforce it"
                  (CicPp.ppterm t)
                  (String.concat "; "
                    (List.map
                      (fun (s, term) -> s ^ " := " ^ CicNotationPtPp.pp_term term)
                      subst))));
*)
                t
            | _ ->
              raise (DisambiguateTypes.Invalid_choice (lazy (loc, "??? Can this happen?")))
           with 
             CicEnvironment.CircularDependency _ -> 
               raise (DisambiguateTypes.Invalid_choice (lazy (loc,"Circular dependency in the environment")))))
    | CicNotationPt.Implicit `Vector -> assert false
    | CicNotationPt.Implicit (`JustOne | `Tagged _) -> Cic.Implicit None
    | CicNotationPt.UserInput -> Cic.Implicit (Some `Hole)
    | CicNotationPt.Num (num, i) ->
       Disambiguate.resolve ~mk_choice ~env
        (DisambiguateTypes.Num i) (`Num_arg num)
    | CicNotationPt.Meta (index, subst) ->
        let cic_subst =
          List.map
            (function
                None -> None
              | Some term -> Some (aux ~localize loc context term))
            subst
        in
        Cic.Meta (index, cic_subst)
    | CicNotationPt.Sort `Prop -> Cic.Sort Cic.Prop
    | CicNotationPt.Sort `Set -> Cic.Sort Cic.Set
    | CicNotationPt.Sort (`Type u) -> Cic.Sort (Cic.Type u)
    | CicNotationPt.Sort (`NType _) -> Cic.Sort (Cic.Type (CicUniv.fresh ()))
    | CicNotationPt.Sort (`NCProp _) -> Cic.Sort (Cic.CProp (CicUniv.fresh ()))
    | CicNotationPt.Sort (`CProp u) -> Cic.Sort (Cic.CProp u)
    | CicNotationPt.Symbol (symbol, instance) ->
        Disambiguate.resolve ~mk_choice ~env
         (DisambiguateTypes.Symbol (symbol, instance)) (`Args [])
    | CicNotationPt.Variable _
    | CicNotationPt.Magic _
    | CicNotationPt.Layout _
    | CicNotationPt.Literal _ -> assert false (* god bless Bologna *)
  and aux_option ~localize loc context annotation = function
    | None -> Cic.Implicit annotation
    | Some term -> aux ~localize loc context term
  in
   aux ~localize:true HExtlib.dummy_floc context ast

let interpretate_path ~context path =
 let localization_tbl = Cic.CicHash.create 23 in
  (* here we are throwing away useful localization informations!!! *)
  fst (
   interpretate_term ~mk_choice:(fun _ -> assert false) ~create_dummy_ids:true 
    ~context ~env:DisambiguateTypes.Environment.empty ~uri:None ~is_path:true
    path ~localization_tbl ~obj_context:[], localization_tbl)

let interpretate_obj ~mk_choice ~context ~env ~uri ~is_path obj
 ~localization_tbl
=
 assert (context = []);
 assert (is_path = false);
 let interpretate_term ?(obj_context=[]) =
  interpretate_term ~mk_choice ~localization_tbl ~obj_context in
 match obj with
  | CicNotationPt.Inductive (params,tyl) ->
     let uri = match uri with Some uri -> uri | None -> assert false in
     let context,params =
      let context,res =
       List.fold_left
        (fun (context,res) (name,t) ->
          let t =
           match t with
              None -> CicNotationPt.Implicit `JustOne
            | Some t -> t in
          let name = CicNotationUtil.cic_name_of_name name in
           name::context,(name, interpretate_term context env None false t)::res
        ) ([],[]) params
      in
       context,List.rev res in
     let add_params =
      List.fold_right (fun (name,ty) t -> Cic.Prod (name,ty,t)) params in
     let obj_context =
      snd (
       List.fold_left
        (*here the explicit_named_substituion is assumed to be of length 0 *)
        (fun (i,res) (name,_,_,_) -> i + 1,(name,Cic.MutInd (uri,i,[]))::res)
        (0,[]) tyl) in
     let tyl =
      List.map
       (fun (name,b,ty,cl) ->
         let ty' = add_params (interpretate_term context env None false ty) in
         let cl' =
          List.map
           (fun (name,ty) ->
             let ty' =
              add_params
               (interpretate_term ~obj_context ~context ~env ~uri:None
                 ~is_path:false ty)
             in
              name,ty'
           ) cl
         in
          name,b,ty',cl'
       ) tyl
     in
      Cic.InductiveDefinition (tyl,[],List.length params,[])
  | CicNotationPt.Record (params,name,ty,fields) ->
     let uri = match uri with Some uri -> uri | None -> assert false in
     let context,params =
      let context,res =
       List.fold_left
        (fun (context,res) (name,t) ->
          let t =
           match t with
              None -> CicNotationPt.Implicit `JustOne
            | Some t -> t in
          let name = CicNotationUtil.cic_name_of_name name in
           name::context,(name, interpretate_term context env None false t)::res
        ) ([],[]) params
      in
       context,List.rev res in
     let add_params =
      List.fold_right
       (fun (name,ty) t -> Cic.Prod (name,ty,t)) params in
     let ty' = add_params (interpretate_term context env None false ty) in
     let fields' =
      snd (
       List.fold_left
        (fun (context,res) (name,ty,_coercion,arity) ->
          let context' = Cic.Name name :: context in
           context',(name,interpretate_term context env None false ty)::res
        ) (context,[]) fields) in
     let concl =
      (*here the explicit_named_substituion is assumed to be of length 0 *)
      let mutind = Cic.MutInd (uri,0,[]) in
      if params = [] then mutind
      else
       Cic.Appl
        (mutind::CicUtil.mk_rels (List.length params) (List.length fields)) in
     let con =
      List.fold_left
       (fun t (name,ty) -> Cic.Prod (Cic.Name name,ty,t))
       concl fields' in
     let con' = add_params con in
     let tyl = [name,true,ty',["mk_" ^ name,con']] in
     let field_names = List.map (fun (x,_,y,z) -> x,y,z) fields in
      Cic.InductiveDefinition
       (tyl,[],List.length params,[`Class (`Record field_names)])
  | CicNotationPt.Theorem (flavour, name, ty, bo, _pragma) ->
     let attrs = [`Flavour flavour] in
     let ty' = interpretate_term [] env None false ty in
     (match bo,flavour with
        None,`Axiom ->
         Cic.Constant (name,None,ty',[],attrs)
      | Some bo,`Axiom -> assert false
      | None,_ ->
         Cic.CurrentProof (name,[],Cic.Implicit None,ty',[],attrs)
      | Some bo,_ ->
         let bo' = Some (interpretate_term [] env None false bo) in
          Cic.Constant (name,bo',ty',[],attrs))
;;

let interpretate_term ~mk_choice ?(create_dummy_ids=false) ~context ~env ~uri
 ~is_path ast ~localization_tbl
=
  let context =
   List.map (function None -> Cic.Anonymous | Some (n,_) -> n) context
  in
   interpretate_term ~mk_choice ~create_dummy_ids ~context ~env ~uri ~is_path
    ast ~localization_tbl ~obj_context:[]
;;

let string_context_of_context =
  List.map (function None -> None | Some (Cic.Name n,_) -> Some n | Some
  (Cic.Anonymous,_) -> Some "_");;

let disambiguate_term ~context ~metasenv ~subst ~expty 
  ?(initial_ugraph = CicUniv.oblivion_ugraph)
  ~mk_implicit ~description_of_alias ~fix_instance ~mk_choice
  ~aliases ~universe ~lookup_in_library (text,prefix_len,term)
=
  let mk_localization_tbl x = Cic.CicHash.create x in
   MultiPassDisambiguator.disambiguate_thing ~context ~metasenv ~subst
    ~initial_ugraph ~aliases ~string_context_of_context
    ~universe ~lookup_in_library ~mk_implicit ~description_of_alias
    ~fix_instance
    ~uri:None ~pp_thing:CicNotationPp.pp_term
    ~domain_of_thing:Disambiguate.domain_of_term
    ~interpretate_thing:(interpretate_term (?create_dummy_ids:None) ~mk_choice)
    ~refine_thing:refine_term (text,prefix_len,term)
    ~mk_localization_tbl
    ~expty
    ~freshen_thing:CicNotationUtil.freshen_term
    ~passes:(MultiPassDisambiguator.passes ())

let disambiguate_obj ~mk_implicit ~description_of_alias ~fix_instance ~mk_choice
 ~aliases ~universe ~lookup_in_library ~uri (text,prefix_len,obj)
=
  let mk_localization_tbl x = Cic.CicHash.create x in
  MultiPassDisambiguator.disambiguate_thing ~context:[] ~metasenv:[] ~subst:[] 
    ~aliases ~universe ~uri ~string_context_of_context
    ~pp_thing:(CicNotationPp.pp_obj CicNotationPp.pp_term)
    ~domain_of_thing:Disambiguate.domain_of_obj
    ~lookup_in_library ~mk_implicit ~description_of_alias ~fix_instance
    ~initial_ugraph:CicUniv.empty_ugraph
    ~interpretate_thing:(interpretate_obj ~mk_choice)
    ~refine_thing:refine_obj
    ~mk_localization_tbl
    ~expty:None
    ~passes:(MultiPassDisambiguator.passes ())
    ~freshen_thing:CicNotationUtil.freshen_obj
    (text,prefix_len,obj)
