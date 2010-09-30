(* Copyright (C) 2005, HELM Team.
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

module Ast = CicNotationPt
module Obj = LibraryObjects

let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s) else ()

type interpretation_id = int

let idref id t = Ast.AttributedTerm (`IdRef id, t)

type term_info =
  { sort: (Cic.id, Ast.sort_kind) Hashtbl.t;
    uri: (Cic.id, UriManager.uri) Hashtbl.t;
  }

let get_types uri =
  let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
    match o with
      | Cic.InductiveDefinition (l,_,lpsno,_) -> l, lpsno 
      | _ -> assert false

let name_of_inductive_type uri i = 
  let types, _ = get_types uri in
  let (name, _, _, _) = try List.nth types i with Not_found -> assert false in
  name

  (* returns <name, type> pairs *)
let constructors_of_inductive_type uri i =
  let types, _ = get_types uri in
  let (_, _, _, constructors) = 
    try List.nth types i with Not_found -> assert false
  in
  constructors

  (* returns name only *)
let constructor_of_inductive_type uri i j =
  (try
    fst (List.nth (constructors_of_inductive_type uri i) (j-1))
  with Not_found -> assert false)

  (* returns the number of left parameters *)
let left_params_no_of_inductive_type uri =
   snd (get_types uri)

let destroy_nat annterm =
  let is_zero = function
    | Cic.AMutConstruct (_, uri, 0, 1, _) when Obj.is_nat_URI uri -> true
    | _ -> false
  in
  let is_succ = function
    | Cic.AMutConstruct (_, uri, 0, 2, _) when Obj.is_nat_URI uri -> true
    | _ -> false
  in
  let rec aux acc = function
    | Cic.AAppl (_, [he ; tl]) when is_succ he -> aux (acc + 1) tl
    | t when is_zero t -> Some acc
    | _ -> None in
  aux 0 annterm

let ast_of_acic0 ~output_type term_info acic k =
  let k = k term_info in
  let id_to_uris = term_info.uri in
  let register_uri id uri = Hashtbl.add id_to_uris id uri in
  let sort_of_id id =
    try
      Hashtbl.find term_info.sort id
    with Not_found ->
      prerr_endline (sprintf "warning: sort of id %s not found, using Type" id);
      `Type (CicUniv.fresh ())
  in
  let aux_substs substs =
    Some
      (List.map
        (fun (uri, annterm) -> (UriManager.name_of_uri uri, k annterm))
        substs)
  in
  let aux_context context =
    List.map
      (function
        | None -> None
        | Some annterm -> Some (k annterm))
      context
  in
  let aux = function
    | Cic.ARel (id,_,_,b) -> idref id (Ast.Ident (b, None))
    | Cic.AVar (id,uri,substs) ->
        register_uri id uri;
        idref id (Ast.Ident (UriManager.name_of_uri uri, aux_substs substs))
    | Cic.AMeta (id,n,l) -> idref id (Ast.Meta (n, aux_context l))
    | Cic.ASort (id,Cic.Prop) -> idref id (Ast.Sort `Prop)
    | Cic.ASort (id,Cic.Set) -> idref id (Ast.Sort `Set)
    | Cic.ASort (id,Cic.Type u) -> idref id (Ast.Sort (`Type u))
    | Cic.ASort (id,Cic.CProp u) -> idref id (Ast.Sort (`CProp u))
    | Cic.AImplicit (id, Some `Hole) -> idref id Ast.UserInput
    | Cic.AImplicit (id, _) -> idref id (Ast.Implicit `JustOne)
    | Cic.AProd (id,n,s,t) ->
        let binder_kind =
          match sort_of_id id with
          | `Set | `Type _ | `NType _ -> `Pi
          | `Prop | `CProp _ | `NCProp _ -> `Forall
        in
        idref id (Ast.Binder (binder_kind,
          (CicNotationUtil.name_of_cic_name n, Some (k s)), k t))
    | Cic.ACast (id,v,t) -> idref id (Ast.Cast (k v, k t))
    | Cic.ALambda (id,n,s,t) ->
        idref id (Ast.Binder (`Lambda,
          (CicNotationUtil.name_of_cic_name n, Some (k s)), k t))
    | Cic.ALetIn (id,n,s,ty,t) ->
        idref id (Ast.LetIn ((CicNotationUtil.name_of_cic_name n, Some (k ty)),
          k s, k t))
    | Cic.AAppl (aid,(Cic.AConst _ as he::tl as args))
    | Cic.AAppl (aid,(Cic.AMutInd _ as he::tl as args))
    | Cic.AAppl (aid,(Cic.AMutConstruct _ as he::tl as args)) as t ->
       (match destroy_nat t with
       | Some n -> idref aid (Ast.Num (string_of_int n, -1))
       | None ->
           let deannot_he = Deannotate.deannotate_term he in
           let coercion_info = CoercDb.is_a_coercion deannot_he in
           if coercion_info <> None && !Acic2content.hide_coercions then
             match coercion_info with
             | None -> assert false 
             | Some (_,_,_,sats,cpos) -> 
                 if cpos < List.length tl then
                   let _,rest = 
                     try HExtlib.split_nth (cpos+sats+1) tl with Failure _ -> [],[] 
                   in
                   if rest = [] then
                     idref aid (k (List.nth tl cpos))
                   else
                     idref aid (Ast.Appl (List.map k (List.nth tl cpos::rest)))
                 else
                   idref aid (Ast.Appl (List.map k args))
           else
             idref aid (Ast.Appl (List.map k args)))
    | Cic.AAppl (aid,args) ->
        idref aid (Ast.Appl (List.map k args))
    | Cic.AConst (id,uri,substs) ->
        register_uri id uri;
        idref id (Ast.Ident (UriManager.name_of_uri uri, aux_substs substs))
    | Cic.AMutInd (id,uri,i,substs) ->
        let name = name_of_inductive_type uri i in
        let uri_str = UriManager.string_of_uri uri in
        let puri_str = sprintf "%s#xpointer(1/%d)" uri_str (i+1) in
        register_uri id (UriManager.uri_of_string puri_str);
        idref id (Ast.Ident (name, aux_substs substs))
    | Cic.AMutConstruct (id,uri,i,j,substs) ->
        let name = constructor_of_inductive_type uri i j in
        let uri_str = UriManager.string_of_uri uri in
        let puri_str = sprintf "%s#xpointer(1/%d/%d)" uri_str (i + 1) j in
        register_uri id (UriManager.uri_of_string puri_str);
        idref id (Ast.Ident (name, aux_substs substs))
    | Cic.AMutCase (id,uri,typeno,ty,te,patterns) ->
        let name = name_of_inductive_type uri typeno in
        let uri_str = UriManager.string_of_uri uri in
        let puri_str = sprintf "%s#xpointer(1/%d)" uri_str (typeno+1) in
        let ctor_puri j =
          UriManager.uri_of_string
            (sprintf "%s#xpointer(1/%d/%d)" uri_str (typeno+1) j)
        in
        let case_indty = name, Some (UriManager.uri_of_string puri_str) in
        let constructors = constructors_of_inductive_type uri typeno in
        let lpsno = left_params_no_of_inductive_type uri in
	let rec eat_branch n ty pat =
          match (ty, pat) with
	  | Cic.Prod (_, _, t), _ when n > 0 -> eat_branch (pred n) t pat 
          | Cic.Prod (_, _, t), Cic.ALambda (_, name, s, t') ->
              let (cv, rhs) = eat_branch 0 t t' in
              (CicNotationUtil.name_of_cic_name name, Some (k s)) :: cv, rhs
          | _, _ -> [], k pat
        in
        let j = ref 0 in
        let patterns =
          try
            List.map2
              (fun (name, ty) pat ->
                incr j;
                let name,(capture_variables,rhs) =
                 match output_type with
                    `Term -> name, eat_branch lpsno ty pat
                  | `Pattern -> "_", ([], k pat)
                in
                 Ast.Pattern (name, Some (ctor_puri !j), capture_variables), rhs
              ) constructors patterns
          with Invalid_argument _ -> assert false
        in
        let indty =
         match output_type with
            `Pattern -> None
          | `Term -> Some case_indty
        in
        idref id (Ast.Case (k te, indty, Some (k ty), patterns))
    | Cic.AFix (id, no, funs) -> 
        let defs = 
          List.map
            (fun (_, n, decr_idx, ty, bo) ->
              let params,bo =
               let rec aux =
                function
                   Cic.ALambda (_,name,so,ta) ->
                    let params,rest = aux ta in
                     (CicNotationUtil.name_of_cic_name name,Some (k so))::
                      params, rest
                 | t -> [],t
               in
                aux bo
              in
              let ty =
               let rec eat_pis =
                function
                   0,ty -> ty
                 | n,Cic.AProd (_,_,_,ta) -> eat_pis (n - 1,ta)
                 | n,ty ->
                    (* I should do a whd here, but I have no context *)
                    assert false
               in
                eat_pis ((List.length params),ty)
              in
               (params,(Ast.Ident (n, None), Some (k ty)), k bo, decr_idx))
            funs
        in
        let name =
          try
            (match List.nth defs no with
            | _, (Ast.Ident (n, _), _), _, _ when n <> "_" -> n
            | _ -> assert false)
          with Not_found -> assert false
        in
         idref id (Ast.LetRec (`Inductive, defs, Ast.Ident (name, None)))
    | Cic.ACoFix (id, no, funs) -> 
        let defs = 
          List.map
            (fun (_, n, ty, bo) ->
              let params,bo =
               let rec aux =
                function
                   Cic.ALambda (_,name,so,ta) ->
                    let params,rest = aux ta in
                     (CicNotationUtil.name_of_cic_name name,Some (k so))::
                      params, rest
                 | t -> [],t
               in
                aux bo
              in
              let ty =
               let rec eat_pis =
                function
                   0,ty -> ty
                 | n,Cic.AProd (_,_,_,ta) -> eat_pis (n - 1,ta)
                 | n,ty ->
                    (* I should do a whd here, but I have no context *)
                    assert false
               in
                eat_pis ((List.length params),ty)
              in
               (params,(Ast.Ident (n, None), Some (k ty)), k bo, 0))
            funs
        in
        let name =
          try
            (match List.nth defs no with
            | _, (Ast.Ident (n, _), _), _, _ when n <> "_" -> n
            | _ -> assert false)
          with Not_found -> assert false
        in
        idref id (Ast.LetRec (`CoInductive, defs, Ast.Ident (name, None)))
  in
  aux acic

  (* persistent state *)

let initial_level2_patterns32 () = Hashtbl.create 211
let initial_interpretations () = Hashtbl.create 211

let level2_patterns32 = ref (initial_level2_patterns32 ())
(* symb -> id list ref *)
let interpretations = ref (initial_interpretations ())
let compiled32 = ref None
let pattern32_matrix = ref []
let counter = ref ~-1 
let find_level2_patterns32 pid = Hashtbl.find !level2_patterns32 pid;;

let stack = ref []

let push () =
 stack := (!counter,!level2_patterns32,!interpretations,!compiled32,!pattern32_matrix)::!stack;
 counter := ~-1;
 level2_patterns32 := initial_level2_patterns32 ();
 interpretations := initial_interpretations ();
 compiled32 := None;
 pattern32_matrix := []
;;

let pop () =
 match !stack with
    [] -> assert false
  | (ocounter,olevel2_patterns32,ointerpretations,ocompiled32,opattern32_matrix)::old ->
   stack := old;
   counter := ocounter;
   level2_patterns32 := olevel2_patterns32;
   interpretations := ointerpretations;
   compiled32 := ocompiled32;
   pattern32_matrix := opattern32_matrix
;;

let get_compiled32 () =
  match !compiled32 with
  | None -> assert false
  | Some f -> Lazy.force f

let set_compiled32 f = compiled32 := Some f

let add_idrefs =
  List.fold_right (fun idref t -> Ast.AttributedTerm (`IdRef idref, t))

let instantiate32 term_info idrefs env symbol args =
  let rec instantiate_arg = function
    | Ast.IdentArg (n, name) ->
        let t = 
          try List.assoc name env 
          with Not_found -> prerr_endline ("name not found in env: "^name);
                            assert false
        in
        let rec count_lambda = function
          | Ast.AttributedTerm (_, t) -> count_lambda t
          | Ast.Binder (`Lambda, _, body) -> 1 + count_lambda body
          | _ -> 0
        in
        let rec add_lambda t n =
          if n > 0 then
            let name = CicNotationUtil.fresh_name () in
            Ast.Binder (`Lambda, (Ast.Ident (name, None), None),
              Ast.Appl [add_lambda t (n - 1); Ast.Ident (name, None)])
          else
            t
        in
        add_lambda t (n - count_lambda t)
  in
  let head =
    let symbol = Ast.Symbol (symbol, 0) in
    add_idrefs idrefs symbol
  in
  if args = [] then head
  else Ast.Appl (head :: List.map instantiate_arg args)

let rec ast_of_acic1 ~output_type term_info annterm = 
  let id_to_uris = term_info.uri in
  let register_uri id uri = Hashtbl.add id_to_uris id uri in
  match (get_compiled32 ()) annterm with
  | None ->
     ast_of_acic0 ~output_type term_info annterm (ast_of_acic1 ~output_type)
  | Some (env, ctors, pid) -> 
      let idrefs =
        List.map
          (fun annterm ->
            let idref = CicUtil.id_of_annterm annterm in
            (try
              register_uri idref
                (CicUtil.uri_of_term (Deannotate.deannotate_term annterm))
            with Invalid_argument _ -> ());
            idref)
          ctors
      in
      let env' =
       List.map
        (fun (name, term) -> name, ast_of_acic1 ~output_type term_info term) env
      in
      let _, symbol, args, _ =
        try
          find_level2_patterns32 pid
        with Not_found -> assert false
      in
      let ast = instantiate32 term_info idrefs env' symbol args in
      Ast.AttributedTerm (`IdRef (CicUtil.id_of_annterm annterm), ast)

let load_patterns32s =
 let load_patterns32 t =
  let t =
    HExtlib.filter_map (function (true, ap, id) -> Some (ap, id) | _ -> None) t
  in
   set_compiled32 (lazy (Acic2astMatcher.Matcher32.compiler t))
 in
  ref [load_patterns32]
;;

let add_load_patterns32 f = load_patterns32s := f :: !load_patterns32s;;

let ast_of_acic ~output_type id_to_sort annterm =
  debug_print (lazy ("ast_of_acic <- "
    ^ CicPp.ppterm (Deannotate.deannotate_term annterm)));
  let term_info = { sort = id_to_sort; uri = Hashtbl.create 211 } in
  let ast = ast_of_acic1 ~output_type term_info annterm in
  debug_print (lazy ("ast_of_acic -> " ^ CicNotationPp.pp_term ast));
  ast, term_info.uri

let fresh_id =
  fun () ->
    incr counter;
    !counter

let add_interpretation dsc (symbol, args) appl_pattern =
  let id = fresh_id () in
  Hashtbl.add !level2_patterns32 id (dsc, symbol, args, appl_pattern);
  pattern32_matrix := (true, appl_pattern, id) :: !pattern32_matrix;
  List.iter (fun f -> f !pattern32_matrix) !load_patterns32s;
  (try
    let ids = Hashtbl.find !interpretations symbol in
    ids := id :: !ids
  with Not_found -> Hashtbl.add !interpretations symbol (ref [id]));
  id

let get_all_interpretations () =
  List.map
    (function (_, _, id) ->
      let (dsc, _, _, _) =
        try
          Hashtbl.find !level2_patterns32 id
        with Not_found -> assert false
      in
      (id, dsc))
    !pattern32_matrix

let get_active_interpretations () =
  HExtlib.filter_map (function (true, _, id) -> Some id | _ -> None)
    !pattern32_matrix

let set_active_interpretations ids =
  let pattern32_matrix' =
    List.map
      (function 
        | (_, ap, id) when List.mem id ids -> (true, ap, id)
        | (_, ap, id) -> (false, ap, id))
      !pattern32_matrix
  in
  pattern32_matrix := pattern32_matrix';
  List.iter (fun f -> f !pattern32_matrix) !load_patterns32s

exception Interpretation_not_found

let lookup_interpretations ?(sorted=true) symbol =
  try
    let raw = 
      List.map (
        fun id ->
          let (dsc, _, args, appl_pattern) =
            try
              Hashtbl.find !level2_patterns32 id
            with Not_found -> assert false 
          in
          dsc, args, appl_pattern
      )
      !(Hashtbl.find !interpretations symbol)
    in
    if sorted then HExtlib.list_uniq (List.sort Pervasives.compare raw)
              else raw
  with Not_found -> raise Interpretation_not_found

let remove_interpretation id =
  (try
    let dsc, symbol, _, _ = Hashtbl.find !level2_patterns32 id in
    let ids = Hashtbl.find !interpretations symbol in
    ids := List.filter ((<>) id) !ids;
    Hashtbl.remove !level2_patterns32 id;
  with Not_found -> raise Interpretation_not_found);
  pattern32_matrix :=
    List.filter (fun (_, _, id') -> id <> id') !pattern32_matrix;
  List.iter (fun f -> f !pattern32_matrix) !load_patterns32s

let init () = List.iter (fun f -> f []) !load_patterns32s

let instantiate_appl_pattern 
  ~mk_appl ~mk_implicit ~term_of_uri ~term_of_nref env appl_pattern 
=
  let lookup name =
    try List.assoc name env
    with Not_found ->
      prerr_endline (sprintf "Name %s not found" name);
      assert false
  in
  let rec aux = function
    | Ast.UriPattern uri -> term_of_uri uri
    | Ast.NRefPattern nref -> term_of_nref nref
    | Ast.ImplicitPattern -> mk_implicit false
    | Ast.VarPattern name -> lookup name
    | Ast.ApplPattern terms -> mk_appl (List.map aux terms)
  in
  aux appl_pattern

