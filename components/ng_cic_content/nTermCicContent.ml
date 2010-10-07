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

(* $Id: termAcicContent.ml 9304 2008-12-05 23:12:39Z sacerdot $ *)

open Printf

module Ast = CicNotationPt

let debug = false
let debug_print s = if debug then prerr_endline (Lazy.force s) else ()

type id = string

let hide_coercions = ref true;;

(*
type interpretation_id = int

type term_info =
  { sort: (Cic.id, Ast.sort_kind) Hashtbl.t;
    uri: (Cic.id, UriManager.uri) Hashtbl.t;
  }

let get_types uri =
  let o,_ = CicEnvironment.get_obj CicUniv.oblivion_ugraph uri in
    match o with
      | Cic.InductiveDefinition (l,_,leftno,_) -> l, leftno 
      | _ -> assert false
*)

let idref register_ref =
 let id = ref 0 in
  fun ?reference t ->
   incr id;
   let id = "i" ^ string_of_int !id in
    (match reference with None -> () | Some r -> register_ref id r);
    Ast.AttributedTerm (`IdRef id, t)
;;

let level_of_uri u = 
  let name = NUri.name_of_uri u in
  assert(String.length name > String.length "Type");
  String.sub name 4 (String.length name - 4)
;;

let destroy_nat =
  let is_nat_URI = NUri.eq (NUri.uri_of_string
  "cic:/matita/ng/arithmetics/nat/nat.ind") in
  let is_zero = function
    | NCic.Const (NReference.Ref (uri, NReference.Con (0, 1, 0))) when
       is_nat_URI uri -> true
    | _ -> false
  in
  let is_succ = function
    | NCic.Const (NReference.Ref (uri, NReference.Con (0, 2, 0))) when
       is_nat_URI uri -> true
    | _ -> false
  in
  let rec aux acc = function
    | NCic.Appl [he ; tl] when is_succ he -> aux (acc + 1) tl
    | t when is_zero t -> Some acc
    | _ -> None
  in
   aux 0

(* CODICE c&p da NCicPp *)
let nast_of_cic0 status
 ~(idref:
    ?reference:NReference.reference -> CicNotationPt.term -> CicNotationPt.term)
 ~output_type ~metasenv ~subst k ~context =
  function
    | NCic.Rel n ->
       (try 
         let name,_ = List.nth context (n-1) in
         let name = if name = "_" then "__"^string_of_int n else name in
          idref (Ast.Ident (name,None))
        with Failure "nth" | Invalid_argument "List.nth" -> 
         idref (Ast.Ident ("-" ^ string_of_int (n - List.length context),None)))
    | NCic.Const r -> idref ~reference:r (Ast.Ident (NCicPp.r2s true r, None))
    | NCic.Meta (n,lc) when List.mem_assoc n subst -> 
        let _,_,t,_ = List.assoc n subst in
         k ~context (NCicSubstitution.subst_meta lc t)
    | NCic.Meta (n,(s,l)) ->
       (* CSC: qua non dovremmo espandere *)
       let l = NCicUtils.expand_local_context l in
        idref (Ast.Meta
         (n, List.map (fun x -> Some (k ~context (NCicSubstitution.lift s x))) l))
    | NCic.Sort NCic.Prop -> idref (Ast.Sort `Prop)
    | NCic.Sort NCic.Type [] -> idref (Ast.Sort `Set)
    | NCic.Sort NCic.Type ((`Type,u)::_) -> 
              idref(Ast.Sort (`NType (level_of_uri u)))
    | NCic.Sort NCic.Type ((`CProp,u)::_) -> 
              idref(Ast.Sort (`NCProp (level_of_uri u)))
    | NCic.Sort NCic.Type ((`Succ,u)::_) -> 
              idref(Ast.Sort (`NType (level_of_uri u ^ "+1")))
    | NCic.Implicit `Hole -> idref (Ast.UserInput)
    | NCic.Implicit `Vector -> idref (Ast.Implicit `Vector)
    | NCic.Implicit _ -> idref (Ast.Implicit `JustOne)
    | NCic.Prod (n,s,t) ->
        let n = if n.[0] = '_' then "_" else n in
        let binder_kind = `Forall in
         idref (Ast.Binder (binder_kind, (Ast.Ident (n,None), Some (k ~context s)),
          k ~context:((n,NCic.Decl s)::context) t))
    | NCic.Lambda (n,s,t) ->
        idref (Ast.Binder (`Lambda,(Ast.Ident (n,None), Some (k ~context s)),
         k ~context:((n,NCic.Decl s)::context) t))
    | NCic.LetIn (n,s,ty,NCic.Rel 1) ->
        idref (Ast.Cast (k ~context ty, k ~context s))
    | NCic.LetIn (n,s,ty,t) ->
        idref (Ast.LetIn ((Ast.Ident (n,None), Some (k ~context s)), k ~context
          ty, k ~context:((n,NCic.Decl s)::context) t))
    | NCic.Appl (NCic.Meta (n,lc) :: args) when List.mem_assoc n subst -> 
       let _,_,t,_ = List.assoc n subst in
       let hd = NCicSubstitution.subst_meta lc t in
        k ~context
         (NCicReduction.head_beta_reduce ~upto:(List.length args)
           (match hd with
           | NCic.Appl l -> NCic.Appl (l@args)
           | _ -> NCic.Appl (hd :: args)))
    | NCic.Appl args as t ->
       (match destroy_nat t with
         | Some n -> idref (Ast.Num (string_of_int n, -1))
         | None ->
            let args =
             if not !hide_coercions then args
             else
              match
               NCicCoercion.match_coercion status ~metasenv ~context ~subst t
              with
               | None -> args
               | Some (_,sats,cpos) -> 
(* CSC: sats e' il numero di pi, ma non so cosa farmene! voglio il numero di
   argomenti da saltare, come prima! *)
                  if cpos < List.length args - 1 then
                   List.nth args (cpos + 1) ::
                    try snd (HExtlib.split_nth (cpos+sats+2) args)
                    with Failure _->[]
                  else
                   args
            in
             (match args with
                 [arg] -> idref (k ~context arg)
               | _ -> idref (Ast.Appl (List.map (k ~context) args))))
    | NCic.Match (NReference.Ref (uri,_) as r,outty,te,patterns) ->
        let name = NUri.name_of_uri uri in
(* CSC
        let uri_str = UriManager.string_of_uri uri in
        let puri_str = sprintf "%s#xpointer(1/%d)" uri_str (typeno+1) in
        let ctor_puri j =
          UriManager.uri_of_string
            (sprintf "%s#xpointer(1/%d/%d)" uri_str (typeno+1) j)
        in
*)
        let case_indty =
         name, None(*CSC Some (UriManager.uri_of_string puri_str)*) in
        let constructors, leftno =
         let _,leftno,tys,_,n = NCicEnvironment.get_checked_indtys r in
         let _,_,_,cl  = List.nth tys n in
          cl,leftno
        in
	let rec eat_branch n ctx ty pat =
          match (ty, pat) with
	  | NCic.Prod (name, s, t), _ when n > 0 ->
             eat_branch (pred n) ctx t pat 
          | NCic.Prod (_, _, t), NCic.Lambda (name, s, t') ->
              let cv, rhs = eat_branch 0 ((name,NCic.Decl s)::ctx) t t' in
              (Ast.Ident (name,None), Some (k ~context:ctx s)) :: cv, rhs
          | _, _ -> [], k ~context:ctx pat
        in
        let j = ref 0 in
        let patterns =
          try
            List.map2
              (fun (_, name, ty) pat ->
                incr j;
                let name,(capture_variables,rhs) =
                 match output_type with
                    `Term -> name, eat_branch leftno context ty pat
                  | `Pattern -> "_", ([], k ~context pat)
                in
                 Ast.Pattern (name, None(*CSC Some (ctor_puri !j)*), capture_variables), rhs
              ) constructors patterns
          with Invalid_argument _ -> assert false
        in
        let indty =
         match output_type with
            `Pattern -> None
          | `Term -> Some case_indty
        in
         idref (Ast.Case (k ~context te, indty, Some (k ~context outty), patterns))
;;

  (* persistent state *)

(*
let initial_level2_patterns32 () = Hashtbl.create 211
let initial_interpretations () = Hashtbl.create 211

let level2_patterns32 = ref (initial_level2_patterns32 ())
(* symb -> id list ref *)
let interpretations = ref (initial_interpretations ())
*)
let compiled32 = ref None
(*
let pattern32_matrix = ref []
let counter = ref ~-1 

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
*)

let get_compiled32 () =
  match !compiled32 with
  | None -> assert false
  | Some f -> Lazy.force f

let set_compiled32 f = compiled32 := Some f

let add_idrefs =
  List.fold_right (fun idref t -> Ast.AttributedTerm (`IdRef idref, t))

let instantiate32 idrefs env symbol args =
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

let rec nast_of_cic1 status ~idref ~output_type ~metasenv ~subst ~context term =
  match (get_compiled32 ()) term with
  | None ->
     nast_of_cic0 status ~idref ~output_type ~metasenv ~subst
      (nast_of_cic1 status ~idref ~output_type ~metasenv ~subst) ~context term 
  | Some (env, ctors, pid) -> 
      let idrefs =
       List.map
        (fun term ->
          let attrterm =
           idref
            ~reference:
              (match term with NCic.Const nref -> nref | _ -> assert false)
           (CicNotationPt.Ident ("dummy",None))
          in
           match attrterm with
              Ast.AttributedTerm (`IdRef id, _) -> id
            | _ -> assert false
        ) ctors
      in
      let env =
       List.map
        (fun (name, term) ->
          name,
           nast_of_cic1 status ~idref ~output_type ~subst ~metasenv ~context
            term
        ) env
      in
      let _, symbol, args, _ =
        try
          TermAcicContent.find_level2_patterns32 pid
        with Not_found -> assert false
      in
      let ast = instantiate32 idrefs env symbol args in
      idref ast (*Ast.AttributedTerm (`IdRef (idref term), ast)*)
;;

let load_patterns32 t =
 let t =
  HExtlib.filter_map (function (true, ap, id) -> Some (ap, id) | _ -> None) t
 in
  set_compiled32 (lazy (Ncic2astMatcher.Matcher32.compiler t))
in
 TermAcicContent.add_load_patterns32 load_patterns32;
 TermAcicContent.init ()
;;

(*
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
  load_patterns32 !pattern32_matrix;
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
  load_patterns32 !pattern32_matrix

exception Interpretation_not_found

let lookup_interpretations symbol =
  try
   HExtlib.list_uniq
    (List.sort Pervasives.compare
     (List.map
      (fun id ->
        let (dsc, _, args, appl_pattern) =
          try
            Hashtbl.find !level2_patterns32 id
          with Not_found -> assert false 
        in
        dsc, args, appl_pattern)
      !(Hashtbl.find !interpretations symbol)))
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
  load_patterns32 !pattern32_matrix

let _ = load_patterns32 []

let instantiate_appl_pattern 
  ~mk_appl ~mk_implicit ~term_of_uri env appl_pattern 
=
  let lookup name =
    try List.assoc name env
    with Not_found ->
      prerr_endline (sprintf "Name %s not found" name);
      assert false
  in
  let rec aux = function
    | Ast.UriPattern uri -> term_of_uri uri
    | Ast.ImplicitPattern -> mk_implicit false
    | Ast.VarPattern name -> lookup name
    | Ast.ApplPattern terms -> mk_appl (List.map aux terms)
  in
  aux appl_pattern
*)

let nmap_sequent0 status ~idref ~metasenv ~subst (i,(n,context,ty)) =
 let module K = Content in
 let nast_of_cic =
  nast_of_cic1 status ~idref ~output_type:`Term ~metasenv ~subst in
 let context',_ =
  List.fold_right
   (fun item (res,context) ->
     match item with
      | name,NCic.Decl t ->
         Some
          (* We should call build_decl_item, but we have not computed *)
          (* the inner-types ==> we always produce a declaration      *)
          (`Declaration
            { K.dec_name = (Some name);
              K.dec_id = "-1"; 
              K.dec_inductive = false;
              K.dec_aref = "-1";
              K.dec_type = nast_of_cic ~context t
            })::res,item::context
      | name,NCic.Def (t,ty) ->
         Some
          (* We should call build_def_item, but we have not computed *)
          (* the inner-types ==> we always produce a declaration     *)
          (`Definition
             { K.def_name = (Some name);
               K.def_id = "-1"; 
               K.def_aref = "-1";
               K.def_term = nast_of_cic ~context t;
               K.def_type = nast_of_cic ~context ty
             })::res,item::context
   ) context ([],[])
 in
  ("-1",i,context',nast_of_cic ~context ty)
;;

let nmap_sequent status ~metasenv ~subst conjecture =
 let module K = Content in
 let ids_to_refs = Hashtbl.create 211 in
 let register_ref = Hashtbl.add ids_to_refs in
  nmap_sequent0 status ~idref:(idref register_ref) ~metasenv ~subst conjecture,
  ids_to_refs
;;

let object_prefix = "obj:";;
let declaration_prefix = "decl:";;
let definition_prefix = "def:";;
let inductive_prefix = "ind:";;
let joint_prefix = "joint:";;

let get_id =
 function
    Ast.AttributedTerm (`IdRef id, _) -> id
  | _ -> assert false
;;

let gen_id prefix seed =
 let res = prefix ^ string_of_int !seed in
  incr seed ;
  res
;;

let build_def_item seed context metasenv id n t ty =
 let module K = Content in
(*
  try
   let sort = Hashtbl.find ids_to_inner_sorts id in
   if sort = `Prop then
       (let p = 
        (acic2content seed context metasenv ?name:(name_of n) ~ids_to_inner_sorts  ~ids_to_inner_types t)
       in 
        `Proof p;)
   else 
*)
      `Definition
        { K.def_name = Some n;
          K.def_id = gen_id definition_prefix seed; 
          K.def_aref = id;
          K.def_term = t;
          K.def_type = ty
        }
(*
  with
   Not_found -> assert false
*)

let build_decl_item seed id n s =
 let module K = Content in
(*
 let sort =
   try
    Some (Hashtbl.find ids_to_inner_sorts (Cic2acic.source_id_of_id id))
   with Not_found -> None
 in
 match sort with
 | Some `Prop ->
    `Hypothesis
      { K.dec_name = name_of n;
        K.dec_id = gen_id declaration_prefix seed; 
        K.dec_inductive = false;
        K.dec_aref = id;
        K.dec_type = s
      }
 | _ ->
*)
    `Declaration
      { K.dec_name = Some n;
        K.dec_id = gen_id declaration_prefix seed; 
        K.dec_inductive = false;
        K.dec_aref = id;
        K.dec_type = s
      }
;;

let nmap_obj status (uri,_,metasenv,subst,kind) =
  let module K = Content in
  let ids_to_refs = Hashtbl.create 211 in
  let register_ref = Hashtbl.add ids_to_refs in
  let idref = idref register_ref in
  let nast_of_cic =
   nast_of_cic1 status ~idref ~output_type:`Term ~metasenv ~subst in
  let seed = ref 0 in
  let conjectures =
   match metasenv with
      [] -> None
    | _ -> (*Some (List.map (map_conjectures seed) metasenv)*)
      (*CSC: used to be the previous line, that uses seed *)
      Some (List.map (nmap_sequent0 status ~idref ~metasenv ~subst) metasenv)
  in
let  build_constructors seed l =
      List.map 
       (fun (_,n,ty) ->
           let ty = nast_of_cic ~context:[] ty in
           { K.dec_name = Some n;
             K.dec_id = gen_id declaration_prefix seed;
             K.dec_inductive = false;
             K.dec_aref = "";
             K.dec_type = ty
           }) l
in
let build_inductive b seed = 
      fun (_,n,ty,cl) ->
        let ty = nast_of_cic ~context:[] ty in
        `Inductive
          { K.inductive_id = gen_id inductive_prefix seed;
            K.inductive_name = n;
            K.inductive_kind = b;
            K.inductive_type = ty;
            K.inductive_constructors = build_constructors seed cl
           }
in
let build_fixpoint b seed = 
      fun (_,n,_,ty,t) ->
        let t = nast_of_cic ~context:[] t in
        let ty = nast_of_cic ~context:[] ty in
        `Definition
          { K.def_id = gen_id inductive_prefix seed;
            K.def_name = Some n;
            K.def_aref = "";
            K.def_type = ty;
            K.def_term = t;
           }
in
  let res =
   match kind with
    | NCic.Fixpoint (is_rec, ifl, _) -> 
         (gen_id object_prefix seed, [], conjectures,
            `Joint
              { K.joint_id = gen_id joint_prefix seed;
                K.joint_kind = 
                   if is_rec then 
                        `Recursive (List.map (fun (_,_,i,_,_) -> i) ifl)
                   else `CoRecursive;
                K.joint_defs = List.map (build_fixpoint is_rec seed) ifl
              }) 
    | NCic.Inductive (is_ind, lno, itl, _) ->
         (gen_id object_prefix seed, [], conjectures,
            `Joint
              { K.joint_id = gen_id joint_prefix seed;
                K.joint_kind = 
                   if is_ind then `Inductive lno else `CoInductive lno;
                K.joint_defs = List.map (build_inductive is_ind seed) itl
              }) 
    | NCic.Constant (_,_,Some bo,ty,_) ->
       let ty = nast_of_cic ~context:[] ty in
       let bo = nast_of_cic ~context:[] bo in
        (gen_id object_prefix seed, [], conjectures,
          `Def (K.Const,ty,
            build_def_item seed [] [] (get_id bo) (NUri.name_of_uri uri) bo ty))
    | NCic.Constant (_,_,None,ty,_) ->
       let ty = nast_of_cic ~context:[] ty in
         (gen_id object_prefix seed, [], conjectures,
           `Decl (K.Const,
             (*CSC: ??? get_id ty here used to be the id of the axiom! *)
             build_decl_item seed (get_id ty) (NUri.name_of_uri uri) ty))
 in
  res,ids_to_refs
;;
