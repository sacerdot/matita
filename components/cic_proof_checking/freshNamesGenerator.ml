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
 * http://cs.unibo.it/helm/.
 *)

(* $Id$ *)

let debug_print = fun _ -> ()

let rec higher_name arity =
  function 
      Cic.Sort Cic.Prop
    | Cic.Sort (Cic.CProp _) -> 
	if arity = 0 then "A" (* propositions *)
	else if arity = 1 then "P" (* predicates *)
	else "R" (*relations *)
    | Cic.Sort Cic.Set
	-> if arity = 0 then "S" else "F"
    | Cic.Sort (Cic.Type _ ) -> 
	if arity = 0 then "T" else "F"
    | Cic.Prod (_,_,t) -> higher_name (arity+1) t
    | _ -> "f"

let get_initial s = 
   if String.length s = 0 then "_"
   else 
     let head = String.sub s 0 1 in
     String.lowercase head

(* only used when the sort is not Prop or CProp *)
let rec guess_a_name context ty =
  match ty with
    Cic.Rel n ->  
      (match List.nth context (n-1) with
	None -> assert false
      | Some (Cic.Anonymous,_) -> "eccomi_qua"
      | Some (Cic.Name s,_) -> get_initial s)
  | Cic.Var (uri,_) -> get_initial (UriManager.name_of_uri uri)
  | Cic.Sort _ -> higher_name 0 ty
  | Cic.Implicit _ -> assert false
  | Cic.Cast (t1,t2) -> guess_a_name context t1
  | Cic.Prod (na_,_,t) -> higher_name 1 t
(* warning: on appl we should beta reduce before the recursive call
  | Cic.Lambda _ -> assert false   
*)
  | Cic.LetIn (_,s,_,t) -> guess_a_name context (CicSubstitution.subst ~avoid_beta_redexes:true s t)
  | Cic.Appl [] -> assert false
  | Cic.Appl (he::_) -> guess_a_name context he 
  | Cic.Const (uri,_)
  | Cic.MutInd (uri,_,_)
  | Cic.MutConstruct (uri,_,_,_) -> get_initial (UriManager.name_of_uri uri)  
  | _ -> "x"

(* mk_fresh_name context name typ                      *)
(* returns an identifier which is fresh in the context *)
(* and that resembles [name] as much as possible.      *)
(* [typ] will be the type of the variable              *)
let mk_fresh_name ~subst metasenv context name ~typ =
 let module C = Cic in
  let basename =
   match name with
      C.Anonymous ->
       (try
        let ty,_ = 
          CicTypeChecker.type_of_aux' ~subst metasenv context typ 
            CicUniv.oblivion_ugraph 
        in 
         (match ty with
             C.Sort C.Prop
           | C.Sort (C.CProp _) -> "H"
           | _ -> guess_a_name context typ
         )
        with CicTypeChecker.TypeCheckerFailure _ -> "H"
       )
    | C.Name name ->
       Str.global_replace (Str.regexp "[0-9']*$") "" name
  in
   let already_used name =
    List.exists (function Some (n,_) -> n=name | _ -> false) context
   in
    if name <> C.Anonymous && not (already_used name) then
     name
    else if not (already_used (C.Name basename)) then
     C.Name basename
    else
     let rec try_next n =
      let name' = C.Name (basename ^ string_of_int n) in
       if already_used name' then
        try_next (n+1)
       else
        name'
     in
      try_next 1
;;

(* let mk_fresh_names ~subst metasenv context t *)
let rec mk_fresh_names ~subst metasenv context t =
  match t with
    Cic.Rel _ -> t
  | Cic.Var (uri,exp_named_subst) ->
      let ens = 
	List.map 
	  (fun (uri,t) ->
	    (uri,mk_fresh_names ~subst metasenv context t)) exp_named_subst in
      Cic.Var (uri,ens)
  | Cic.Meta (i,l) ->
       let l' = 
        List.map 
         (fun t ->
           match t with
             None -> None
           | Some t -> Some (mk_fresh_names ~subst metasenv context t)) l in
       Cic.Meta(i,l')
    | Cic.Sort _ 
    | Cic.Implicit _ -> t
    | Cic.Cast (te,ty) ->
       let te' = mk_fresh_names ~subst metasenv context te in
       let ty' = mk_fresh_names ~subst metasenv context ty in
       Cic.Cast (te', ty')
    | Cic.Prod (n,s,t) ->
	let s' = mk_fresh_names ~subst metasenv context s in
	let n' =
	  match n with
	    Cic.Anonymous -> Cic.Anonymous
	  | Cic.Name "matita_dummy" -> 
	      mk_fresh_name ~subst metasenv context Cic.Anonymous ~typ:s'
	  | _ -> n in 
	let t' = mk_fresh_names ~subst metasenv (Some(n',Cic.Decl s')::context) t in
	Cic.Prod (n',s',t')
    | Cic.Lambda (n,s,t) ->
	let s' = mk_fresh_names ~subst metasenv context s in
	let n' =
	  match n with
	    Cic.Anonymous -> Cic.Anonymous
	  | Cic.Name "matita_dummy" -> 
	      mk_fresh_name ~subst metasenv context Cic.Anonymous ~typ:s' 
	  | _ -> n in 
	let t' = mk_fresh_names ~subst metasenv (Some(n',Cic.Decl s')::context) t in
	Cic.Lambda (n',s',t')
    | Cic.LetIn (n,s,ty,t) ->
	let s' = mk_fresh_names ~subst metasenv context s in
        let ty' = mk_fresh_names ~subst metasenv context ty in
	let n' =
	  match n with
	    Cic.Anonymous -> Cic.Anonymous
	  | Cic.Name "matita_dummy" -> 
	      mk_fresh_name ~subst metasenv context Cic.Anonymous ~typ:s' 
	  | _ -> n in 
	let t' = mk_fresh_names ~subst metasenv (Some(n',Cic.Def (s',ty'))::context) t in
	Cic.LetIn (n',s',ty',t')	
    | Cic.Appl l ->
	Cic.Appl (List.map (mk_fresh_names ~subst metasenv context) l)
    | Cic.Const (uri,exp_named_subst) ->
        let ens = 
	  List.map 
	    (fun (uri,t) ->
	      (uri,mk_fresh_names ~subst metasenv context t)) exp_named_subst in
	Cic.Const(uri,ens)
    | Cic.MutInd (uri,tyno,exp_named_subst) ->
	let ens = 
	  List.map 
	    (fun (uri,t) ->
	      (uri,mk_fresh_names ~subst metasenv context t)) exp_named_subst in
        Cic.MutInd (uri,tyno,ens)
    | Cic.MutConstruct (uri,tyno,consno,exp_named_subst) ->
        let ens = 
	  List.map 
	    (fun (uri,t) ->
	      (uri,mk_fresh_names ~subst metasenv context t)) exp_named_subst in
        Cic.MutConstruct (uri,tyno,consno, ens)
    | Cic.MutCase (sp,i,outty,t,pl) ->
       let outty' = mk_fresh_names ~subst metasenv context outty in
       let t' = mk_fresh_names ~subst metasenv context t in
       let pl' = List.map (mk_fresh_names ~subst metasenv context) pl in
       Cic.MutCase (sp, i, outty', t', pl')
    | Cic.Fix (i, fl) -> 
        let tys,_ =
          List.fold_left
            (fun (types,len) (n,_,ty,_) ->
               (Some (Cic.Name n,(Cic.Decl (CicSubstitution.lift len ty)))::types,
                len+1)
	    ) ([],0) fl
        in
	let fl' = List.map 
	    (fun (n,i,ty,bo) -> 
	      let ty' = mk_fresh_names ~subst metasenv context ty in
	      let bo' = mk_fresh_names ~subst metasenv (tys@context) bo in
	      (n,i,ty',bo')) fl in
	Cic.Fix (i, fl') 
    | Cic.CoFix (i, fl) ->
        let tys,_ =
          List.fold_left
            (fun (types,len) (n,ty,_) ->
               (Some (Cic.Name n,(Cic.Decl (CicSubstitution.lift len ty)))::types,
                len+1)
	    ) ([],0) fl
        in
	let fl' = List.map 
	    (fun (n,ty,bo) -> 
	      let ty' = mk_fresh_names ~subst metasenv context ty in
	      let bo' = mk_fresh_names ~subst metasenv (tys@context) bo in
	      (n,ty',bo')) fl in
	Cic.CoFix (i, fl') 	
;;

(* clean_dummy_dependent_types term                             *)
(* returns a copy of [term] where every dummy dependent product *)
(* have been replaced with a non-dependent product and where    *)
(* dummy let-ins have been removed.                             *)
let clean_dummy_dependent_types t =
 let module C = Cic in
  let rec aux k =
   function
      C.Rel m as t -> t,[k - m]
    | C.Var (uri,exp_named_subst) ->
       let exp_named_subst',rels = 
        List.fold_right
         (fun (uri,t) (exp_named_subst,rels) ->
           let t',rels' = aux k t in
            (uri,t')::exp_named_subst, rels' @ rels
         ) exp_named_subst ([],[])
       in
        C.Var (uri,exp_named_subst'),rels
    | C.Meta (i,l) ->
       let l',rels =
        List.fold_right
         (fun t (l,rels) ->
           let t',rels' =
            match t with
               None -> None,[]
             | Some t ->
                let t',rels' = aux k t in
                 Some t', rels'
           in
            t'::l, rels' @ rels
         ) l ([],[])
       in
        C.Meta(i,l'),rels
    | C.Sort _ as t -> t,[]
    | C.Implicit _ as t -> t,[]
    | C.Cast (te,ty) ->
       let te',rels1 = aux k te in
       let ty',rels2 = aux k ty in
        C.Cast (te', ty'), rels1@rels2
    | C.Prod (n,s,t) ->
       let s',rels1 = aux k s in
       let t',rels2 = aux (k+1) t in
        let n' =
         match n with
            C.Anonymous ->
             if List.mem k rels2 then
(
              debug_print (lazy "If this happens often, we can do something about it (i.e. we can generate a new fresh name; problem: we need the metasenv and context ;-(. Alternative solution: mk_implicit does not generate entries for the elements in the context that have no name") ;
              C.Anonymous
)
             else
              C.Anonymous
          | C.Name _ as n ->
             if List.mem k rels2 then n else C.Anonymous
        in
         C.Prod (n', s', t'), rels1@rels2
    | C.Lambda (n,s,t) ->
       let s',rels1 = aux k s in
       let t',rels2 = aux (k+1) t in
        C.Lambda (n, s', t'), rels1@rels2
    | C.LetIn (n,s,ty,t) ->
       let s',rels1 = aux k s in
       let ty',rels2 = aux k ty in
       let t',rels3 = aux (k+1) t in
       let rels = rels1 @ rels2 @ rels3 in
        if List.mem k rels3 then
         C.LetIn (n, s', ty', t'), rels
        else
         (* (C.Rel 1) is just a dummy term; any term would fit *)
         CicSubstitution.subst (C.Rel 1) t', rels
    | C.Appl l ->
       let l',rels =
        List.fold_right
         (fun t (exp_named_subst,rels) ->
           let t',rels' = aux k t in
            t'::exp_named_subst, rels' @ rels
         ) l ([],[])
       in
        C.Appl l', rels
    | C.Const (uri,exp_named_subst) ->
       let exp_named_subst',rels = 
        List.fold_right
         (fun (uri,t) (exp_named_subst,rels) ->
           let t',rels' = aux k t in
            (uri,t')::exp_named_subst, rels' @ rels
         ) exp_named_subst ([],[])
       in
        C.Const (uri,exp_named_subst'),rels
    | C.MutInd (uri,tyno,exp_named_subst) ->
       let exp_named_subst',rels = 
        List.fold_right
         (fun (uri,t) (exp_named_subst,rels) ->
           let t',rels' = aux k t in
            (uri,t')::exp_named_subst, rels' @ rels
         ) exp_named_subst ([],[])
       in
        C.MutInd (uri,tyno,exp_named_subst'),rels
    | C.MutConstruct (uri,tyno,consno,exp_named_subst) ->
       let exp_named_subst',rels = 
        List.fold_right
         (fun (uri,t) (exp_named_subst,rels) ->
           let t',rels' = aux k t in
            (uri,t')::exp_named_subst, rels' @ rels
         ) exp_named_subst ([],[])
       in
        C.MutConstruct (uri,tyno,consno,exp_named_subst'),rels
    | C.MutCase (sp,i,outty,t,pl) ->
       let outty',rels1 = aux k outty in
       let t',rels2 = aux k t in
       let pl',rels3 =
        List.fold_right
         (fun t (exp_named_subst,rels) ->
           let t',rels' = aux k t in
            t'::exp_named_subst, rels' @ rels
         ) pl ([],[])
       in
        C.MutCase (sp, i, outty', t', pl'), rels1 @ rels2 @rels3
    | C.Fix (i, fl) ->
       let len = List.length fl in
       let fl',rels =
        List.fold_right
         (fun (name,i,ty,bo) (fl,rels) ->
           let ty',rels1 = aux k ty in
           let bo',rels2 = aux (k + len) bo in
            (name,i,ty',bo')::fl, rels1 @ rels2 @ rels
         ) fl ([],[])
       in
        C.Fix (i, fl'),rels
    | C.CoFix (i, fl) ->
       let len = List.length fl in
       let fl',rels =
        List.fold_right
         (fun (name,ty,bo) (fl,rels) ->
           let ty',rels1 = aux k ty in
           let bo',rels2 = aux (k + len) bo in
            (name,ty',bo')::fl, rels1 @ rels2 @ rels
         ) fl ([],[])
       in
        C.CoFix (i, fl'),rels
  in
   fst (aux 0 t)
;;
