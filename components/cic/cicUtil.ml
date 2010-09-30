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

module C  = Cic
module UM = UriManager

exception Meta_not_found of int
exception Subst_not_found of int

let lookup_meta index metasenv =
  try
    List.find (fun (index', _, _) -> index = index') metasenv
  with Not_found -> raise (Meta_not_found index)

let lookup_subst n subst =
  try
    List.assoc n subst
  with Not_found -> raise (Subst_not_found n)

let exists_meta index = List.exists (fun (index', _, _) -> (index = index'))

(* clean_up_meta take a substitution, a metasenv a meta_inex and a local
context l and clean up l with respect to the hidden hipothesis in the 
canonical context *)

let clean_up_local_context subst metasenv n l =
  let cc =
    (try
       let (cc,_,_) = lookup_subst n subst in cc
     with Subst_not_found _ ->
       try
	 let (_,cc,_) = lookup_meta n metasenv in cc
       with Meta_not_found _ -> assert false) in
  (try 
     List.map2
       (fun t1 t2 ->
	  match t1,t2 with 
	      None , _ -> None
	    | _ , t -> t) cc l
   with 
       Invalid_argument _ -> 
	 assert false)

let is_closed =
 let module C = Cic in
 let rec is_closed k =
  function
      C.Rel m when m > k -> false
    | C.Rel m -> true
    | C.Meta (_,l) ->
       List.fold_left
        (fun i t -> i && (match t with None -> true | Some t -> is_closed k t)
        ) true l
    | C.Sort _ -> true
    | C.Implicit _ -> assert false
    | C.Cast (te,ty) -> is_closed k te && is_closed k ty
    | C.Prod (name,so,dest) -> is_closed k so && is_closed (k+1) dest
    | C.Lambda (_,so,dest) -> is_closed k so && is_closed (k+1) dest
    | C.LetIn (_,so,ty,dest) ->
       is_closed k so && is_closed k ty && is_closed (k+1) dest
    | C.Appl l ->
       List.fold_right (fun x i -> i && is_closed k x) l true
    | C.Var (_,exp_named_subst)
    | C.Const (_,exp_named_subst)
    | C.MutInd (_,_,exp_named_subst)
    | C.MutConstruct (_,_,_,exp_named_subst) ->
       List.fold_right (fun (_,x) i -> i && is_closed k x)
        exp_named_subst true
    | C.MutCase (_,_,out,te,pl) ->
       is_closed k out && is_closed k te &&
        List.fold_right (fun x i -> i && is_closed k x) pl true
    | C.Fix (_,fl) ->
       let len = List.length fl in
        let k_plus_len = k + len in
         List.fold_right
          (fun (_,_,ty,bo) i -> i && is_closed k ty && is_closed k_plus_len bo
          ) fl true
    | C.CoFix (_,fl) ->
       let len = List.length fl in
        let k_plus_len = k + len in
         List.fold_right
          (fun (_,ty,bo) i -> i && is_closed k ty && is_closed k_plus_len bo
          ) fl true
in 
 is_closed 0
;;

let rec is_meta_closed =
  function
      C.Rel _ -> true
    | C.Meta _ -> false
    | C.Sort _ -> true
    | C.Implicit _ -> assert false
    | C.Cast (te,ty) -> is_meta_closed te && is_meta_closed ty
    | C.Prod (name,so,dest) -> is_meta_closed so && is_meta_closed dest
    | C.Lambda (_,so,dest) -> is_meta_closed so && is_meta_closed dest
    | C.LetIn (_,so,ty,dest) ->
       is_meta_closed so &&
       is_meta_closed ty &&
       is_meta_closed dest
    | C.Appl l ->
       not (List.exists (fun x -> not (is_meta_closed x)) l)
    | C.Var (_,exp_named_subst)
    | C.Const (_,exp_named_subst)
    | C.MutInd (_,_,exp_named_subst)
    | C.MutConstruct (_,_,_,exp_named_subst) ->
       not (List.exists (fun (_,x) -> not (is_meta_closed x)) exp_named_subst)
    | C.MutCase (_,_,out,te,pl) ->
       is_meta_closed out && is_meta_closed te &&
        not (List.exists (fun x -> not (is_meta_closed x)) pl)
    | C.Fix (_,fl) ->
        not (List.exists 
              (fun (_,_,ty,bo) -> 
                  not (is_meta_closed ty) || not (is_meta_closed bo)) 
              fl)
    | C.CoFix (_,fl) ->
        not (List.exists 
              (fun (_,ty,bo) -> 
                  not (is_meta_closed ty) || not (is_meta_closed bo)) 
              fl)
;;

let xpointer_RE = Str.regexp "\\([^#]+\\)#xpointer(\\(.*\\))"
let slash_RE = Str.regexp "/"

let term_of_uri uri =
  let s = UriManager.string_of_uri uri in
  try
    (if UriManager.uri_is_con uri then
      C.Const (uri, [])
    else if UriManager.uri_is_var uri then
      C.Var (uri, [])
    else if not (Str.string_match xpointer_RE s 0) then
      raise (UriManager.IllFormedUri s)
    else
      let (baseuri,xpointer) = (Str.matched_group 1 s, Str.matched_group 2 s) in
      let baseuri = UriManager.uri_of_string baseuri in
      (match Str.split slash_RE xpointer with
      | [_; tyno] -> C.MutInd (baseuri, int_of_string tyno - 1, [])
      | [_; tyno; consno] ->
          C.MutConstruct
            (baseuri, int_of_string tyno - 1, int_of_string consno, [])
      | _ -> raise Exit))
  with
  | Exit
  | Failure _
  | Not_found -> raise (UriManager.IllFormedUri s)

let uri_of_term = function
  | C.Const (uri, _)
  | C.Var (uri, _) -> uri
  | C.MutInd (baseuri, tyno, _) ->
     UriManager.uri_of_string
      (Printf.sprintf "%s#xpointer(1/%d)" (UriManager.string_of_uri baseuri) (tyno+1))
  | C.MutConstruct (baseuri, tyno, consno, _) ->
     UriManager.uri_of_string
      (Printf.sprintf "%s#xpointer(1/%d/%d)" (UriManager.string_of_uri baseuri)
        (tyno + 1) consno)
  | _ -> raise (Invalid_argument "uri_of_term")


(*
let pack terms =
  List.fold_right
    (fun term acc -> C.Prod (C.Anonymous, term, acc))
    terms (C.Sort (C.Type (CicUniv.fresh ())))

let rec unpack = function
  | C.Prod (C.Anonymous, term, C.Sort (C.Type _)) -> [term]
  | C.Prod (C.Anonymous, term, tgt) -> term :: unpack tgt
  | _ -> assert false
*)

let rec strip_prods n = function
  | t when n = 0 -> t
  | C.Prod (_, _, tgt) when n > 0 -> strip_prods (n-1) tgt
  | _ -> failwith "not enough prods"

let params_of_obj = function
  | C.Constant (_, _, _, params, _)
  | C.Variable (_, _, _, params, _)
  | C.CurrentProof (_, _, _, _, params, _)
  | C.InductiveDefinition (_, params, _, _) ->
      params

let attributes_of_obj = function
  | C.Constant (_, _, _, _, attributes)
  | C.Variable (_, _, _, _, attributes)
  | C.CurrentProof (_, _, _, _, _, attributes)
  | C.InductiveDefinition (_, _, _, attributes) ->
      attributes

let is_generated obj = List.exists ((=) `Generated) (attributes_of_obj obj)

let projections_of_record obj uri =
  let attrs = attributes_of_obj obj in
  try
    let tag=List.find (function `Class (`Record _) -> true|_->false) attrs in
    match tag with
    |  `Class (`Record l) -> 
         List.map (fun (name,_,_) ->
           let buri = UriManager.buri_of_uri uri in
           let puri = UriManager.uri_of_string (buri ^ "/" ^ name ^ ".con") in
           puri) l
    | _-> assert false 
  with Not_found -> []
;;
      
let rec mk_rels howmany from =
  match howmany with 
  | 0 -> []
  | _ -> (C.Rel (howmany + from)) :: (mk_rels (howmany-1) from)

let id_of_annterm =
  function
  | C.ARel (id,_,_,_)
  | C.AVar (id,_,_)
  | C.AMeta (id,_,_)
  | C.ASort (id,_)
  | C.AImplicit (id,_)
  | C.ACast (id,_,_)
  | C.AProd (id,_,_,_)
  | C.ALambda (id,_,_,_)
  | C.ALetIn (id,_,_,_,_)
  | C.AAppl (id,_)
  | C.AConst (id,_,_)
  | C.AMutInd (id,_,_,_)
  | C.AMutConstruct (id,_,_,_,_)
  | C.AMutCase (id,_,_,_,_,_)
  | C.AFix (id,_,_)
  | C.ACoFix (id,_,_) -> id


let rec rehash_term =
  let module C = Cic in
  let recons uri = UriManager.uri_of_string (UriManager.string_of_uri uri) in
  function
   | (C.Rel _) as t -> t
   | C.Var (uri,exp_named_subst) ->
      let uri' = recons uri in
      let exp_named_subst' =
       List.map
        (function (uri,t) ->(recons uri,rehash_term t)) 
         exp_named_subst
      in
       C.Var (uri',exp_named_subst')
   | C.Meta (i,l) ->
      let l' =
       List.map
        (function
            None -> None
          | Some t -> Some (rehash_term t)
        ) l
      in
       C.Meta(i,l')
   | C.Sort (C.Type u) -> 
       CicUniv.assert_univ u;
       C.Sort (C.Type (CicUniv.recons_univ u))
   | C.Sort _ as t -> t
   | C.Implicit _ as t -> t
   | C.Cast (te,ty) -> C.Cast (rehash_term te, rehash_term ty)
   | C.Prod (n,s,t) -> C.Prod (n, rehash_term s, rehash_term t)
   | C.Lambda (n,s,t) -> C.Lambda (n, rehash_term s, rehash_term t)
   | C.LetIn (n,s,ty,t) ->
      C.LetIn (n, rehash_term s, rehash_term ty, rehash_term t)
   | C.Appl l -> C.Appl (List.map rehash_term l)
   | C.Const (uri,exp_named_subst) ->
      let uri' = recons uri in
      let exp_named_subst' = 
       List.map
        (function (uri,t) -> (recons uri,rehash_term t)) exp_named_subst
      in
       C.Const (uri',exp_named_subst')
   | C.MutInd (uri,tyno,exp_named_subst) ->
      let uri' = recons uri in
      let exp_named_subst' = 
       List.map
        (function (uri,t) -> (recons uri,rehash_term t)) exp_named_subst
      in
       C.MutInd (uri',tyno,exp_named_subst')
   | C.MutConstruct (uri,tyno,consno,exp_named_subst) ->
      let uri' = recons uri in
      let exp_named_subst' = 
       List.map
        (function (uri,t) -> (recons uri,rehash_term t)) exp_named_subst
      in
       C.MutConstruct (uri',tyno,consno,exp_named_subst')
   | C.MutCase (uri,i,outty,t,pl) ->
      C.MutCase (recons uri, i, rehash_term outty, rehash_term t,
       List.map rehash_term pl)
   | C.Fix (i, fl) ->
      let liftedfl =
       List.map
        (fun (name, i, ty, bo) ->
          (name, i, rehash_term ty, rehash_term bo))
         fl
      in
       C.Fix (i, liftedfl)
   | C.CoFix (i, fl) ->
      let liftedfl =
       List.map
        (fun (name, ty, bo) -> (name, rehash_term ty, rehash_term bo))
         fl
      in
       C.CoFix (i, liftedfl)

let rehash_obj =
 let module C = Cic in
 let recons uri = UriManager.uri_of_string (UriManager.string_of_uri uri) in
 function 
   C.Constant (name,bo,ty,params,attrs) ->
     let bo' =
       match bo with
         None -> None
       | Some bo -> Some (rehash_term bo)
     in
     let ty' = rehash_term ty in
     let params' = List.map recons params in
     C.Constant (name, bo', ty', params',attrs)
 | C.CurrentProof (name,conjs,bo,ty,params,attrs) ->
     let conjs' =
       List.map
         (function (i,hyps,ty) ->
           (i,
           List.map (function
               None -> None
             | Some (name,C.Decl t) ->
                 Some (name,C.Decl (rehash_term t))
             | Some (name,C.Def (bo,ty)) ->
                 Some (name,C.Def (rehash_term bo, rehash_term ty))) hyps,
           rehash_term ty))
         conjs
     in
     let bo' = rehash_term bo in
     let ty' = rehash_term ty in
     let params' = List.map recons params in
     C.CurrentProof (name, conjs', bo', ty', params',attrs)
 | C.Variable (name,bo,ty,params,attrs) ->
     let bo' =
       match bo with
         None -> None
       | Some bo -> Some (rehash_term bo)
     in
     let ty' = rehash_term ty in
     let params' = List.map recons params in
     C.Variable (name, bo', ty', params',attrs)
 | C.InductiveDefinition (tl,params,paramsno,attrs) ->
     let params' = List.map recons params in
     let tl' =
       List.map (function (name, inductive, ty, constructors) ->
         name,
         inductive,
         rehash_term ty,
         (List.map
           (function (name, ty) -> name, rehash_term ty)
           constructors))
         tl
     in
     C.InductiveDefinition (tl', params', paramsno, attrs)

let rec metas_of_term = function
  | C.Meta (i, c) -> [i,c]
  | C.Var (_, ens) 
  | C.Const (_, ens) 
  | C.MutInd (_, _, ens) 
  | C.MutConstruct (_, _, _, ens) ->
      List.flatten (List.map (fun (u, t) -> metas_of_term t) ens)
  | C.Cast (s, t)
  | C.Prod (_, s, t)
  | C.Lambda (_, s, t) -> (metas_of_term s) @ (metas_of_term t)
  | C.LetIn (_, s, ty, t) ->
     (metas_of_term s) @ (metas_of_term ty) @ (metas_of_term t)
  | C.Appl l -> List.flatten (List.map metas_of_term l)
  | C.MutCase (uri, i, s, t, l) ->
      (metas_of_term s) @ (metas_of_term t) @
        (List.flatten (List.map metas_of_term l))
  | C.Fix (i, il) ->
      List.flatten
        (List.map (fun (s, i, t1, t2) ->
                     (metas_of_term t1) @ (metas_of_term t2)) il)
  | C.CoFix (i, il) ->
      List.flatten
        (List.map (fun (s, t1, t2) ->
                     (metas_of_term t1) @ (metas_of_term t2)) il)
  | _ -> []
;;      

module MetaOT = struct
  type t = int * C.term option list
  let compare = Pervasives.compare
end

module S = Set.Make(MetaOT)

let rec metas_of_term_set = function
  | C.Meta (i, c) -> S.singleton (i,c)
  | C.Var (_, ens) 
  | C.Const (_, ens) 
  | C.MutInd (_, _, ens) 
  | C.MutConstruct (_, _, _, ens) ->
      List.fold_left 
        (fun s (_,t) -> S.union s (metas_of_term_set t)) 
        S.empty ens
  | C.Cast (s, t)
  | C.Prod (_, s, t)
  | C.Lambda (_, s, t) -> S.union (metas_of_term_set s) (metas_of_term_set t)
  | C.LetIn (_, s, ty, t) ->
     S.union (metas_of_term_set s)
      (S.union (metas_of_term_set ty) (metas_of_term_set t))
  | C.Appl l -> 
      List.fold_left 
        (fun s t -> S.union s (metas_of_term_set t)) 
        S.empty l
  | C.MutCase (uri, i, s, t, l) ->
      S.union 
        (S.union (metas_of_term_set s)  (metas_of_term_set t))
        (List.fold_left 
          (fun s t -> S.union s (metas_of_term_set t)) 
          S.empty l)
  | C.Fix (_, il) ->
      (List.fold_left 
        (fun s (_,_,t1,t2) -> 
          S.union s (S.union (metas_of_term_set t1) (metas_of_term_set t2))))
        S.empty il
  | C.CoFix (i, il) ->
      (List.fold_left 
        (fun s (_,t1,t2) -> 
          S.union s (S.union (metas_of_term_set t1) (metas_of_term_set t2))))
        S.empty il
  | _ -> S.empty
;;      

let metas_of_term_set t = 
  let s = metas_of_term_set t in
  S.elements s
;;

(* syntactic_equality up to the                 *)
(* distinction between fake dependent products  *)
(* and non-dependent products, alfa-conversion  *)
let alpha_equivalence =
  let rec aux t t' =
   if t = t' then true
   else
    match t,t' with
       C.Var (uri1,exp_named_subst1), C.Var (uri2,exp_named_subst2) ->
        UriManager.eq uri1 uri2 &&
         aux_exp_named_subst exp_named_subst1 exp_named_subst2
     | C.Cast (te,ty), C.Cast (te',ty') ->
        aux te te' && aux ty ty'
     | C.Prod (_,s,t), C.Prod (_,s',t') ->
        aux s s' && aux t t'
     | C.Lambda (_,s,t), C.Lambda (_,s',t') ->
        aux s s' && aux t t'
     | C.LetIn (_,s,ty,t), C.LetIn(_,s',ty',t') ->
        aux s s' && aux ty ty' && aux t t'
     | C.Appl l, C.Appl l' when List.length l = List.length l' ->
        (try
          List.fold_left2
           (fun b t1 t2 -> b && aux t1 t2) true l l'
         with
          Invalid_argument _ -> false)
     | C.Const (uri,exp_named_subst1), C.Const (uri',exp_named_subst2) ->
        UriManager.eq uri uri' &&
         aux_exp_named_subst exp_named_subst1 exp_named_subst2
     | C.MutInd (uri,i,exp_named_subst1), C.MutInd (uri',i',exp_named_subst2) ->
        UriManager.eq uri uri' && i = i' &&
         aux_exp_named_subst exp_named_subst1 exp_named_subst2
     | C.MutConstruct (uri,i,j,exp_named_subst1),
       C.MutConstruct (uri',i',j',exp_named_subst2) ->
        UriManager.eq uri uri' && i = i' && j = j' &&
         aux_exp_named_subst exp_named_subst1 exp_named_subst2
     | C.MutCase (sp,i,outt,t,pl), C.MutCase (sp',i',outt',t',pl') ->
        UriManager.eq sp sp' && i = i' &&
         aux outt outt' && aux t t' &&
          (try
            List.fold_left2
             (fun b t1 t2 -> b && aux t1 t2) true pl pl'
           with
            Invalid_argument _ -> false)
     | C.Fix (i,fl), C.Fix (i',fl') ->
        i = i' &&
        (try
          List.fold_left2
           (fun b (_,i,ty,bo) (_,i',ty',bo') ->
             b && i = i' && aux ty ty' && aux bo bo'
           ) true fl fl'
         with
          Invalid_argument _ -> false)
     | C.CoFix (i,fl), C.CoFix (i',fl') ->
        i = i' &&
        (try
          List.fold_left2
           (fun b (_,ty,bo) (_,ty',bo') ->
             b && aux ty ty' && aux bo bo'
           ) true fl fl'
         with
          Invalid_argument _ -> false)
     | C.Meta (i, subst), C.Meta (i', subst') ->
        i = i' &&
        (try
          List.fold_left2
           (fun b xt xt' -> match xt,xt' with
	     | Some t, Some t' -> b && aux t t'
	     | _               -> b
           ) true subst subst'
         with
          Invalid_argument _ -> false)
     | C.Appl [t], t' | t, C.Appl [t'] -> assert false
(* FG: are we _really_ sure of these?      
     | C.Sort (C.Type u), C.Sort (C.Type u') -> u = u' 
     | C.Implicit a, C.Implicit a' -> a = a'
   we insert an unused variable below to genarate a warning at compile time
*)     
     | _,_ -> false (* we already know that t != t' *)
  and aux_exp_named_subst exp_named_subst1 exp_named_subst2 =
   try
     List.fold_left2
      (fun b (uri1,t1) (uri2,t2) ->
        b && UriManager.eq uri1 uri2 && aux t1 t2
      ) true exp_named_subst1 exp_named_subst2
    with
     Invalid_argument _ -> false
  in
   aux

let is_sober c t =
   let rec sober_term c g = function
      | C.Rel i                         ->
         if i <= 0 then fun b -> false else g
      | C.Sort _  
      | C.Implicit _                    -> g      
      | C.Const (_, xnss) 
      | C.Var (_, xnss) 
      | C.MutConstruct (_, _, _, xnss)
      | C.MutInd (_, _, xnss)           -> sober_xnss c g xnss
      | C.Meta (_, xss)                 -> sober_xss c g xss
      | C.Lambda (_, v, t)
      | C.Prod (_, v, t)
      | C.Cast (t, v)                   ->
         sober_term c (sober_term c g t) v
      | C.LetIn (_, v, ty, t)           ->
         sober_term c (sober_term c (sober_term c g t) ty) v
      | C.Appl []                       
      | C.Appl [_]                      
      | C.Appl (C.Appl _ :: _)          -> fun b -> false
      | C.Appl ts                       -> sober_terms c g ts
      | C.MutCase (_, _, t, v, ts)      -> 
         sober_terms c (sober_term c (sober_term c g t) v) ts
      | C.Fix (_, ifs)                  -> sober_ifs c g ifs
      | C.CoFix (_, cifs)               -> sober_cifs c g cifs
   and sober_terms c g = List.fold_left (sober_term c) g
   and sober_xnss c g =
      let map g (_, t) = sober_term c g t in
      List.fold_left map g
   and sober_xss c g =
      let map g = function 
         | None   -> g
	 | Some t -> sober_term c g t
      in
      List.fold_left map g
   and sober_ifs c g =
      let map g (_, _, t, v) = sober_term c (sober_term c g t) v in
      List.fold_left map g
   and sober_cifs c g =
      let map g (_, t, v) = sober_term c (sober_term c g t) v in
      List.fold_left map g
   in 
   sober_term c (fun b -> b) t true

(* raw cic prettyprinter ****************************************************)

let xiter out so ss sc map l =
   let rec aux = function
      | hd :: tl when tl <> [] -> map hd; out ss; aux tl
      | hd :: tl               -> map hd; aux tl
      | []                     -> ()
   in
   out so; aux l; out sc

let abst s w = Some (s, C.Decl w)

let abbr s v w = Some (s, C.Def (v, w))

let pp_sort out = function
   | C.Type _  -> out "*Type"
   | C.Prop    -> out "*Prop"
   | C.CProp _ -> out "*CProp"
   | C.Set     -> out "*Set"

let pp_name out = function
   | C.Name s    -> out s
   | C.Anonymous -> out "_"

let pp_rel out c i =
   try match List.nth c (pred i) with
      | None           -> out (Printf.sprintf "%u[?]" i)
      | Some (s, _)    -> out (Printf.sprintf "%u[" i); pp_name out s; out "]"
   with Failure "nth" -> out (Printf.sprintf "%u[%i]" i (List.length c - i))

let pp_implicit out = function
   | None         -> out "?"
   | Some `Closed -> out "?[Closed]" 
   | Some `Type   -> out "?[Type]"
   | Some `Hole   -> out "?[Hole]"
   | Some `Vector -> out "?[...]"

let pp_uri out a =
   out (Printf.sprintf "%s<%s>" (UM.name_of_uri a) (UM.string_of_uri a)) 

let rec pp_term out e c = function
   | C.Sort h                      -> pp_sort out h
   | C.Rel i                       -> pp_rel out c i
   | C.Implicit x                  -> pp_implicit out x
   | C.Meta (i, iss)               ->
      let map = function None   -> out "_" | Some v -> pp_term out e c v in
      out (Printf.sprintf "?%u" i); xiter out "[" "; " "]" map iss
   | C.Var (a, xss)              ->
      pp_uri out a; pp_xss out e c xss
   | C.Const (a, xss)              ->
      pp_uri out a; pp_xss out e c xss
   | C.MutInd (a, m, xss)          ->
      pp_uri out a; out (Printf.sprintf "/%u" m);
      pp_xss out e c xss
   | C.MutConstruct (a, m, n, xss) ->
      pp_uri out a; out (Printf.sprintf "/%u/%u" m n);
      pp_xss out e c xss
   | C.Cast (v, w)                 ->
      out "type "; pp_term out e c w; out " contains "; pp_term out e c v
   | C.Appl vs                     ->
      xiter out "(" " @ " ")" (pp_term out e c) vs
   | C.MutCase (a, m, w, v, vs)    ->
      out "match "; pp_term out e c v;
      out " of "; pp_uri out a; out (Printf.sprintf "/%u" m);
      out " to "; pp_term out e c w;
      xiter out " cases " " | " "" (pp_term out e c) vs
   | C.Prod (s, w, t)             ->
      out "forall "; pp_name out s; out " of "; pp_term out e c w;
      out " in "; pp_term out e (abst s w :: c) t
   | C.Lambda (s, w, t)            ->
      out "fun "; pp_name out s; out " of "; pp_term out e c w;
      out " in "; pp_term out e (abst s w :: c) t
   | C.LetIn (s, v, w, t)          ->
      out "let "; pp_name out s; 
      out " def "; pp_term out e c v; out " of "; pp_term out e c w;
      out " in "; pp_term out e (abbr s v w :: c) t
   | C.Fix (i, fs)                 ->
      let map c (s, _, w, v) = abbr (C.Name s) v w :: c in
      let c' = List.fold_left map c fs in
      let map (s, i, w, v) =
         out (Printf.sprintf "%s[%u] def " s i); pp_term out e c' v; 
	 out " of "; pp_term out e c w;
      in
      xiter out "let rec " " and " " in " map fs; pp_rel out c' (succ i)
   | C.CoFix (i, fs)                 ->
      let map c (s, w, v) = abbr (C.Name s) v w :: c in
      let c' = List.fold_left map c fs in
      let map (s, w, v) =
         out s; pp_term out e c' v; 
	 out " of "; pp_term out e c w;
      in
      xiter out "let corec " " and " " in " map fs; pp_rel out c' (succ i)

and pp_xss out e c xss = 
   let map (a, v) = pp_uri out a; out " <- "; pp_term out e c v in
   xiter out "[" "; " "]" map xss 

let pp_int out i =
   out (Printf.sprintf "%u" i)

let pp_attrs out attrs = 
   let map = function
      | _ -> ()
   in
   xiter out "[" "; " "] " map attrs 
   
let pp_pars out pars = 
   xiter out " (" ", " ")\n" (pp_uri out) pars 

let pp_point out point =
   if point then out "ind " else out "coind "

let pp_constructor out (s, w) =
   out s; out " of "; pp_term out [] [] w

let pp_definition out (s, point, w, ts) =
   out "let "; pp_point out point; out s; out " of "; pp_term out [] [] w;  
   xiter out "\ndef " "\nor " "" (pp_constructor out) ts

let pp_obj out = function
   | C.Constant (s, None, u, pars, attrs)           ->
      out "fun "; pp_attrs out attrs; out s; pp_pars out pars;
      out " of "; pp_term out [] [] u
   | C.Constant (s, Some t, u, pars, attrs)         ->
      out "let "; pp_attrs out attrs; out s; pp_pars out pars;
      out " def "; pp_term out [] [] t; out " of "; pp_term out [] [] u
   | C.Variable (s, None, u, pars, attrs)           ->
      out "local fun "; pp_attrs out attrs; out s; pp_pars out pars;
      out " of "; pp_term out [] [] u
   | C.Variable (s, Some t, u, pars, attrs)         ->
      out "local let "; pp_attrs out attrs; out s; pp_pars out pars;
      out " def "; pp_term out [] [] t; out " of "; pp_term out [] [] u
   | C.InductiveDefinition (us, pars, lpsno, attrs) ->
      out "Inductive "; pp_attrs out attrs; pp_int out lpsno; pp_pars out pars;
      xiter out "" "\n" "" (pp_definition out) us
   | C.CurrentProof (s, e, t, u, pars, attrs)       ->
      out "Current Proof" 

