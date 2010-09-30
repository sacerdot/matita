(* Copyright (C) 2003-2005, HELM Team.
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

module C    = Cic
module E    = CicEnvironment
module Un   = CicUniv
module TC   = CicTypeChecker
module UM   = UriManager
module Rd   = CicReduction
module PEH  = ProofEngineHelpers
module PT   = PrimitiveTactics
module DTI  = DoubleTypeInference

module H    = ProceduralHelpers

(* helpers ******************************************************************)

let rec list_sub start length = function
   | _  :: tl when start  > 0 -> list_sub (pred start) length tl
   | hd :: tl when length > 0 -> hd :: list_sub start (pred length) tl
   | _                        -> []
    
(* proof construction *******************************************************)

let iter f k =
   let rec iter_xns k (uri, t) = uri, iter_term k t
   and iter_ms k = function
      | None   -> None
      | Some t -> Some (iter_term k t)
   and iter_fix len k (id, name, i, ty, bo) =
      id, name, i, iter_term k ty, iter_term (k + len) bo
   and iter_cofix len k (id, name, ty, bo) =
      id, name, iter_term k ty, iter_term (k + len) bo
   and iter_term k = function
      | C.ASort _ as t -> t
      | C.AImplicit _ as t -> t
      | C.ARel (id, rid, m, b) as t -> 
         if m < k then t else f k id rid m b
      | C.AConst (id, uri, xnss) -> C.AConst (id, uri, List.map (iter_xns k) xnss)
      | C.AVar (id, uri, xnss) -> C.AVar (id, uri, List.map (iter_xns k) xnss)
      | C.AMutInd (id, uri, tyno, xnss) -> C.AMutInd (id, uri, tyno, List.map (iter_xns k) xnss)
      | C.AMutConstruct (id, uri, tyno, consno, xnss) -> C.AMutConstruct (id, uri,tyno,consno, List.map (iter_xns k) xnss)
      | C.AMeta (id, i, mss) -> C.AMeta(id, i, List.map (iter_ms k) mss)
      | C.AAppl (id, ts) -> C.AAppl (id, List.map (iter_term k) ts)
      | C.ACast (id, te, ty) -> C.ACast (id, iter_term k te, iter_term k ty)
      | C.AMutCase (id, sp, i, outty, t, pl) -> C.AMutCase (id, sp, i, iter_term k outty, iter_term k t, List.map (iter_term k) pl)
      | C.AProd (id, n, s, t) -> C.AProd (id, n, iter_term k s, iter_term (succ k) t)
      | C.ALambda (id, n, s, t) -> C.ALambda (id, n, iter_term k s, iter_term (succ k) t)
      | C.ALetIn (id, n, ty, s, t) -> C.ALetIn (id, n, iter_term k ty, iter_term k s, iter_term (succ k) t)
      | C.AFix (id, i, fl) -> C.AFix (id, i, List.map (iter_fix (List.length fl) k) fl)
      | C.ACoFix (id, i, fl) -> C.ACoFix (id, i, List.map (iter_cofix (List.length fl) k) fl)
   in
   iter_term k

let lift k n =
   let f _ id rid m b =
      if m + n > 0 then C.ARel (id, rid, m + n, b) else
      begin 
         HLog.error (Printf.sprintf "ProceduralConversion.lift: %i %i" m n);
	 assert false
      end
   in
   iter f k

let subst k v =
   let f k id rid m b =
      if m = k then lift 1 (pred k) v else C.ARel (id, rid, pred m, b)
   in
   iter f k

let fake_annotate id c =
   let get_binder c m =
      try match List.nth c (pred m) with
         | Some (C.Name s, _) -> s
         | _ -> assert false
      with
         | Invalid_argument _ -> assert false
   in
   let mk_decl n v = Some (n, C.Decl v) in
   let mk_def n v ty = Some (n, C.Def (v, ty)) in
   let mk_fix (name, _, ty, bo) = mk_def (C.Name name) bo ty in
   let mk_cofix (name, ty, bo) = mk_def (C.Name name) bo ty in
   let rec ann_xns c (uri, t) = uri, ann_term c t
   and ann_ms c = function
      | None -> None
      | Some t -> Some (ann_term c t)
   and ann_fix newc c (name, i, ty, bo) =
      id, name, i, ann_term c ty, ann_term (List.rev_append newc c) bo
   and ann_cofix newc c (name, ty, bo) =
      id, name, ann_term c ty, ann_term (List.rev_append newc c) bo
   and ann_term c = function
      | C.Sort sort -> C.ASort (id, sort)
      | C.Implicit ann -> C.AImplicit (id, ann)
      | C.Rel m -> C.ARel (id, id, m, get_binder c m)
      | C.Const (uri, xnss) -> C.AConst (id, uri, List.map (ann_xns c) xnss)
      | C.Var (uri, xnss) -> C.AVar (id, uri, List.map (ann_xns c) xnss)
      | C.MutInd (uri, tyno, xnss) -> C.AMutInd (id, uri, tyno, List.map (ann_xns c) xnss)
      | C.MutConstruct (uri, tyno, consno, xnss) -> C.AMutConstruct (id, uri,tyno,consno, List.map (ann_xns c) xnss)
      | C.Meta (i, mss) -> C.AMeta(id, i, List.map (ann_ms c) mss)
      | C.Appl ts -> C.AAppl (id, List.map (ann_term c) ts)
      | C.Cast (te, ty) -> C.ACast (id, ann_term c te, ann_term c ty)
      | C.MutCase (sp, i, outty, t, pl) -> C.AMutCase (id, sp, i, ann_term c outty, ann_term c t, List.map (ann_term c) pl)
      | C.Prod (n, s, t) -> C.AProd (id, n, ann_term c s, ann_term (mk_decl n s :: c) t)
      | C.Lambda (n, s, t) -> C.ALambda (id, n, ann_term c s, ann_term (mk_decl n s :: c) t)
      | C.LetIn (n, s, ty, t) -> C.ALetIn (id, n, ann_term c s, ann_term c ty, ann_term (mk_def n s ty :: c) t)
      | C.Fix (i, fl) -> C.AFix (id, i, List.map (ann_fix (List.rev_map mk_fix fl) c) fl)
      | C.CoFix (i, fl) -> C.ACoFix (id, i, List.map (ann_cofix (List.rev_map mk_cofix fl) c) fl)
   in
   ann_term c

let mk_arel k = C.ARel ("", "", k, "")

let mk_aappl ts = C.AAppl ("", ts)

let rec clear_absts f n k = function
   | t when n = 0           -> f k t
   | C.ALambda (_, _, _, t) -> clear_absts f (pred n) (succ k) t
   | t                      ->
      let u = match mk_aappl [lift (succ k) 1 t; mk_arel (succ k)] with
         | C.AAppl (_, [ C.AAppl (id, ts); t]) -> C.AAppl (id, ts @ [t])
         | t                                   -> t
      in
      clear_absts f (pred n) (succ k) u

let hole id = C.AImplicit (id, Some `Hole)

let meta id = C.AImplicit (id, None)

let anon = C.Anonymous

let generalize n =
   let is_meta =
      let map b = function
         | C.AImplicit (_, None) when b -> b
	 | _                            -> false
      in
      List.fold_left map true
   in
   let rec gen_fix len k (id, name, i, ty, bo) =
      id, name, i, gen_term k ty, gen_term (k + len) bo
   and gen_cofix len k (id, name, ty, bo) =
      id, name, gen_term k ty, gen_term (k + len) bo
   and gen_term k = function
      | C.ASort (id, _) 
      | C.AImplicit (id, _)
      | C.AConst (id, _, _)
      | C.AVar (id, _, _)
      | C.AMutInd (id, _, _, _)
      | C.AMutConstruct (id, _, _, _, _)
      | C.AMeta (id, _, _) -> meta id
      | C.ARel (id, _, m, _) -> 
         if succ (k - n) <= m && m <= k then hole id else meta id
      | C.AAppl (id, ts) -> 
         let ts = List.map (gen_term k) ts in
         if is_meta ts then meta id else C.AAppl (id, ts)
      | C.ACast (id, te, ty) -> 
         let te, ty = gen_term k te, gen_term k ty in
	 if is_meta [te; ty] then meta id else C.ACast (id, te, ty)
      | C.AMutCase (id, sp, i, outty, t, pl) ->         
	 let outty, t, pl = gen_term k outty, gen_term k t, List.map (gen_term k) pl in
	 if is_meta (outty :: t :: pl) then meta id else hole id (* C.AMutCase (id, sp, i, outty, t, pl) *)
      | C.AProd (id, _, s, t) -> 
         let s, t = gen_term k s, gen_term (succ k) t in
         if is_meta [s; t] then meta id else C.AProd (id, anon, s, t)
      | C.ALambda (id, _, s, t) ->
         let s, t = gen_term k s, gen_term (succ k) t in
         if is_meta [s; t] then meta id else C.ALambda (id, anon, s, t)
      | C.ALetIn (id, _, s, ty, t) -> 
         let s, ty, t = gen_term k s, gen_term k ty, gen_term (succ k) t in
         if is_meta [s; t] then meta id else C.ALetIn (id, anon, s, ty, t)
      | C.AFix (id, i, fl) -> C.AFix (id, i, List.map (gen_fix (List.length fl) k) fl)
      | C.ACoFix (id, i, fl) -> C.ACoFix (id, i, List.map (gen_cofix (List.length fl) k) fl)
   in
   gen_term

let convert g ity k predicate =
   let rec aux = function
      | C.ALambda (_, _, b, ity), C.ALambda (id, n, u, pred) ->
         C.ALambda (id, n, aux (b, u), aux (ity, pred))
      | C.AProd (_, _, b, ity), C.AProd (id, n, u, pred) ->
         C.AProd (id, n, aux (b, u), aux (ity, pred))
      | C.ALetIn (_, _, a, b, ity), C.ALetIn (id, n, v, u, pred) ->
         C.ALetIn (id, n, aux (a, v), aux (b, u), aux (ity, pred))
      | C.AAppl (_, bs), C.AAppl (id, us) when List.length bs = List.length us ->
         let map b u = aux (b,u) in
	 C.AAppl (id, List.map2 map bs us)
      | C.ACast (_, ity, b), C.ACast (id, pred, u) ->
         C.ACast (id, aux (ity, pred), aux (b, u))
      | ity, C.AAppl (_, C.ALambda (_, _, _, pred) :: v :: []) ->
	 aux (ity, subst 1 v pred) 	 
      | ity, C.AAppl (id, C.ALambda (_, _, _, pred) :: v :: vs) ->
         aux (ity, C.AAppl (id, subst 1 v pred :: vs))
      | _, pred                                                 -> pred
   in
   g k (aux (ity, predicate))

let mk_pattern psno ity predicate =
   clear_absts (convert (generalize psno) ity) psno 0 predicate 

let beta v = function
   | C.ALambda (_, _, _, t) -> subst 1 v t
   | _                      -> assert false

let get_clears c p xtypes = 
   let meta = C.Implicit None in
   let rec aux c names p it et = function
      | []                                                -> 
         List.rev c, List.rev names         
      | Some (C.Name name as n, C.Decl v) as hd :: tl     ->
         let hd, names, v = 
	    if DTI.does_not_occur 1 p && DTI.does_not_occur 1 it && DTI.does_not_occur 1 et then 
	       Some (C.Anonymous, C.Decl v), name :: names, meta 
	    else 
	       hd, names, v
	 in
	 let p = C.Lambda (n, v, p) in
	 let it = C.Prod (n, v, it) in
	 let et = C.Prod (n, v, et) in
	 aux (hd :: c) names p it et tl
      | Some (C.Name name as n, C.Def (v, x)) as hd :: tl ->
         let hd, names, v = 
	    if DTI.does_not_occur 1 p && DTI.does_not_occur 1 it && DTI.does_not_occur 1 et then 
	       Some (C.Anonymous, C.Def (v, x)), name :: names, meta
	    else 
	       hd, names, v
	 in
	 let p = C.LetIn (n, v, x, p) in
	 let it = C.LetIn (n, v, x, it) in
	 let et = C.LetIn (n, v, x, et) in
	 aux (hd :: c) names p it et tl
      | Some (C.Anonymous as n, C.Decl v) as hd :: tl     ->
	 let p = C.Lambda (n, meta, p) in
	 let it = C.Lambda (n, meta, it) in
	 let et = C.Lambda (n, meta, et) in
	 aux (hd :: c) names p it et tl
      | Some (C.Anonymous as n, C.Def (v, _)) as hd :: tl ->
	 let p = C.LetIn (n, meta, meta, p) in
	 let it = C.LetIn (n, meta, meta, it) in
	 let et = C.LetIn (n, meta, meta, et) in
	 aux (hd :: c) names p it et tl
      | None :: tl                                        -> assert false
   in
   match xtypes with 
      | Some (it, et) -> aux [] [] p it et c
      | None          -> c, []

let clear c hyp =
   let rec aux c = function
      | []            -> List.rev c
      | Some (C.Name name, entry) :: tail when name = hyp ->
	 aux (Some (C.Anonymous, entry) :: c) tail
      | entry :: tail -> aux (entry :: c) tail
   in
   aux [] c
(*
let elim_inferred_type context goal arg using cpattern =
   let metasenv, ugraph = [], Un.default_ugraph in
   let ety = H.get_type "elim_inferred_type" context using in
   let _splits, args_no = PEH.split_with_whd (context, ety) in
   let _metasenv, _subst, predicate, _arg, actual_args = 
     PT.mk_predicate_for_elim 
     ~context ~metasenv ~subst:[] ~ugraph ~goal ~arg ~using ~cpattern ~args_no
   in
   let ty = C.Appl (predicate :: actual_args) in
   let upto = List.length actual_args in
   Rd.head_beta_reduce ~delta:false ~upto ty
*)
let does_not_occur = function
   | C.AImplicit (_, None) -> true
   | _                     -> false
