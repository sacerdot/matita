(* Copyright (C) 2000, HELM Team.
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

let unshare ?(fresh_univs=false) t =
 let module C = Cic in
 let rec unshare =
  function
     C.Rel m -> C.Rel m
   | C.Var (uri,exp_named_subst) ->
      let exp_named_subst' = 
       List.map (function (uri,t) -> (uri,unshare t)) exp_named_subst
      in
       C.Var (uri,exp_named_subst')
   | C.Meta (i,l) ->
      let l' =
       List.map
        (function
            None -> None
          | Some t -> Some (unshare t)
        ) l
      in
       C.Meta(i,l')
   | C.Sort s when not fresh_univs -> C.Sort s
   | C.Sort (C.Type _) -> C.Sort (C.Type (CicUniv.fresh ()))
   | C.Sort s -> C.Sort s
   | C.Implicit info -> C.Implicit info
   | C.Cast (te,ty) -> C.Cast (unshare te, unshare ty)
   | C.Prod (n,s,t) -> C.Prod (n, unshare s, unshare t)
   | C.Lambda (n,s,t) -> C.Lambda (n, unshare s, unshare t)
   | C.LetIn (n,s,ty,t) ->
      C.LetIn (n, unshare s, unshare ty, unshare t)
   | C.Appl l -> C.Appl (List.map unshare l)
   | C.Const (uri,exp_named_subst) ->
      let exp_named_subst' = 
       List.map (function (uri,t) -> (uri,unshare t)) exp_named_subst
      in
       C.Const (uri,exp_named_subst')
   | C.MutInd (uri,tyno,exp_named_subst) ->
      let exp_named_subst' = 
       List.map (function (uri,t) -> (uri,unshare t)) exp_named_subst
      in
       C.MutInd (uri,tyno,exp_named_subst')
   | C.MutConstruct (uri,tyno,consno,exp_named_subst) ->
      let exp_named_subst' = 
       List.map (function (uri,t) -> (uri,unshare t)) exp_named_subst
      in
       C.MutConstruct (uri,tyno,consno,exp_named_subst')
   | C.MutCase (sp,i,outty,t,pl) ->
      C.MutCase (sp, i, unshare outty, unshare t,
       List.map unshare pl)
   | C.Fix (i, fl) ->
      let liftedfl =
       List.map
        (fun (name, i, ty, bo) -> (name, i, unshare ty, unshare bo))
         fl
      in
       C.Fix (i, liftedfl)
   | C.CoFix (i, fl) ->
      let liftedfl =
       List.map
        (fun (name, ty, bo) -> (name, unshare ty, unshare bo))
         fl
      in
       C.CoFix (i, liftedfl)
 in
  unshare t
;;

let sharing_map f l =
  let unchanged = ref true in
  let rec aux b = function
    | [] as t -> unchanged := b; t
    | he::tl ->
        let he1 = f he in
        he1 :: aux (b && he1 == he) tl
  in
  let l1 = aux true l in
  if !unchanged then l else l1
;;

let fresh_univs t =
 let module C = Cic in
 let rec unshare =
  function
   | C.Sort (C.Type u) when not (CicUniv.is_anon u) -> C.Sort (C.Type (CicUniv.fresh ()))
   | C.Sort _ | C.Implicit _ | C.Var _ | C.Rel _ as t -> t
   | C.Meta (i,l) as orig -> 
      let l' = sharing_map 
        (function None -> None | Some t -> Some (unshare t)) l
      in
      if l == l' then orig else C.Meta(i,l')
   | C.Cast (te,ty) as orig -> 
      let te' = unshare te in 
      let ty' = unshare ty in
      if te' == te && ty' == ty then orig else C.Cast(te', ty')
   | C.Prod (n,s,t) as orig -> 
      let s' = unshare s in             
      let t' = unshare t in             
      if s' == s && t' == t then orig else C.Prod(n,s',t')
   | C.Lambda (n,s,t) as orig -> 
      let s' = unshare s in             
      let t' = unshare t in             
      if s' == s && t' == t then orig else C.Lambda(n,s',t')
   | C.LetIn (n,s,ty,t) as orig ->
      let s' = unshare s in             
      let t' = unshare t in             
      let ty' = unshare ty in             
      if t' == t && ty' == ty && s' == s then orig else C.LetIn (n, s', ty', t')
   | C.Appl l as orig -> 
      let l' = sharing_map unshare l in 
      if l == l' then orig else C.Appl l'
   | C.Const (uri,exp_named_subst) as orig ->
      let exp_named_subst' = 
        sharing_map 
          (fun (uri,t as orig) -> 
            let t' = unshare t in 
            if t == t' then orig else (uri,t')) 
          exp_named_subst
      in
      if exp_named_subst' == exp_named_subst then orig
      else C.Const (uri,exp_named_subst')
   | C.MutInd (uri,tyno,exp_named_subst) as orig ->
      let exp_named_subst' = 
        sharing_map 
          (fun (uri,t as orig) -> 
            let t' = unshare t in 
            if t == t' then orig else (uri,t')) 
          exp_named_subst
      in
      if exp_named_subst' == exp_named_subst then orig
      else C.MutInd (uri,tyno,exp_named_subst')
   | C.MutConstruct (uri,tyno,consno,exp_named_subst) as orig ->
      let exp_named_subst' = 
        sharing_map 
          (fun (uri,t as orig) -> 
            let t' = unshare t in 
            if t == t' then orig else (uri,t')) 
          exp_named_subst
      in
      if exp_named_subst' == exp_named_subst then orig
      else C.MutConstruct (uri,tyno,consno,exp_named_subst')
   | C.MutCase (sp,i,outty,t,pl) as orig ->
      let t' = unshare t in 
      let pl' = sharing_map unshare pl in
      let outty' = unshare outty in
      if t' == t && pl' == pl && outty' == outty then orig
      else C.MutCase (sp, i, outty', t', pl')
   | C.Fix (i, fl) as orig ->
      let fl' =
       sharing_map
        (fun (name, i, ty, bo as orig) -> 
           let ty' = unshare ty in
           let bo' = unshare bo in
           if ty' == ty && bo' == bo then orig else name,i,ty',bo')
         fl
      in
      if fl' == fl then orig else C.Fix (i, fl')
   | C.CoFix (i, fl) as orig ->
      let fl' =
       sharing_map
        (fun (name, ty, bo as orig) -> 
           let ty' = unshare ty in
           let bo' = unshare bo in
           if ty' == ty && bo' == bo then orig else name,ty',bo')
         fl
      in
      if fl' == fl then orig else C.CoFix (i, fl')
 in
  unshare t
;;

let fresh_types = 
  let module C = Cic in
  let unshare = fresh_univs in      
  function
   | C.Constant (name,te,ty,exp,att) ->
        C.Constant (name,HExtlib.map_option unshare te,
          unshare ty,exp,att)
   | C.CurrentProof _ -> assert false
   | C.Variable _ -> assert false
   | C.InductiveDefinition (itl,u,i,att) ->
        C.InductiveDefinition
          (List.map 
            (fun (name,b,t,cl) -> 
               name,b,unshare t,
               List.map 
                 (fun (name,t) -> name, unshare t) 
                 cl) 
            itl,u,i,att)
;;
