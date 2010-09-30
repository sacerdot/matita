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

module UM = UriManager
module C  = Cic

module Int = struct
   type t = int
   let compare = compare 
end
module S = Set.Make (Int) 

let overlaps s1 s2 =
   let predicate x = S.mem x s1 in
   S.exists predicate s2

let get_rels_from_premise h t = 
   let rec aux d g = function
      | C.Sort _
      | C.Implicit _       -> g
      | C.Rel i            -> 
         if i < d then g else fun a -> g (S.add (i - d + h + 1) a)
      | C.Appl ss          -> List.fold_left (aux d) g ss
      | C.Const (_, ss)
      | C.MutInd (_, _, ss)
      | C.MutConstruct (_, _, _, ss)
      | C.Var (_, ss)      -> 
         let map g (_, t) = aux d g t in 
	 List.fold_left map g ss
      | C.Meta (_, ss)     ->
         let map g = function 
	    | None   -> g
	    | Some t -> aux d g t
	 in
	 List.fold_left map g ss
      | C.Cast (t1, t2)    -> aux d (aux d g t2) t1
      | C.Lambda (_, t1, t2)
      | C.Prod (_, t1, t2) -> aux d (aux (succ d) g t2) t1
      | C.LetIn (_, t1, ty, t2) ->
         aux d (aux d (aux (succ d) g t2) ty) t1
      | C.MutCase (_, _, t1, t2, ss) ->
	 aux d (aux d (List.fold_left (aux d) g ss) t2) t1
      | C.Fix (_, ss) ->
         let k = List.length ss in
	 let map g (_, _, t1, t2) = aux d (aux (d + k) g t2) t1 in
	 List.fold_left map g ss
      | C.CoFix (_, ss) ->
         let k = List.length ss in
	 let map g (_, t1, t2) = aux d (aux (d + k) g t2) t1 in
	 List.fold_left map g ss
   in
   let g a = a in
   aux 1 g t S.empty

let get_mutinds_of_uri u t = 
   let rec aux g = function
      | C.Sort _
      | C.Implicit _
      | C.Rel _                      -> g
      | C.Appl ss                    -> List.fold_left aux g ss
      | C.Const (_, ss)
      | C.MutConstruct (_, _, _, ss)
      | C.Var (_, ss)                -> 
         let map g (_, t) = aux g t in 
	 List.fold_left map g ss
      | C.MutInd (uri, tyno, ss)     ->
	 let map g (_, t) = aux g t in 
	 let g = List.fold_left map g ss in
         if UM.eq u uri then fun a -> g (S.add tyno a) else g
      | C.Meta (_, ss)               ->
         let map g = function 
	    | None   -> g
	    | Some t -> aux g t
	 in
	 List.fold_left map g ss
      | C.Cast (t1, t2)              -> aux (aux g t2) t1
      | C.Lambda (_, t1, t2)
      | C.Prod (_, t1, t2) -> aux (aux g t2) t1
      | C.LetIn (_, t1, ty, t2) -> aux (aux (aux g t2) ty) t1
      | C.MutCase (_, _, t1, t2, ss) ->
	 aux (aux (List.fold_left aux g ss) t2) t1
      | C.Fix (_, ss)                ->
	 let map g (_, _, t1, t2) = aux (aux g t2) t1 in
	 List.fold_left map g ss
      | C.CoFix (_, ss)              ->
	 let map g (_, t1, t2) = aux (aux g t2) t1 in
	 List.fold_left map g ss
   in
   let g a = a in
   aux g t S.empty

let count_nodes ~meta n t =
   let offset = if meta then 1 else 0 in
   let rec aux n = function
      | C.Implicit _                 -> offset + n
      | C.Sort _
      | C.Rel _                      -> succ n
      | C.Appl ts                    -> 
         List.fold_left aux (List.length ts - 1 + n) ts
      | C.Const (_, ss)
      | C.MutConstruct (_, _, _, ss)
      | C.MutInd (_, _, ss)
      | C.Var (_, ss)                -> 
         let map n (_, t) = aux n t in 
         List.fold_left map (succ n) ss
      | C.Meta (_, ss)               ->
         let map n = function 
	    | None   -> n
	    | Some t -> aux n t
         in
         List.fold_left map (n + offset) ss
      | C.Cast (t1, t2) -> aux (aux (offset + n) t2) t1
      | C.Lambda (_, t1, t2)
      | C.Prod (_, t1, t2) -> aux (aux (succ n) t2) t1
      | C.LetIn (_, t1, ty, t2) -> aux (aux (aux (offset + n) t2) ty) t1
      | C.MutCase (_, _, t1, t2, ss) ->
         aux (aux (List.fold_left aux (offset + 1 + n) ss) t2) t1
      | C.Fix (_, ss)                ->
         let map n (_, _, t1, t2) = aux (aux n t2) t1 in
         List.fold_left map (2 + n) ss
      | C.CoFix (_, ss)              ->
         let map n (_, t1, t2) = aux (aux n t2) t1 in
         List.fold_left map (2 + n) ss
in
aux n t
