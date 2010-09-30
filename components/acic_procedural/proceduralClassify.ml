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

module UM  = UriManager
module C   = Cic
module D   = Deannotate
module I   = CicInspect
module PEH = ProofEngineHelpers

module H   = ProceduralHelpers

type dependences = (I.S.t * bool) list

type conclusion = (int * int * UM.uri * int) option

(* debugging ****************************************************************)

let string_of_entry synth (inverse, b) =
   if I.overlaps synth inverse then begin if b then "CF" else "C" end else
   if I.S.is_empty inverse then "I" else "P"

let to_string synth (classes, rc) =
   let linearize = 
      String.concat " " (List.map (string_of_entry synth) classes)
   in
   match rc with
      | None              -> linearize
      | Some (i, j, _, _) -> Printf.sprintf "%s %u %u" linearize i j

let out_table b =
   let map i (_, inverse) =
      let map i tl = Printf.sprintf "%2u" i :: tl in 
      let iset = String.concat " " (I.S.fold map inverse []) in
      Printf.eprintf "%2u|%s\n" i iset
   in
   Array.iteri map b;
   prerr_newline ()

(* dummy dependences ********************************************************)

let make l =
   let map _ = I.S.empty, false in
   List.rev_map map l

(* classification ***********************************************************)

let classify_conclusion vs = 
   let rec get_argsno = function
      | c, C.Appl (t :: vs) -> 
         let hd, argsno = get_argsno (c, t) in 
         hd, argsno + List.length vs
      | _, t                -> t, 0
   in
   let inside i = i > 1 && i <= List.length vs in
   match vs with
      | v0 :: v1 :: _ ->
         let hd0, a0 = get_argsno v0 in
	 let hd1, a1 = get_argsno v1 in
	 begin match hd0, hd1 with
	    | C.Rel i, C.MutInd (u, n, _) when inside i -> Some (i, a0, u, n)
	    | _                                         -> None
	 end
      | _             -> None
 
let classify c t =
try   
   let vs, h = PEH.split_with_whd (c, t) in
   let rc = classify_conclusion vs in
   let map (b, h) (c, v) = 
      let _, argsno = PEH.split_with_whd (c, v) in
      let isf = argsno > 0 (* || H.is_sort v *) in
      let iu = H.is_unsafe h (List.hd vs) in
      (I.get_rels_from_premise h v, I.S.empty, isf && iu) :: b, succ h
   in
   let l, h = List.fold_left map ([], 0) vs in
   let b = Array.of_list (List.rev l) in
   let mk_closure b h =
      let map j = if j < h then I.S.union (H.fst3 b.(j)) else H.identity in 
      for i = pred h downto 0 do
         let direct, unused, fa = b.(i) in
	 b.(i) <- I.S.fold map direct direct, unused, fa 
      done; b
   in
   let b = mk_closure b h in
   let rec mk_inverse i direct =
      if I.S.is_empty direct then () else
      let j = I.S.choose direct in
      if j < h then
         let unused, inverse, fa = b.(j) in 
         b.(j) <- unused, I.S.add i inverse, fa
       else ();
       mk_inverse i (I.S.remove j direct)
   in
   let map i (direct, _, _) = mk_inverse i direct in
   Array.iteri map b;
(*   out_table b; *)
   let extract (x, y, z) = y, z in
   List.rev_map extract (List.tl (Array.to_list b)), rc
with Invalid_argument _ -> failwith "Classify.classify"

(* adjusting the inferrable arguments that do not occur in the goal *********)

let adjust c vs ?goal classes = 
   let list_xmap2 map l1 l2 = 
      let rec aux a = function
         | hd1 :: tl1, hd2 :: tl2 -> aux (map hd1 hd2 :: a) (tl1,tl2)
	 | _, l2                  -> List.rev_append l2 a
      in
      List.rev (aux [] (l1, l2))
   in
   let map where what (i, b) = 
      let what = H.cic what in
      (i, b || not (H.occurs c ~what ~where))
   in
   match goal with
      | None      -> classes
      | Some goal -> list_xmap2 (map goal) vs classes
