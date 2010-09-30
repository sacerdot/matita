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

module UM   = UriManager
module C    = Cic
module Pp   = CicPp
module I    = CicInspect
module E    = CicEnvironment
module S    = CicSubstitution
module DTI  = DoubleTypeInference
module HEL  = HExtlib
module PEH  = ProofEngineHelpers
module TC   = CicTypeChecker 
module Un   = CicUniv
module L    = Librarian
module Ut   = CicUtil

module H    = ProceduralHelpers
module Cl   = ProceduralClassify

(* debugging ****************************************************************)

let debug = ref false

(* term optimization ********************************************************)

let critical = ref true

type status = {
   dummy: unit;
   info: string
}

let info st str = {st with info = st.info ^ str ^ "\n"}

let defined_premise = "LOCAL"

let define c v =
   let name = C.Name defined_premise in
   let ty = H.get_type "define" c v in
   C.LetIn (name, v, ty, C.Rel 1)

let clear_absts m =
   let rec aux k n = function
      | C.Lambda (s, v, t) when k > 0 -> 
         C.Lambda (s, v, aux (pred k) n t)
      | C.Lambda (_, _, t) when n > 0 -> 
         aux 0 (pred n) (S.lift (-1) t)
      | t                  when n > 0 ->
         Printf.eprintf "PO.clear_absts: %u %s\n" n (Pp.ppterm t);
         assert false
      | t                             -> t
   in 
   aux m

let rec add_abst k = function 
   | C.Lambda (s, v, t) when k > 0 -> C.Lambda (s, v, add_abst (pred k) t)
   | t when k > 0 -> assert false
   | t -> C.Lambda (C.Anonymous, C.Implicit None, S.lift 1 t)

let rec opt_letin g st es c name v w t =
   let name = H.mk_fresh_name true c name in
   let entry = Some (name, C.Def (v, w)) in
   let g st t =
      if DTI.does_not_occur 1 t then
         let x = S.lift (-1) t in
	 opt_proof g (info st "Optimizer: remove 1") true c x
      else 
      let g st = function
         | C.LetIn (nname, vv, ww, tt) when H.is_proof c v ->
	    let eentry = Some (nname, C.Def (vv, ww)) in
	    let ttw = H.get_type "opt_letin 1" (eentry :: c) tt in
	    let x = C.LetIn (nname, vv, ww,
             C.LetIn (name, tt, ttw, S.lift_from 2 1 t))
	    in
	    opt_proof g (info st "Optimizer: swap 1") true c x
         | v when H.is_proof c v && H.is_atomic v          ->
	    let x = S.subst v t in
	    opt_proof g (info st "Optimizer: remove 5") true c x 
(*	 | v when t = C.Rel 1                              ->
	    g (info st "Optimizer: remove 6") v 
*)	 | v                                               ->
	    g st (C.LetIn (name, v, w, t))
      in
      if es then opt_term g st es c v else g st v
   in
   if es then opt_proof g st es (entry :: c) t else g st t

and opt_lambda g st es c name w t =
   let name = H.mk_fresh_name true c name in
   let entry = Some (name, C.Decl w) in
   let g st t = g st (C.Lambda (name, w, t)) in
   if es then opt_proof g st es (entry :: c) t else g st t

and opt_appl g st es c t vs =
   let g (st, vs) =
      let g st = function      
         | C.LetIn (mame, vv, tyty, tt) ->
            let vs = List.map (S.lift 1) vs in
	    let x = C.LetIn (mame, vv, tyty, C.Appl (tt :: vs)) in
	    opt_proof g (info st "Optimizer: swap 2") true c x
         | C.Lambda (name, ww, tt) ->
	    let v, vs = List.hd vs, List.tl vs in
            let w = H.get_type "opt_appl 1" c v in
	    let x = C.Appl (C.LetIn (name, v, w, tt) :: vs) in
	    opt_proof g (info st "Optimizer: remove 2") true c x
	 | C.Appl vvs              ->
            let x = C.Appl (vvs @ vs) in
	    opt_proof g (info st "Optimizer: nested application") true c x
	 | t                       ->
(*	    
            let rec aux st d rvs = function
	       | [], _                   -> 
	          let x = C.Appl (t :: List.rev rvs) in
		  if d then opt_proof g st true c x else g st x
	       | v :: vs, (cc, bb) :: cs ->
	          if H.is_not_atomic v && I.S.mem 0 cc && bb then 
                     aux (st info "Optimizer: anticipate 1") true
		      (define c v :: rvs) (vs, cs)
		  else 
		     aux st d (v :: rvs) (vs, cs)
	       | _, []                   -> assert false
	    in
*)
	    let h st =
	       let classes, conclusion = Cl.classify c (H.get_type "opt_appl 3" c t) in
	       let csno, vsno = List.length classes, List.length vs in
	       if csno < vsno then
	          let vvs, vs = HEL.split_nth csno vs in
		  let x = C.Appl (define c (C.Appl (t :: vvs)) :: vs) in
		  opt_proof g (info st "Optimizer: anticipate 2") true c x
	       else match conclusion, List.rev vs with
	          | Some _, rv :: rvs when csno = vsno && H.is_not_atomic rv ->
		     let x = C.Appl (t :: List.rev rvs @ [define c rv]) in
		     opt_proof g (info st "Optimizer: anticipate 3";) true c x
	          | _ (* Some _, _ *)                                             ->
		     g st (C.Appl (t :: vs))
(*		  | None, _                                                ->
	             aux false [] (vs, classes)
*)	    in
	    let rec aux h st prev = function
	       | C.LetIn (name, vv, tyty, tt) :: vs ->
	          let t = S.lift 1 t in
                  let prev = List.map (S.lift 1) prev in
                  let vs = List.map (S.lift 1) vs in
		  let y = C.Appl (t :: List.rev prev @ tt :: vs) in
                  let ww = H.get_type "opt_appl 2" c vv in
		  let x = C.LetIn (name, vv, ww, y) in  
		  opt_proof g (info st "Optimizer: swap 3") true c x
	       | v :: vs                      -> aux h st (v :: prev) vs
	       | []                           -> h st
	    in 
	    aux h st [] vs
      in
      if es then opt_proof g st es c t else g st t
   in
   let map h v (st, vs) =
      let h st vv = h (st, vv :: vs) in opt_term h st es c v
   in
   if es then H.list_fold_right_cps g map vs (st, []) else g (st, vs)

and opt_mutcase_critical g st es c uri tyno outty arg cases =   
   let eliminator = H.get_default_eliminator c uri tyno outty in
   let lpsno, (_, _, _, constructors) = H.get_ind_type uri tyno in
   let ps, sort_disp = H.get_ind_parameters c arg in
   let lps, rps = HEL.split_nth lpsno ps in
   let rpsno = List.length rps in
   if rpsno = 0 && sort_disp = 0 then
(* FG: the transformation is not possible, we fall back into the plain case *)
      opt_mutcase_plain g st es c uri tyno outty arg cases
   else
   let predicate = clear_absts rpsno (1 - sort_disp) outty in   
   if H.occurs c ~what:(C.Rel 0) ~where:predicate then
(* FG: the transformation is not possible, we fall back into the plain case *)
      opt_mutcase_plain g st es c uri tyno outty arg cases
   else
   let is_recursive t =
      I.S.mem tyno (I.get_mutinds_of_uri uri t) 
   in
   let map2 case (_, cty) = 
      let map (h, case, k) (_, premise) = 
         if h > 0 then pred h, case, k else
	 if is_recursive premise then 
	    0, add_abst k case, k + 2 
	 else
	    0, case, succ k
      in
      let premises, _ = PEH.split_with_whd (c, cty) in
      let _, lifted_case, _ =
         List.fold_left map (lpsno, case, 1) (List.rev (List.tl premises))
      in
      lifted_case
   in
   let lifted_cases = List.map2 map2 cases constructors in
   let args = eliminator :: lps @ predicate :: lifted_cases @ rps @ [arg] in
   try 
      let x = H.refine c (C.Appl args) in
      opt_proof g (info st "Optimizer: remove 3") es c x	 
   with e ->
(* FG: the transformation is not possible, we fall back into the plain case *)
      let st = info st ("Optimizer: refine_error: " ^ Printexc.to_string e) in
      opt_mutcase_plain g st es c uri tyno outty arg cases

and opt_mutcase_plain g st es c uri tyno outty arg cases =
   let g st v =
      let g (st, ts) = g st (C.MutCase (uri, tyno, outty, v, ts)) in
      let map h v (st, vs) =
         let h st vv = h (st, vv :: vs) in opt_proof h st es c v
      in
      if es then H.list_fold_right_cps g map cases (st, []) else g (st, cases)
   in
   if es then opt_proof g st es c arg else g st arg

and opt_mutcase g =
   if !critical then opt_mutcase_critical g else opt_mutcase_plain g 

and opt_cast g st es c t w =
   let g st t = g (info st "Optimizer: remove 4") t in
   if es then opt_proof g st es c t else g st t

and opt_other g st es c t = g st t 

and opt_proof g st es c = function 
   | C.LetIn (name, v, ty, t)   -> opt_letin g st es c name v ty t
   | C.Lambda (name, w, t)      -> opt_lambda g st es c name w t
   | C.Appl (t :: v :: vs)      -> opt_appl g st es c t (v :: vs)
   | C.Appl [t]                 -> opt_proof g st es c t
   | C.MutCase (u, n, t, v, ws) -> opt_mutcase g st es c u n t v ws
   | C.Cast (t, w)              -> opt_cast g st es c t w
   | t                          -> opt_other g st es c t

and opt_term g st es c t = 
   if H.is_proof c t then opt_proof g st es c t else g st t

(* object optimization ******************************************************)

let wrap g st c bo =
   try opt_term g st true c bo
   with
      | E.Object_not_found uri ->
         let msg = "optimize_obj: object not found: " ^ UM.string_of_uri uri in
	 failwith msg 
      | e                      -> 
	 let msg = "optimize_obj: " ^ Printexc.to_string e in
	 failwith msg

let optimize_obj = function
   | C.Constant (name, Some bo, ty, pars, attrs) ->
      let count_nodes = I.count_nodes ~meta:false 0 in 
      let st, c = {info = ""; dummy = ()}, [] in
      L.time_stamp ("PO: OPTIMIZING " ^ name);
      let nodes = Printf.sprintf "Initial nodes: %u" (count_nodes bo) in
      if !debug then begin 
         Printf.eprintf "BEGIN: %s\n" name;      
         Printf.eprintf "Initial : %s\n" (Pp.ppterm bo); 
	 prerr_string "Ut.pp_term : ";
	 Ut.pp_term prerr_string [] c bo; prerr_newline ()
      end;
      let bo, ty = H.cic_bc c bo, H.cic_bc c ty in 
      let g st bo =
	 if !debug then begin 
	    Printf.eprintf "Optimized : %s\n" (Pp.ppterm bo); 
	    prerr_string "Ut.pp_term : ";
	    Ut.pp_term prerr_string [] c bo; prerr_newline ()
	 end;
(*	 let _ = H.get_type "opt" [] (C.Cast (bo, ty)) in *)
         let nodes = Printf.sprintf "Optimized nodes: %u" (count_nodes bo) in
	 let st = info st nodes in
	 L.time_stamp ("PO: DONE       " ^ name);
	 C.Constant (name, Some bo, ty, pars, attrs), st.info
      in
      wrap g (info st nodes) c bo
   | obj                                         -> obj, ""

let optimize_term c bo =
   let st = {info = ""; dummy = ()} in
   let bo = H.cic_bc c bo in
   let g st bo = bo, st.info in
   wrap g st c bo
