(* Copyright (C) 2002, HELM Team.
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


(* TODO se ce n'e' piu' di una, prende la prima che trova... sarebbe meglio
chiedere: find dovrebbe restituire una lista di hyp (?) da passare all'utonto con una
funzione di callback che restituisce la (sola) hyp da applicare *)

let assumption_tac =
 let module PET = ProofEngineTypes in
 let assumption_tac status =
  let (proof, goal) = status in
  let module C = Cic in
  let module R = CicReduction in
  let module S = CicSubstitution in
  let module PT = PrimitiveTactics in
  let _,metasenv,_,_,_, _ = proof in
  let _,context,ty = CicUtil.lookup_meta goal metasenv in
  let rec find n = function 
      hd::tl -> 
        (match hd with
             (Some (_, C.Decl t)) when
               fst (R.are_convertible context (S.lift n t) ty 
		       CicUniv.oblivion_ugraph) -> n
           | (Some (_, C.Def (_,ty'))) when
               fst (R.are_convertible context (S.lift n ty') ty
                       CicUniv.oblivion_ugraph) -> n
           | _ -> find (n+1) tl
         )
      | [] -> raise (PET.Fail (lazy "Assumption: No such assumption"))
     in PET.apply_tactic (PT.apply_tac ~term:(C.Rel (find 1 context))) status
 in
  PET.mk_tactic assumption_tac
;;
