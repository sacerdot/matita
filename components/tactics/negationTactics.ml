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

let absurd_tac ~term =
 let absurd_tac ~term status =
  let (proof, goal) = status in
  let module C = Cic in
  let module U = UriManager in
  let module P = PrimitiveTactics in
  let _,metasenv,_subst,_,_, _ = proof in
  let _,context,ty = CicUtil.lookup_meta goal metasenv in
  let absurd_URI =
   match LibraryObjects.absurd_URI () with
      Some uri -> uri
    | None -> raise (ProofEngineTypes.Fail (lazy "You need to register the default \"absurd\" theorem first. Please use the \"default\" command"))
  in
  let ty_term,_ = 
    CicTypeChecker.type_of_aux' metasenv context term CicUniv.oblivion_ugraph in
    if (ty_term = (C.Sort C.Prop)) (* ma questo controllo serve?? *)
    then ProofEngineTypes.apply_tactic 
      (P.apply_tac 
         ~term:(
           C.Appl [(C.Const (absurd_URI, [] )) ; 
	           term ; ty])
      ) 
      status
    else raise (ProofEngineTypes.Fail (lazy "Absurd: Not a Proposition"))
 in
   ProofEngineTypes.mk_tactic (absurd_tac ~term)
;;

(* FG: METTERE I NOMI ANCHE QUI? CSC: in teoria si', per la intros*)
let contradiction_tac =
 let contradiction_tac status =
  let module C = Cic in
  let module U = UriManager in
  let module P = PrimitiveTactics in
  let module T = Tacticals in
  let false_URI =
   match LibraryObjects.false_URI () with
      Some uri -> uri
    | None -> raise (ProofEngineTypes.Fail (lazy "You need to register the default \"false\" definition first. Please use the \"default\" command"))
  in
   try
    ProofEngineTypes.apply_tactic (
     T.then_
      ~start:(P.intros_tac ())
      ~continuation:(
	 T.then_
           ~start:
             (EliminationTactics.elim_type_tac (C.MutInd (false_URI, 0, [])))
           ~continuation: VariousTactics.assumption_tac))
    status
   with 
    ProofEngineTypes.Fail msg when Lazy.force msg = "Assumption: No such assumption" -> raise (ProofEngineTypes.Fail (lazy "Contradiction: No such assumption"))
    (* sarebbe piu' elegante se Assumtion sollevasse un'eccezione tutta sua che questa cattura, magari con l'aiuto di try_tactics *)
 in 
  ProofEngineTypes.mk_tactic contradiction_tac
;;

(* Questa era in fourierR.ml
(* !!!!! fix !!!!!!!!!! *)
let contradiction_tac (proof,goal)=
        Tacticals.then_
                ~start:(PrimitiveTactics.intros_tac ~name:"bo?" ) (*inutile sia questo che quello prima  della chiamata*)
                ~continuation:(Tacticals.then_
                        ~start:(VariousTactics.elim_type_tac ~term:_False)
                        ~continuation:(assumption_tac))
        (proof,goal)
;;
*)


