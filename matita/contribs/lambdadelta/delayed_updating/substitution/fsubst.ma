(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "ground/xoa/ex_3_1.ma".
include "delayed_updating/syntax/preterm.ma".
include "delayed_updating/notation/functions/pitchforkleftarrow_3.ma".

(* FOCALIZED SUBSTITUTION ***************************************************)

definition fsubst (p) (u): preterm → preterm ≝
           λt,q.
           ∨∨ ∃∃r. r ϵ u & p ϵ ▵t & p;;r = q
            | ∧∧ q ϵ t & (∀r. p;;r = q → ⊥) 
.

interpretation
  "focalized substitution (preterm)"
  'PitchforkLeftArrow t p u = (fsubst p u t).
