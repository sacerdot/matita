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

include "apps_2/notation/functional/dotteduparrow_2.ma".
include "apps_2/functional/flifts_basic.ma".
include "apps_2/functional/mf_v.ma".

(* MULTIPLE EVALUATION LIFT *************************************************)

definition mf_vlift (j) (gv): mf_evaluation ≝ λi. ↑[j,1](gv i).

interpretation "lift (multiple_filling)"
  'DottedUpArrow i gv = (mf_vlift i gv).

(* Basic properties *********************************************************)

lemma mf_vlift_rw (j) (gv): ∀i. (⇡[j]gv) i = ↑[j,1](gv i).
// qed.
