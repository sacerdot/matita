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

include "apps_2/notation/functional/dotteduparrow_3.ma".
include "apps_2/functional/flifts_basic.ma".
include "apps_2/functional/mf_v.ma".

(* MULTIPLE FILLING PUSH ****************************************************)

definition mf_vpush (j) (T) (lv): mf_evaluation ≝
                    λi. tri … i j (lv i) T (↑[j,1](lv (↓i))).

interpretation "push (multiple filling)"
  'DottedUpArrow i d lv = (mf_vpush i d lv).

(* Basic properties *********************************************************)

lemma mf_vpush_lt (lv) (j) (T): ∀i. i < j → (⇡[j←T]lv) i = lv i.
/2 width=1 by tri_lt/ qed-.

lemma mf_vpush_eq: ∀lv,T,i. (⇡[i←T]lv) i = T.
/2 width=1 by tri_eq/ qed.

lemma mf_vpush_gt: ∀lv,T,j,i. j < i → (⇡[j←T]lv) i = ↑[j,1](lv (↓i)).
/2 width=1 by tri_gt/ qed-.
