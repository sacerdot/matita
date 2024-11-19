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

include "explicit_updating/syntax/term_valid.ma".
include "explicit_updating/reduction/xstep.ma".
include "explicit_updating/reduction/xbeta1.ma".
include "explicit_updating/notation/relations/black_rightarrow_2.ma".

(* X-REDUCTION TO ♭-NORMAL FORM *********************************************)

definition xstep_phi: relation2 … ≝
           λt1,t2. ∧∧ t1 ➡[𝛃ⓣ] t2 & ⓕ ⊢ t2.

interpretation
  "x-reduction to ♭-normal form (term)"
  'BlackRightArrow t1 t2 = (xstep_phi t1 t2).

(* Basic constructions ******************************************************)

lemma xstep_phi_fold (t1) (t2):
      t1 ➡[𝛃ⓣ] t2 → ⓕ ⊢ t2 → t1 ➡𝛟 t2.
/2 width=1 by conj/
qed.

(* Advanced constructions ***************************************************)

lemma xstep_phi_abst (t1) (t2):
      t1 ➡𝛟 t2 → 𝛌𝗽.t1 ➡𝛟 𝛌𝗽.t2.
#t1 #t2 * #Ht12 #Ht2
/3 width=1 by xstep_phi_fold, term_valid_abst, xstep_abst/
qed.

lemma xstep_phi_side (v1) (v2) (t1) (t2):
      v1 ➡𝛟 v2 → t1 ≐ t2 → ⓕ ⊢ t2 → ＠v1.t1 ➡𝛟 ＠v2.t2.
#v1 #v2 #t1 #t2 * #Hf12 #Hv2 #Ht12 #Ht2 
/3 width=1 by xstep_phi_fold, term_valid_appl, xstep_side/
qed.

lemma xstep_phi_head (v1) (v2) (t1) (t2):
      v1 ≐ v2 → ⓕ ⊢ v2 → t1 ➡𝛟 t2 → ＠v1.t1 ➡𝛟 ＠v2.t2.
#v1 #v2 #t1 #t2 #Hf12 #Hv2 * #Ht12 #Ht2
/3 width=1 by xstep_phi_fold, term_valid_appl, xstep_head/
qed.

lemma xstep_phi_lift (f1) (f2) (t1) (t2):
      f1 ≐ f2 → t1 ➡𝛟 t2 → 𝛗f1.t1 ➡𝛟 𝛗f2.t2.
#f1 #f2 #t1 #t2 #Hf12 * #Ht12 #Ht2
/3 width=1 by xstep_phi_fold, term_valid_lift, xstep_lift/
qed.
