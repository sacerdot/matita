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

include "basic_2/rt_transition/cnr_teqg.ma". (**) (* one dependence *)

(* NORMAL TERMS FOR CONTEXT-SENSITIVE R-TRANSITION **************************)

(* Properties with context-free sort-irrelevant equivalence for terms *******)

(* Basic_1: was: nf2_dec *)
(* Basic_2A1: uses: cnr_dec *)
lemma cnr_dec_teqx (h) (G) (L):
      ∀T1. ∨∨ ❪G,L❫ ⊢ ➡𝐍[h,0] T1
            | ∃∃T2. ❪G,L❫ ⊢ T1 ➡[h,0] T2 & (T1 ≅ T2 → ⊥).
/2 width=1 by cnr_dec_teqg/ qed-.
