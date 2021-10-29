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

include "basic_2/rt_transition/rpx_fqup.ma".
include "basic_2/rt_transition/fpb.ma".

(* PARALLEL RST-TRANSITION FOR CLOSURES *************************************)

(* Advanced properties ******************************************************)

(* Basic_2A1: was: fpbq_refl *)
lemma fpb_refl: tri_reflexive … fpb.
/2 width=5 by fpb_intro/ qed.

(* Basic_2A1: uses: fpbq_cpx *)
lemma cpx_fpb (G) (L):
      ∀T1,T2. ❨G,L❩ ⊢ T1 ⬈ T2 → ❨G,L,T1❩ ≽ ❨G,L,T2❩.
/2 width=5 by fpb_intro/ qed.

(* Basic_2A1: uses: fpbq_fquq *)
lemma fquq_fpb (G1) (G2) (L1) (L2) (T1) (T2):
      ❨G1,L1,T1❩ ⬂⸮ ❨G2,L2,T2❩ → ❨G1,L1,T1❩ ≽ ❨G2,L2,T2❩.
/2 width=5 by fpb_intro/ qed.

lemma fqu_fpb (G1) (G2) (L1) (L2) (T1) (T2):
      ❨G1,L1,T1❩ ⬂ ❨G2,L2,T2❩ → ❨G1,L1,T1❩ ≽ ❨G2,L2,T2❩.
/3 width=5 by fquq_fpb, fqu_fquq/ qed.
