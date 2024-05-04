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

include "basic_2/notation/relations/predsubty_6.ma".
include "static_2/s_transition/fquq.ma".
include "basic_2/rt_transition/rpx.ma".

(* PARALLEL RST-TRANSITION FOR CLOSURES *************************************)

(* Basic_2A1: uses: fpbq *)
definition fpb (G1) (L1) (T1) (G2) (L2) (T2): Prop ≝
           ∃∃L,T. ❨G1,L1,T1❩ ⬂⸮ ❨G2,L,T❩ & ❨G2,L❩ ⊢ T ⬈ T2 & ❨G2,L❩ ⊢ ⬈[T] L2.

interpretation
  "parallel rst-transition (closure)"
  'PRedSubTy G1 L1 T1 G2 L2 T2 = (fpb G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fpb_intro (G1) (L1) (T1) (G2) (L2) (T2):
      ∀L,T. ❨G1,L1,T1❩ ⬂⸮ ❨G2,L,T❩ → ❨G2,L❩ ⊢ T ⬈ T2 →
      ❨G2,L❩ ⊢ ⬈[T] L2 → ❨G1,L1,T1❩ ≽ ❨G2,L2,T2❩.
/2 width=5 by ex3_2_intro/ qed.

lemma rpx_fpb (G) (T):
      ∀L1,L2. ❨G,L1❩ ⊢ ⬈[T] L2 → ❨G,L1,T❩ ≽ ❨G,L2,T❩.
/2 width=5 by fpb_intro/ qed.

(* Basic inversion lemmas ***************************************************)

lemma fpb_inv_gen (G1) (L1) (T1) (G2) (L2) (T2):
      ❨G1,L1,T1❩ ≽ ❨G2,L2,T2❩ →
      ∃∃L,T. ❨G1,L1,T1❩ ⬂⸮ ❨G2,L,T❩ & ❨G2,L❩ ⊢ T ⬈ T2 & ❨G2,L❩ ⊢ ⬈[T] L2.
// qed-.

(* Basic_2A1: removed theorems 2:
              fpbq_fpbqa fpbqa_inv_fpbq
*)
