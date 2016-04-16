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

include "basic_2/notation/relations/predsn_5.ma".
include "basic_2/reduction/lpr.ma".
include "basic_2/reduction/cpx.ma".

(* SN EXTENDED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS ********************)

definition lpx: ∀h. sd h → relation3 genv lenv lenv ≝
                λh,o,G. lpx_sn (cpx h o G).

interpretation "extended parallel reduction (local environment, sn variant)"
   'PRedSn h o G L1 L2 = (lpx h o G L1 L2).

(* Basic inversion lemmas ***************************************************)

lemma lpx_inv_atom1: ∀h,o,G,L2. ⦃G, ⋆⦄ ⊢ ➡[h, o] L2 → L2 = ⋆.
/2 width=4 by lpx_sn_inv_atom1_aux/ qed-.

lemma lpx_inv_pair1: ∀h,o,I,G,K1,V1,L2. ⦃G, K1.ⓑ{I}V1⦄ ⊢ ➡[h, o] L2 →
                     ∃∃K2,V2. ⦃G, K1⦄ ⊢ ➡[h, o] K2 & ⦃G, K1⦄ ⊢ V1 ➡[h, o] V2 &
                              L2 = K2. ⓑ{I} V2.
/2 width=3 by lpx_sn_inv_pair1_aux/ qed-.

lemma lpx_inv_atom2: ∀h,o,G,L1.  ⦃G, L1⦄ ⊢ ➡[h, o] ⋆ → L1 = ⋆.
/2 width=4 by lpx_sn_inv_atom2_aux/ qed-.

lemma lpx_inv_pair2: ∀h,o,I,G,L1,K2,V2.  ⦃G, L1⦄ ⊢ ➡[h, o] K2.ⓑ{I}V2 →
                     ∃∃K1,V1. ⦃G, K1⦄ ⊢ ➡[h, o] K2 & ⦃G, K1⦄ ⊢ V1 ➡[h, o] V2 &
                             L1 = K1. ⓑ{I} V1.
/2 width=3 by lpx_sn_inv_pair2_aux/ qed-.

lemma lpx_inv_pair: ∀h,o,I1,I2,G,L1,L2,V1,V2.  ⦃G, L1.ⓑ{I1}V1⦄ ⊢ ➡[h, o] L2.ⓑ{I2}V2 →
                    ∧∧ ⦃G, L1⦄ ⊢ ➡[h, o] L2 & ⦃G, L1⦄ ⊢ V1 ➡[h, o] V2 & I1 = I2.
/2 width=1 by lpx_sn_inv_pair/ qed-.

(* Basic properties *********************************************************)

lemma lpx_refl: ∀h,o,G,L.  ⦃G, L⦄ ⊢ ➡[h, o] L.
/2 width=1 by lpx_sn_refl/ qed.

lemma lpx_pair: ∀h,o,I,G,K1,K2,V1,V2. ⦃G, K1⦄ ⊢ ➡[h, o] K2 → ⦃G, K1⦄ ⊢ V1 ➡[h, o] V2 →
                ⦃G, K1.ⓑ{I}V1⦄ ⊢ ➡[h, o] K2.ⓑ{I}V2.
/2 width=1 by lpx_sn_pair/ qed.

lemma lpr_lpx: ∀h,o,G,L1,L2. ⦃G, L1⦄ ⊢ ➡ L2 → ⦃G, L1⦄ ⊢ ➡[h, o] L2.
#h #o #G #L1 #L2 #H elim H -L1 -L2 /3 width=1 by lpx_pair, cpr_cpx/
qed.

(* Basic forward lemmas *****************************************************)

lemma lpx_fwd_length: ∀h,o,G,L1,L2. ⦃G, L1⦄ ⊢ ➡[h, o] L2 → |L1| = |L2|.
/2 width=2 by lpx_sn_fwd_length/ qed-.
