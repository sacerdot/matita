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
                λh,g,G. lpx_sn (cpx h g G).

interpretation "extended parallel reduction (local environment, sn variant)"
   'PRedSn h g G L1 L2 = (lpx h g G L1 L2).

(* Basic inversion lemmas ***************************************************)

lemma lpx_inv_atom1: ∀h,g,G,L2. ⦃G, ⋆⦄ ⊢ ➡[h, g] L2 → L2 = ⋆.
/2 width=4 by lpx_sn_inv_atom1_aux/ qed-.

lemma lpx_inv_pair1: ∀h,g,I,G,K1,V1,L2. ⦃G, K1.ⓑ{I}V1⦄ ⊢ ➡[h, g] L2 →
                     ∃∃K2,V2. ⦃G, K1⦄ ⊢ ➡[h, g] K2 & ⦃G, K1⦄ ⊢ V1 ➡[h, g] V2 &
                              L2 = K2. ⓑ{I} V2.
/2 width=3 by lpx_sn_inv_pair1_aux/ qed-.

lemma lpx_inv_atom2: ∀h,g,G,L1.  ⦃G, L1⦄ ⊢ ➡[h, g] ⋆ → L1 = ⋆.
/2 width=4 by lpx_sn_inv_atom2_aux/ qed-.

lemma lpx_inv_pair2: ∀h,g,I,G,L1,K2,V2.  ⦃G, L1⦄ ⊢ ➡[h, g] K2.ⓑ{I}V2 →
                     ∃∃K1,V1. ⦃G, K1⦄ ⊢ ➡[h, g] K2 & ⦃G, K1⦄ ⊢ V1 ➡[h, g] V2 &
                             L1 = K1. ⓑ{I} V1.
/2 width=3 by lpx_sn_inv_pair2_aux/ qed-.

(* Basic properties *********************************************************)

lemma lpx_refl: ∀h,g,G,L.  ⦃G, L⦄ ⊢ ➡[h, g] L.
/2 width=1 by lpx_sn_refl/ qed.

lemma lpx_pair: ∀h,g,I,G,K1,K2,V1,V2. ⦃G, K1⦄ ⊢ ➡[h, g] K2 → ⦃G, K1⦄ ⊢ V1 ➡[h, g] V2 →
                ⦃G, K1.ⓑ{I}V1⦄ ⊢ ➡[h, g] K2.ⓑ{I}V2.
/2 width=1/ qed.

lemma lpx_append: ∀h,g,G,K1,K2. ⦃G, K1⦄ ⊢ ➡[h, g] K2 → ∀L1,L2. ⦃G, L1⦄ ⊢ ➡[h, g] L2 →
                  ⦃G, L1 @@ K1⦄ ⊢ ➡[h, g] L2 @@ K2.
/3 width=1 by lpx_sn_append, cpx_append/ qed.

lemma lpr_lpx: ∀h,g,G,L1,L2. ⦃G, L1⦄ ⊢ ➡ L2 → ⦃G, L1⦄ ⊢ ➡[h, g] L2.
#h #g #G #L1 #L2 #H elim H -L1 -L2 // /3 width=1/
qed.

(* Basic forward lemmas *****************************************************)

lemma lpx_fwd_length: ∀h,g,G,L1,L2. ⦃G, L1⦄ ⊢ ➡[h, g] L2 → |L1| = |L2|.
/2 width=2 by lpx_sn_fwd_length/ qed-.

(* Advanced forward lemmas **************************************************)

lemma lpx_fwd_append1: ∀h,g,G,K1,L1,L. ⦃G, K1 @@ L1⦄ ⊢ ➡[h, g] L →
                       ∃∃K2,L2. ⦃G, K1⦄ ⊢ ➡[h, g] K2 & L = K2 @@ L2.
/2 width=2 by lpx_sn_fwd_append1/ qed-.

lemma lpx_fwd_append2: ∀h,g,G,L,K2,L2. ⦃G, L⦄ ⊢ ➡[h, g] K2 @@ L2 →
                       ∃∃K1,L1. ⦃G, K1⦄ ⊢ ➡[h, g] K2 & L = K1 @@ L1.
/2 width=2 by lpx_sn_fwd_append2/ qed-.
