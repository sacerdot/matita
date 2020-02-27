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

include "basic_2/notation/relations/lazypredsn_7.ma".
include "basic_2/relocation/llpx_sn.ma".
include "basic_2/reduction/cpx.ma".

(* LAZY SN EXTENDED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS ***************)

definition llpx: ∀h. sd h → genv → relation4 ynat term lenv lenv ≝
                 λh,g,G. llpx_sn (cpx h g  G).

interpretation "lazy extended parallel reduction (local environment, sn variant)"
   'LazyPRedSn G L1 L2 h g T d = (llpx h g G d T L1 L2).

(* Basic inversion lemmas ***************************************************)

lemma llpx_inv_flat: ∀h,g,I,G,L1,L2,V,T,d. ⦃G, L1⦄ ⊢ ➡[h, g, ⓕ{I}V.T, d] L2 →
                     ⦃G, L1⦄ ⊢ ➡[h, g, V, d] L2 ∧ ⦃G, L1⦄ ⊢ ➡[h, g, T, d] L2.
/2 width=2 by llpx_sn_inv_flat/ qed-.

(* Basic forward lemmas *****************************************************)

lemma llpx_fwd_length: ∀h,g,G,L1,L2,T,d. ⦃G, L1⦄ ⊢ ➡[h, g, T, d] L2 → |L1| = |L2|.
/2 width=4 by llpx_sn_fwd_length/ qed-.

lemma llpx_fwd_flat_dx: ∀h,g,I,G,L1,L2,V,T,d. ⦃G, L1⦄ ⊢ ➡[h, g, ⓕ{I}V.T, d] L2 →
                     ⦃G, L1⦄ ⊢ ➡[h, g, T, d] L2.
/2 width=3 by llpx_sn_fwd_flat_dx/ qed-.

lemma llpx_fwd_pair_sn: ∀h,g,I,G,L1,L2,V,T,d. ⦃G, L1⦄ ⊢ ➡[h, g, ②{I}V.T, d] L2 →
                        ⦃G, L1⦄ ⊢ ➡[h, g, V, d] L2.
/2 width=3 by llpx_sn_fwd_pair_sn/ qed-.

(* Note: this might be removed *)
lemma llpx_fwd_bind_sn: ∀h,g,a,I,G,L1,L2,V,T,d. ⦃G, L1⦄ ⊢ ➡[h, g, ⓑ{a,I}V.T, d] L2 →
                        ⦃G, L1⦄ ⊢ ➡[h, g, V, d] L2.
/2 width=4 by llpx_sn_fwd_bind_sn/ qed-.

(* Note: this might be removed *)
lemma llpx_fwd_bind_dx: ∀h,g,a,I,G,L1,L2,V,T,d. ⦃G, L1⦄ ⊢ ➡[h, g, ⓑ{a,I}V.T, d] L2 →
                        ⦃G, L1.ⓑ{I}V⦄ ⊢ ➡[h, g, T, ⫯d] L2.ⓑ{I}V.
/2 width=2 by llpx_sn_fwd_bind_dx/ qed-.

(* Note: this might be removed *)
lemma llpx_fwd_flat_sn: ∀h,g,I,G,L1,L2,V,T,d. ⦃G, L1⦄ ⊢ ➡[h, g, ⓕ{I}V.T, d] L2 →
                        ⦃G, L1⦄ ⊢ ➡[h, g, V, d] L2.
/2 width=3 by llpx_sn_fwd_flat_sn/ qed-.

(* Basic properties *********************************************************)

lemma llpx_lref: ∀h,g,I,G,L1,L2,K1,K2,V1,V2,d,i. d ≤ yinj i →
                 ⇩[i] L1 ≡ K1.ⓑ{I}V1 → ⇩[i] L2 ≡ K2.ⓑ{I}V2 →
                 ⦃G, K1⦄ ⊢ ➡[h, g, V1, 0] K2 → ⦃G, K1⦄ ⊢ V1 ➡[h, g] V2 → ⦃G, L1⦄ ⊢ ➡[h, g, #i, d] L2.
/2 width=9 by llpx_sn_lref/ qed.

lemma llpx_refl: ∀h,g,G,T,d. reflexive … (llpx h g G d T).
/2 width=1 by llpx_sn_refl/ qed.
