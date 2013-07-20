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

include "basic_2/reduction/lpr.ma".
include "basic_2/reduction/cpx.ma".

(* SN EXTENDED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS ********************)

definition lpx: ∀h. sd h → relation lenv ≝ λh,g. lpx_sn (cpx h g). 

interpretation "extended parallel reduction (local environment, sn variant)"
   'PRedSn h g L1 L2 = (lpx h g L1 L2).

(* Basic inversion lemmas ***************************************************)

lemma lpx_inv_atom1: ∀h,g,L2. ⦃h, ⋆⦄ ⊢ ➡[g] L2 → L2 = ⋆.
/2 width=4 by lpx_sn_inv_atom1_aux/ qed-.

lemma lpx_inv_pair1: ∀h,g,I,K1,V1,L2. ⦃h, K1.ⓑ{I}V1⦄ ⊢ ➡[g] L2 →
                     ∃∃K2,V2. ⦃h, K1⦄ ⊢ ➡[g] K2 & ⦃h, K1⦄ ⊢ V1 ➡[g] V2 &
                             L2 = K2. ⓑ{I} V2.
/2 width=3 by lpx_sn_inv_pair1_aux/ qed-.

lemma lpx_inv_atom2: ∀h,g,L1.  ⦃h, L1⦄ ⊢ ➡[g] ⋆ → L1 = ⋆.
/2 width=4 by lpx_sn_inv_atom2_aux/ qed-.

lemma lpx_inv_pair2: ∀h,g,I,L1,K2,V2.  ⦃h, L1⦄ ⊢ ➡[g] K2.ⓑ{I}V2 →
                     ∃∃K1,V1. ⦃h, K1⦄ ⊢ ➡[g] K2 & ⦃h, K1⦄ ⊢ V1 ➡[g] V2 &
                             L1 = K1. ⓑ{I} V1.
/2 width=3 by lpx_sn_inv_pair2_aux/ qed-.

(* Basic properties *********************************************************)

lemma lpx_refl: ∀h,g,L.  ⦃h, L⦄ ⊢ ➡[g] L.
/2 width=1 by lpx_sn_refl/ qed.

lemma lpx_pair: ∀h,g,I,K1,K2,V1,V2. ⦃h, K1⦄ ⊢ ➡[g] K2 → ⦃h, K1⦄ ⊢ V1 ➡[g] V2 →
                ⦃h, K1.ⓑ{I}V1⦄ ⊢ ➡[g] K2.ⓑ{I}V2.
/2 width=1/ qed.

lemma lpx_append: ∀h,g,K1,K2. ⦃h, K1⦄ ⊢ ➡[g] K2 → ∀L1,L2. ⦃h, L1⦄ ⊢ ➡[g] L2 →
                  ⦃h, L1 @@ K1⦄ ⊢ ➡[g] L2 @@ K2.
/3 width=1 by lpx_sn_append, cpx_append/ qed.
(*
lamma lpr_lpx: ∀h,g,L1,L2. L1 ⊢ ➡ L2 → ⦃h, L1⦄ ⊢ ➡[g] L2.
#h #g #L1 #L2 #H elim H -L1 -L2 // /3 width=1/
qed.
*)
(* Basic forward lemmas *****************************************************)

lemma lpx_fwd_length: ∀h,g,L1,L2. ⦃h, L1⦄ ⊢ ➡[g] L2 → |L1| = |L2|.
/2 width=2 by lpx_sn_fwd_length/ qed-.

(* Advanced forward lemmas **************************************************)

lemma lpx_fwd_append1: ∀h,g,K1,L1,L. ⦃h, K1 @@ L1⦄ ⊢ ➡[g] L →
                       ∃∃K2,L2. ⦃h, K1⦄ ⊢ ➡[g] K2 & L = K2 @@ L2.
/2 width=2 by lpx_sn_fwd_append1/ qed-.

lemma lpx_fwd_append2: ∀h,g,L,K2,L2. ⦃h, L⦄ ⊢ ➡[g] K2 @@ L2 →
                       ∃∃K1,L1. ⦃h, K1⦄ ⊢ ➡[g] K2 & L = K1 @@ L1.
/2 width=2 by lpx_sn_fwd_append2/ qed-.
