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

include "basic_2/notation/relations/lazypredsn_5.ma".
include "basic_2/relocation/llpx_sn.ma".
include "basic_2/reduction/cpr.ma".

(* LAZY SN PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS ************************)

definition llpr: genv → relation4 ynat term lenv lenv ≝ λG. llpx_sn (cpr G).

interpretation "lazy parallel reduction (local environment, sn variant)"
   'LazyPRedSn G L1 L2 T d = (llpr G d T L1 L2).

(* Basic inversion lemmas ***************************************************)

lemma llpr_inv_flat: ∀I,G,L1,L2,V,T,d. ⦃G, L1⦄ ⊢ ➡[ⓕ{I}V.T, d] L2 →
                     ⦃G, L1⦄ ⊢ ➡[V, d] L2 ∧ ⦃G, L1⦄ ⊢ ➡[T, d] L2.
/2 width=2 by llpx_sn_inv_flat/ qed-.

(* Basic forward lemmas *****************************************************)

lemma llpr_fwd_length: ∀G,L1,L2,T,d. ⦃G, L1⦄ ⊢ ➡[T, d] L2 → |L1| = |L2|.
/2 width=4 by llpx_sn_fwd_length/ qed-.

(* Basic properties *********************************************************)

lemma llpr_lref: ∀I,G,L1,L2,K1,K2,V1,V2,d,i. d ≤ yinj i →
                 ⇩[i] L1 ≡ K1.ⓑ{I}V1 → ⇩[i] L2 ≡ K2.ⓑ{I}V2 →
                 ⦃G, K1⦄ ⊢ ➡[V1, 0] K2 → ⦃G, K1⦄ ⊢ V1 ➡ V2 → ⦃G, L1⦄ ⊢ ➡[#i, d] L2.
/2 width=9 by llpx_sn_lref/ qed.

(* Note: lemma 250 *)
lemma llpr_refl: ∀G,T,d. reflexive … (llpr G d T).
/2 width=1 by llpx_sn_refl/ qed.

(* Basic_1: removed theorems 5: wcpr0_gen_sort wcpr0_gen_head
                                wcpr0_getl wcpr0_getl_back
                                pr0_subst1_back
*)
