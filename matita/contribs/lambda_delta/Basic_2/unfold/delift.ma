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

include "Basic_2/unfold/tpss.ma".

(* DELIFT ON TERMS **********************************************************)

definition delift: nat → nat → lenv → relation term ≝
                   λd,e,L,T1,T2. ∃∃T. L ⊢ T1 [d, e] ≫* T & ↑[d, e] T2 ≡ T.

interpretation "delift (term)"
   'TSubst L T1 d e T2 = (delift d e L T1 T2).

(* Basic properties *********************************************************)

lemma delift_lsubs_conf: ∀L1,T1,T2,d,e. L1 ⊢ T1 [d, e] ≡ T2 →
                         ∀L2. L1 [d, e] ≼ L2 → L2 ⊢ T1 [d, e] ≡ T2.
#L1 #T1 #T2 #d #e * /3 width=3/
qed.

lemma delift_bind: ∀I,L,V1,V2,T1,T2,d,e.
                   L ⊢ V1 [d, e] ≡ V2 → L. 𝕓{I} V2 ⊢ T1 [d+1, e] ≡ T2 →
                   L ⊢ 𝕓{I} V1. T1 [d, e] ≡ 𝕓{I} V2. T2.
#I #L #V1 #V2 #T1 #T2 #d #e * #V #HV1 #HV2 * #T #HT1 #HT2
lapply (tpss_lsubs_conf … HT1 (L. 𝕓{I} V) ?) -HT1 /2 width=1/ /3 width=5/
qed.

lemma delift_flat: ∀I,L,V1,V2,T1,T2,d,e.
                   L ⊢ V1 [d, e] ≡ V2 → L ⊢ T1 [d, e] ≡ T2 →
                   L ⊢ 𝕗{I} V1. T1 [d, e] ≡ 𝕗{I} V2. T2.
#I #L #V1 #V2 #T1 #T2 #d #e * #V #HV1 #HV2 * /3 width=5/
qed.

(* Basic forward lemmas *****************************************************)

lemma delift_fwd_sort1: ∀L,U2,d,e,k. L ⊢ ⋆k [d, e] ≡ U2 → U2 = ⋆k.
#L #U2 #d #e #k * #U #HU
>(tpss_inv_sort1 … HU) -HU #HU2
>(lift_inv_sort2 … HU2) -HU2 //
qed-.

lemma delift_fwd_gref1: ∀L,U2,d,e,p. L ⊢ §p [d, e] ≡ U2 → U2 = §p.
#L #U #d #e #p * #U #HU
>(tpss_inv_gref1 … HU) -HU #HU2
>(lift_inv_gref2 … HU2) -HU2 //
qed-.

lemma delift_fwd_bind1: ∀I,L,V1,T1,U2,d,e. L ⊢ 𝕓{I} V1. T1 [d, e] ≡ U2 →
                        ∃∃V2,T2. L ⊢ V1 [d, e] ≡ V2 &
                                 L. 𝕓{I} V2 ⊢ T1 [d+1, e] ≡ T2 &
                                 U2 = 𝕓{I} V2. T2.
#I #L #V1 #T1 #U2 #d #e * #U #HU #HU2
elim (tpss_inv_bind1 … HU) -HU #V #T #HV1 #HT1 #X destruct
elim (lift_inv_bind2 … HU2) -HU2 #V2 #T2 #HV2 #HT2
lapply (tpss_lsubs_conf … HT1 (L. 𝕓{I} V2) ?) -HT1 /2 width=1/ /3 width=5/
qed-.

lemma delift_fwd_flat1: ∀I,L,V1,T1,U2,d,e. L ⊢ 𝕗{I} V1. T1 [d, e] ≡ U2 →
                        ∃∃V2,T2. L ⊢ V1 [d, e] ≡ V2 &
                                 L ⊢ T1 [d, e] ≡ T2 &
                                 U2 = 𝕗{I} V2. T2.
#I #L #V1 #T1 #U2 #d #e * #U #HU #HU2
elim (tpss_inv_flat1 … HU) -HU #V #T #HV1 #HT1 #X destruct
elim (lift_inv_flat2 … HU2) -HU2 /3 width=5/
qed-.

(* Basic Inversion lemmas ***************************************************)

lemma delift_inv_refl_O2: ∀L,T1,T2,d. L ⊢ T1 [d, 0] ≡ T2 → T1 = T2.
#L #T1 #T2 #d * #T #HT1
>(tpss_inv_refl_O2 … HT1) -HT1 #HT2
>(lift_inv_refl_O2 … HT2) -HT2 //
qed-.
