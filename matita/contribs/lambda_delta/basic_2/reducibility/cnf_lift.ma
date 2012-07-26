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

include "basic_2/reducibility/cpr_lift.ma".
include "basic_2/reducibility/cpr_cpr.ma".
include "basic_2/reducibility/cnf.ma".

(* CONTEXT-SENSITIVE NORMAL TERMS *******************************************)

(* Advanced inversion lemmas ************************************************)

lemma cnf_inv_delta: ∀L,K,V,i. ⇩[0, i] L ≡ K.ⓓV → L ⊢ 𝐍⦃#i⦄ → ⊥.
#L #K #V #i #HLK #H
elim (lift_total V 0 (i+1)) #W #HVW
lapply (H W ?) -H [ /3 width=6/ ] -HLK #H destruct
elim (lift_inv_lref2_be … HVW ? ?) -HVW //
qed-.

lemma cnf_inv_abst: ∀a,L,V,T. L ⊢ 𝐍⦃ⓛ{a}V.T⦄ → L ⊢ 𝐍⦃V⦄ ∧ L.ⓛV ⊢ 𝐍⦃T⦄.
#a #L #V1 #T1 #HVT1 @conj
[ #V2 #HV2 lapply (HVT1 (ⓛ{a}V2.T1) ?) -HVT1 /2 width=2/ -HV2 #H destruct //
| #T2 #HT2 lapply (HVT1 (ⓛ{a}V1.T2) ?) -HVT1 /2 width=2/ -HT2 #H destruct //
]
qed-.

lemma cnf_inv_abbr: ∀L,V,T. L ⊢ 𝐍⦃-ⓓV.T⦄ → L ⊢ 𝐍⦃V⦄ ∧ L.ⓓV ⊢ 𝐍⦃T⦄.
#L #V1 #T1 #HVT1 @conj
[ #V2 #HV2 lapply (HVT1 (-ⓓV2.T1) ?) -HVT1 /2 width=2/ -HV2 #H destruct //
| #T2 #HT2 lapply (HVT1 (-ⓓV1.T2) ?) -HVT1 /2 width=2/ -HT2 #H destruct //
]
qed-.

(* Advanced properties ******************************************************)

(* Basic_1: was only: nf2_csort_lref *)
lemma cnf_lref_atom: ∀L,i. ⇩[0, i] L ≡ ⋆ → L  ⊢ 𝐍⦃#i⦄.
#L #i #HLK #X #H
elim (cpr_inv_lref1 … H) // *
#K0 #V0 #V1 #HLK0 #_ #_ #_
lapply (ldrop_mono … HLK … HLK0) -L #H destruct
qed.

(* Basic_1: was: nf2_lref_abst *)
lemma cnf_lref_abst: ∀L,K,V,i. ⇩[0, i] L ≡ K. ⓛV → L ⊢ 𝐍⦃#i⦄.
#L #K #V #i #HLK #X #H
elim (cpr_inv_lref1 … H) // *
#K0 #V0 #V1 #HLK0 #_ #_ #_
lapply (ldrop_mono … HLK … HLK0) -L #H destruct
qed.

(* Basic_1: was: nf2_abst *)
lemma cnf_abst: ∀a,I,L,V,W,T. L ⊢ 𝐍⦃W⦄ → L. ⓑ{I} V ⊢ 𝐍⦃T⦄ → L ⊢ 𝐍⦃ⓛ{a}W.T⦄.
#a #I #L #V #W #T #HW #HT #X #H
elim (cpr_inv_abst1 … H I V) -H #W0 #T0 #HW0 #HT0 #H destruct
>(HW … HW0) -W0 >(HT … HT0) -T0 //
qed.

(* Basic_1: was only: nf2_appl_lref *)
lemma cnf_appl_simple: ∀L,V,T. L ⊢ 𝐍⦃V⦄ → L ⊢ 𝐍⦃T⦄ → 𝐒⦃T⦄ → L ⊢ 𝐍⦃ⓐV.T⦄.
#L #V #T #HV #HT #HS #X #H
elim (cpr_inv_appl1_simple … H ?) -H // #V0 #T0 #HV0 #HT0 #H destruct
>(HV … HV0) -V0 >(HT … HT0) -T0 //
qed.

(* Relocation properties ****************************************************)

(* Basic_1: was: nf2_lift *)
lemma cnf_lift: ∀L0,L,T,T0,d,e.
                L ⊢ 𝐍⦃T⦄ → ⇩[d, e] L0 ≡ L → ⇧[d, e] T ≡ T0 → L0 ⊢ 𝐍⦃T0⦄.
#L0 #L #T #T0 #d #e #HLT #HL0 #HT0 #X #H
elim (cpr_inv_lift1 … HL0 … HT0 … H) -L0 #T1 #HT10 #HT1
<(HLT … HT1) in HT0; -L #HT0
>(lift_mono … HT10 … HT0) -T1 -X //
qed.
