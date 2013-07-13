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

include "basic_2/reduction/cpr.ma".

(* CONTEXT-SENSITIVE NORMAL TERMS *******************************************)

definition cnr: lenv → predicate term ≝ λL. NF … (cpr L) (eq …).

interpretation
   "context-sensitive normality (term)"
   'Normal L T = (cnr L T).

(* Basic inversion lemmas ***************************************************)

lemma cnr_inv_delta: ∀L,K,V,i. ⇩[0, i] L ≡ K.ⓓV → L ⊢ 𝐍⦃#i⦄ → ⊥.
#L #K #V #i #HLK #H
elim (lift_total V 0 (i+1)) #W #HVW
lapply (H W ?) -H [ /3 width=6/ ] -HLK #H destruct
elim (lift_inv_lref2_be … HVW) -HVW //
qed-.

lemma cnr_inv_abst: ∀a,L,V,T. L ⊢ 𝐍⦃ⓛ{a}V.T⦄ → L ⊢ 𝐍⦃V⦄ ∧ L.ⓛV ⊢ 𝐍⦃T⦄.
#a #L #V1 #T1 #HVT1 @conj
[ #V2 #HV2 lapply (HVT1 (ⓛ{a}V2.T1) ?) -HVT1 /2 width=2/ -HV2 #H destruct //
| #T2 #HT2 lapply (HVT1 (ⓛ{a}V1.T2) ?) -HVT1 /2 width=2/ -HT2 #H destruct //
]
qed-.

lemma cnr_inv_abbr: ∀L,V,T. L ⊢ 𝐍⦃-ⓓV.T⦄ → L ⊢ 𝐍⦃V⦄ ∧ L.ⓓV ⊢ 𝐍⦃T⦄.
#L #V1 #T1 #HVT1 @conj
[ #V2 #HV2 lapply (HVT1 (-ⓓV2.T1) ?) -HVT1 /2 width=2/ -HV2 #H destruct //
| #T2 #HT2 lapply (HVT1 (-ⓓV1.T2) ?) -HVT1 /2 width=2/ -HT2 #H destruct //
]
qed-.

lemma cnr_inv_zeta: ∀L,V,T. L ⊢ 𝐍⦃+ⓓV.T⦄ → ⊥.
#L #V #T #H elim (is_lift_dec T 0 1)
[ * #U #HTU
  lapply (H U ?) -H /2 width=3/ #H destruct
  elim (lift_inv_pair_xy_y … HTU)
| #HT
  elim (cpss_delift (⋆) V T (⋆. ⓓV) 0 ?) // #T2 #T1 #HT2 #HT12
  lapply (H (+ⓓV.T2) ?) -H /4 width=1/ -HT2 #H destruct /3 width=2/
]
qed-.

lemma cnr_inv_appl: ∀L,V,T. L ⊢ 𝐍⦃ⓐV.T⦄ → ∧∧ L ⊢ 𝐍⦃V⦄ & L ⊢ 𝐍⦃T⦄ & 𝐒⦃T⦄.
#L #V1 #T1 #HVT1 @and3_intro
[ #V2 #HV2 lapply (HVT1 (ⓐV2.T1) ?) -HVT1 /2 width=1/ -HV2 #H destruct //
| #T2 #HT2 lapply (HVT1 (ⓐV1.T2) ?) -HVT1 /2 width=1/ -HT2 #H destruct //
| generalize in match HVT1; -HVT1 elim T1 -T1 * // #a * #W1 #U1 #_ #_ #H
  [ elim (lift_total V1 0 1) #V2 #HV12
    lapply (H (ⓓ{a}W1.ⓐV2.U1) ?) -H /3 width=3/ -HV12 #H destruct
  | lapply (H (ⓓ{a}V1.U1) ?) -H /3 width=1/ #H destruct
]
qed-.

lemma cnr_inv_tau: ∀L,V,T. L ⊢ 𝐍⦃ⓝV.T⦄ → ⊥.
#L #V #T #H lapply (H T ?) -H /2 width=1/ #H
@discr_tpair_xy_y //
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: nf2_sort *)
lemma cnr_sort: ∀L,k. L ⊢ 𝐍⦃⋆k⦄.
#L #k #X #H
>(cpr_inv_sort1 … H) //
qed.

(* Basic_1: was: nf2_abst *)
lemma cnr_abst: ∀a,I,L,V,W,T. L ⊢ 𝐍⦃W⦄ → L. ⓑ{I} V ⊢ 𝐍⦃T⦄ → L ⊢ 𝐍⦃ⓛ{a}W.T⦄.
#a #I #L #V #W #T #HW #HT #X #H
elim (cpr_fwd_abst1 … H I V) -H #W0 #T0 #HW0 #HT0 #H destruct
>(HW … HW0) -W0 >(HT … HT0) -T0 //
qed.

(* Basic_1: was only: nf2_appl_lref *)
lemma cnr_appl_simple: ∀L,V,T. L ⊢ 𝐍⦃V⦄ → L ⊢ 𝐍⦃T⦄ → 𝐒⦃T⦄ → L ⊢ 𝐍⦃ⓐV.T⦄.
#L #V #T #HV #HT #HS #X #H
elim (cpr_inv_appl1_simple … H ?) -H // #V0 #T0 #HV0 #HT0 #H destruct
>(HV … HV0) -V0 >(HT … HT0) -T0 //
qed.

(* Basic_1: was: nf2_dec *)
axiom cnr_dec: ∀L,T1. L ⊢ 𝐍⦃T1⦄ ∨
               ∃∃T2. L ⊢ T1 ➡ T2 & (T1 = T2 → ⊥).

(* Basic_1: removed theorems 1: nf2_abst_shift *)
