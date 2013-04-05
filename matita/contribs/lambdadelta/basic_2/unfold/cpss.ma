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

include "basic_2/substitution/ldrop_append.ma".

(* CONTEXT-SENSITIVE PARALLEL UNFOLD FOR TERMS ******************************)

inductive cpss: lenv → relation term ≝
| cpss_atom : ∀L,I. cpss L (⓪{I}) (⓪{I})
| cpss_subst: ∀L,K,V,V2,W2,i.
              ⇩[0, i] L ≡ K. ⓓV → cpss K V V2 →
              ⇧[0, i + 1] V2 ≡ W2 → cpss L (#i) W2
| cpss_bind : ∀L,a,I,V1,V2,T1,T2.
              cpss L V1 V2 → cpss (L. ⓑ{I} V1) T1 T2 →
              cpss L (ⓑ{a,I} V1. T1) (ⓑ{a,I} V2. T2)
| cpss_flat : ∀L,I,V1,V2,T1,T2.
              cpss L V1 V2 → cpss L T1 T2 →
              cpss L (ⓕ{I} V1. T1) (ⓕ{I} V2. T2)
.

interpretation "context-sensitive parallel unfold (term)"
   'PSubstStar L T1 T2 = (cpss L T1 T2).

(* Basic properties *********************************************************)

(* Note: it does not hold replacing |L1| with |L2| *)
lemma cpss_lsubr_trans: ∀L1,T1,T2. L1 ⊢ T1 ▶* T2 →
                        ∀L2. L2 ⊑ [0, |L1|] L1 → L2 ⊢ T1 ▶* T2.
#L1 #T1 #T2 #H elim H -L1 -T1 -T2
[ //
| #L1 #K1 #V1 #V2 #W2 #i #HLK1 #_ #HVW2 #IHV12 #L2 #HL12
  lapply (ldrop_fwd_ldrop2_length … HLK1) #Hi
  lapply (ldrop_fwd_O1_length … HLK1) #H2i
  elim (ldrop_lsubr_ldrop2_abbr … HL12 … HLK1 ? ?) -HL12 -HLK1 // -Hi
  <H2i -H2i <minus_plus_m_m /3 width=6/
| /4 width=1/
| /3 width=1/
]
qed-.

lemma cpss_refl: ∀T,L. L ⊢ T ▶* T.
#T elim T -T //
#I elim I -I /2 width=1/
qed.

lemma cpss_delift: ∀K,V,T1,L,d. ⇩[0, d] L ≡ (K. ⓓV) →
                   ∃∃T2,T. L ⊢ T1 ▶* T2 & ⇧[d, 1] T ≡ T2.
#K #V #T1 elim T1 -T1
[ * #i #L #d #HLK /2 width=4/
  elim (lt_or_eq_or_gt i d) #Hid /3 width=4/
  destruct
  elim (lift_total V 0 (i+1)) #W #HVW
  elim (lift_split … HVW i i ? ? ?) // /3 width=6/
| * [ #a ] #I #W1 #U1 #IHW1 #IHU1 #L #d #HLK
  elim (IHW1 … HLK) -IHW1 #W2 #W #HW12 #HW2
  [ elim (IHU1 (L. ⓑ{I} W1) (d+1) ?) -IHU1 /2 width=1/ -HLK /3 width=9/
  | elim (IHU1 … HLK) -IHU1 -HLK /3 width=8/
  ]
]
qed-.

lemma cpss_append: ∀K,T1,T2. K ⊢ T1 ▶* T2 → ∀L. L @@ K ⊢ T1 ▶* T2.
#K #T1 #T2 #H elim H -K -T1 -T2 // /2 width=1/
#K #K0 #V1 #V2 #W2 #i #HK0 #_ #HVW2 #IHV12 #L
lapply (ldrop_fwd_ldrop2_length … HK0) #H
@(cpss_subst … (L@@K0) V1 … HVW2) //
@(ldrop_O1_append_sn_le … HK0) /2 width=2/ (**) (* /3/ does not work *)
qed.

(* Basic inversion lemmas ***************************************************)

fact cpss_inv_atom1_aux: ∀L,T1,T2. L ⊢ T1 ▶* T2 → ∀I. T1 = ⓪{I} →
                         T2 = ⓪{I} ∨
                         ∃∃K,V,V2,i. ⇩[O, i] L ≡ K. ⓓV &
                                     K ⊢ V ▶* V2 &
                                     ⇧[O, i + 1] V2 ≡ T2 &
                                     I = LRef i.
#L #T1 #T2 * -L -T1 -T2
[ #L #I #J #H destruct /2 width=1/
| #L #K #V #V2 #T2 #i #HLK #HV2 #HVT2 #I #H destruct /3 width=8/
| #L #a #I #V1 #V2 #T1 #T2 #_ #_ #J #H destruct
| #L #I #V1 #V2 #T1 #T2 #_ #_ #J #H destruct
]
qed-.

lemma cpss_inv_atom1: ∀L,T2,I. L ⊢ ⓪{I} ▶* T2 →
                      T2 = ⓪{I} ∨
                      ∃∃K,V,V2,i. ⇩[O, i] L ≡ K. ⓓV &
                                  K ⊢ V ▶* V2 &
                                  ⇧[O, i + 1] V2 ≡ T2 &
                                  I = LRef i.
/2 width=3 by cpss_inv_atom1_aux/ qed-.

lemma cpss_inv_sort1: ∀L,T2,k. L ⊢ ⋆k ▶* T2 → T2 = ⋆k.
#L #T2 #k #H
elim (cpss_inv_atom1 … H) -H //
* #K #V #V2 #i #_ #_ #_ #H destruct
qed-.

lemma cpss_inv_lref1: ∀L,T2,i. L ⊢ #i ▶* T2 →
                      T2 = #i ∨
                      ∃∃K,V,V2. ⇩[O, i] L ≡ K. ⓓV &
                                K ⊢ V ▶* V2 &
                                ⇧[O, i + 1] V2 ≡ T2.
#L #T2 #i #H
elim (cpss_inv_atom1 … H) -H /2 width=1/
* #K #V #V2 #j #HLK #HV2 #HVT2 #H destruct /3 width=6/
qed-.

lemma cpss_inv_gref1: ∀L,T2,p. L ⊢ §p ▶* T2 → T2 = §p.
#L #T2 #p #H
elim (cpss_inv_atom1 … H) -H //
* #K #V #V2 #i #_ #_ #_ #H destruct
qed-.

fact cpss_inv_bind1_aux: ∀L,U1,U2. L ⊢ U1 ▶* U2 →
                         ∀a,I,V1,T1. U1 = ⓑ{a,I} V1. T1 →
                         ∃∃V2,T2. L ⊢ V1 ▶* V2 &
                                  L. ⓑ{I} V1 ⊢ T1 ▶* T2 &
                                  U2 = ⓑ{a,I} V2. T2.
#L #U1 #U2 * -L -U1 -U2
[ #L #k #a #I #V1 #T1 #H destruct
| #L #K #V #V2 #W2 #i #_ #_ #_ #a #I #V1 #T1 #H destruct
| #L #b #J #V1 #V2 #T1 #T2 #HV12 #HT12 #a #I #V #T #H destruct /2 width=5/
| #L #J #V1 #V2 #T1 #T2 #_ #_ #a #I #V #T #H destruct
]
qed-.

lemma cpss_inv_bind1: ∀L,a,I,V1,T1,U2. L ⊢ ⓑ{a,I} V1. T1 ▶* U2 →
                      ∃∃V2,T2. L ⊢ V1 ▶* V2 &
                               L. ⓑ{I} V1 ⊢ T1 ▶* T2 &
                               U2 = ⓑ{a,I} V2. T2.
/2 width=3 by cpss_inv_bind1_aux/ qed-.

fact cpss_inv_flat1_aux: ∀L,U1,U2. L ⊢ U1 ▶* U2 →
                         ∀I,V1,T1. U1 = ⓕ{I} V1. T1 →
                         ∃∃V2,T2. L ⊢ V1 ▶* V2 & L ⊢ T1 ▶* T2 &
                                  U2 =  ⓕ{I} V2. T2.
#L #U1 #U2 * -L -U1 -U2
[ #L #k #I #V1 #T1 #H destruct
| #L #K #V #V2 #W2 #i #_ #_ #_ #I #V1 #T1 #H destruct
| #L #a #J #V1 #V2 #T1 #T2 #_ #_ #I #V #T #H destruct
| #L #J #V1 #V2 #T1 #T2 #HV12 #HT12 #I #V #T #H destruct /2 width=5/
]
qed-.

lemma cpss_inv_flat1: ∀L,I,V1,T1,U2. L ⊢ ⓕ{I} V1. T1 ▶* U2 →
                      ∃∃V2,T2. L ⊢ V1 ▶* V2 & L ⊢ T1 ▶* T2 &
                               U2 =  ⓕ{I} V2. T2.
/2 width=3 by cpss_inv_flat1_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma cpss_fwd_tw: ∀L,T1,T2. L ⊢ T1 ▶* T2 → ♯{T1} ≤ ♯{T2}.
#L #T1 #T2 #H elim H -L -T1 -T2 normalize
/3 by monotonic_le_plus_l, le_plus/ (**) (* just /3 width=1/ is too slow *)
qed-.

lemma cpss_fwd_shift1: ∀L1,L,T1,T. L ⊢ L1 @@ T1 ▶* T →
                       ∃∃L2,T2. |L1| = |L2| & T = L2 @@ T2.
#L1 @(lenv_ind_dx … L1) -L1 normalize
[ #L #T1 #T #HT1
  @(ex2_2_intro … (⋆)) // (**) (* explicit constructor *)
| #I #L1 #V1 #IH #L #T1 #X
  >shift_append_assoc normalize #H
  elim (cpss_inv_bind1 … H) -H
  #V0 #T0 #_ #HT10 #H destruct
  elim (IH … HT10) -IH -HT10 #L2 #T2 #HL12 #H destruct
  >append_length >HL12 -HL12
  @(ex2_2_intro … (⋆.ⓑ{I}V0@@L2) T2) [ >append_length ] // /2 width=3/ (**) (* explicit constructor *)
]
qed-.
