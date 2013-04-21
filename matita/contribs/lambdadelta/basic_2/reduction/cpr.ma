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

include "basic_2/unfold/cpqs.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION FOR TERMS ***************************)

(* Basic_1: includes: pr0_delta1 pr2_delta1 pr2_thin_dx pr2_head_1 *)
(* Note: cpr_flat: does not hold in basic_1 *)
inductive cpr: lenv → relation term ≝
| cpr_atom : ∀I,L. cpr L (⓪{I}) (⓪{I})
| cpr_delta: ∀L,K,V,V2,W2,i.
             ⇩[0, i] L ≡ K. ⓓV → cpr K V V2 →
             ⇧[0, i + 1] V2 ≡ W2 → cpr L (#i) W2
| cpr_bind : ∀a,I,L,V1,V2,T1,T2.
             cpr L V1 V2 → cpr (L. ⓑ{I} V1) T1 T2 →
             cpr L (ⓑ{a,I} V1. T1) (ⓑ{a,I} V2. T2)
| cpr_flat : ∀I,L,V1,V2,T1,T2.
             cpr L V1 V2 → cpr L T1 T2 →
             cpr L (ⓕ{I} V1. T1) (ⓕ{I} V2. T2)
| cpr_zeta : ∀L,V,T1,T,T2. cpr (L.ⓓV) T1 T →
             ⇧[0, 1] T2 ≡ T → cpr L (+ⓓV. T1) T2
| cpr_tau  : ∀L,V,T1,T2. cpr L T1 T2 → cpr L (ⓝV. T1) T2
| cpr_beta : ∀a,L,V1,V2,W,T1,T2.
             cpr L V1 V2 → cpr (L.ⓛW) T1 T2 →
             cpr L (ⓐV1. ⓛ{a}W. T1) (ⓓ{a}V2. T2)
| cpr_theta: ∀a,L,V1,V,V2,W1,W2,T1,T2.
             cpr L V1 V → ⇧[0, 1] V ≡ V2 → cpr L W1 W2 → cpr (L.ⓓW1) T1 T2 →
             cpr L (ⓐV1. ⓓ{a}W1. T1) (ⓓ{a}W2. ⓐV2. T2)
.

interpretation "context-sensitive parallel reduction (term)"
   'PRed L T1 T2 = (cpr L T1 T2).

(* Basic properties *********************************************************)

(* Note: it does not hold replacing |L1| with |L2| *)
lemma cpr_lsubr_trans: ∀L1,T1,T2. L1 ⊢ T1 ➡ T2 →
                       ∀L2. L2 ⊑ [0, |L1|] L1 → L2 ⊢ T1 ➡ T2.
#L1 #T1 #T2 #H elim H -L1 -T1 -T2
[ //
| #L1 #K1 #V1 #V2 #W2 #i #HLK1 #_ #HVW2 #IHV12 #L2 #HL12
  lapply (ldrop_fwd_ldrop2_length … HLK1) #Hi
  lapply (ldrop_fwd_O1_length … HLK1) #H2i
  elim (ldrop_lsubr_ldrop2_abbr … HL12 … HLK1 ? ?) -HL12 -HLK1 // -Hi
  <H2i -H2i <minus_plus_m_m /3 width=6/
|3,7: /4 width=1/
|4,6: /3 width=1/
|5,8: /4 width=3/
]
qed-.

(* Basic_1: was by definition: pr2_free *)
lemma tpr_cpr: ∀T1,T2. ⋆ ⊢ T1 ➡ T2 → ∀L. L ⊢ T1 ➡ T2.
#T1 #T2 #HT12 #L
lapply (cpr_lsubr_trans … HT12 L ?) //
qed.

lemma cpqs_cpr: ∀L,T1,T2. L ⊢ T1 ➤* T2 → L ⊢ T1 ➡ T2.
#L #T1 #T2 #H elim H -L -T1 -T2 // /2 width=1/ /2 width=6/
qed.

lemma cpss_cpr: ∀L,T1,T2. L ⊢ T1 ▶* T2 → L ⊢ T1 ➡ T2.
/3 width=1/ qed.

(* Basic_1: includes by definition: pr0_refl *)
lemma cpr_refl: ∀T,L. L ⊢ T ➡ T.
/2 width=1/ qed.

lemma cpr_delift: ∀L,K,V,T1,d. ⇩[0, d] L ≡ (K. ⓓV) →
                  ∃∃T2,T. L ⊢ T1 ➡ T2 & ⇧[d, 1] T ≡ T2.
#L #K #V #T1 #d #HLK
elim (cpqs_delift … T1 … HLK) -HLK /3 width=4/
qed-.

lemma cpr_append: l_appendable_sn … cpr.
#K #T1 #T2 #H elim H -K -T1 -T2 // /2 width=1/ /2 width=3/
#K #K0 #V1 #V2 #W2 #i #HK0 #_ #HVW2 #IHV12 #L
lapply (ldrop_fwd_ldrop2_length … HK0) #H
@(cpr_delta … (L@@K0) V1 … HVW2) //
@(ldrop_O1_append_sn_le … HK0) /2 width=2/ (**) (* /3/ does not work *)
qed.

lemma cpr_ext_bind: ∀L,V1,V2. L ⊢ V1 ➡ V2 → ∀V,T1,T2. L.ⓛV ⊢ T1 ➡ T2 →
                    ∀a,I. L ⊢ ⓑ{a,I}V1. T1 ➡ ⓑ{a,I}V2. T2.
#L #V1 #V2 #HV12 #V #T1 #T2 #HT12 #a #I
lapply (cpr_lsubr_trans … HT12 (L.ⓑ{I}V1) ?) -HT12 /2 width=1/
qed.

(* Basic inversion lemmas ***************************************************)

fact cpr_inv_atom1_aux: ∀L,T1,T2. L ⊢ T1 ➡ T2 → ∀I. T1 = ⓪{I} →
                        T2 = ⓪{I} ∨
                        ∃∃K,V,V2,i. ⇩[O, i] L ≡ K. ⓓV &
                                    K ⊢ V ➡ V2 &
                                    ⇧[O, i + 1] V2 ≡ T2 &
                                    I = LRef i.
#L #T1 #T2 * -L -T1 -T2
[ #I #L #J #H destruct /2 width=1/
| #L #K #V #V2 #T2 #i #HLK #HV2 #HVT2 #J #H destruct /3 width=8/
| #a #I #L #V1 #V2 #T1 #T2 #_ #_ #J #H destruct
| #I #L #V1 #V2 #T1 #T2 #_ #_ #J #H destruct
| #L #V #T1 #T #T2 #_ #_ #J #H destruct
| #L #V #T1 #T2 #_ #J #H destruct
| #a #L #V1 #V2 #W #T1 #T2 #_ #_ #J #H destruct
| #a #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #J #H destruct
]
qed-.

lemma cpr_inv_atom1: ∀I,L,T2. L ⊢ ⓪{I} ➡ T2 →
                     T2 = ⓪{I} ∨
                     ∃∃K,V,V2,i. ⇩[O, i] L ≡ K. ⓓV &
                                 K ⊢ V ➡ V2 &
                                 ⇧[O, i + 1] V2 ≡ T2 &
                                 I = LRef i.
/2 width=3 by cpr_inv_atom1_aux/ qed-.

(* Basic_1: includes: pr0_gen_sort pr2_gen_sort *)
lemma cpr_inv_sort1: ∀L,T2,k. L ⊢ ⋆k ➡ T2 → T2 = ⋆k.
#L #T2 #k #H
elim (cpr_inv_atom1 … H) -H //
* #K #V #V2 #i #_ #_ #_ #H destruct
qed-.

(* Basic_1: includes: pr0_gen_lref pr2_gen_lref *)
lemma cpr_inv_lref1: ∀L,T2,i. L ⊢ #i ➡ T2 →
                     T2 = #i ∨
                     ∃∃K,V,V2. ⇩[O, i] L ≡ K. ⓓV &
                               K ⊢ V ➡ V2 &
                               ⇧[O, i + 1] V2 ≡ T2.
#L #T2 #i #H
elim (cpr_inv_atom1 … H) -H /2 width=1/
* #K #V #V2 #j #HLK #HV2 #HVT2 #H destruct /3 width=6/
qed-.

lemma cpr_inv_gref1: ∀L,T2,p. L ⊢ §p ➡ T2 → T2 = §p.
#L #T2 #p #H
elim (cpr_inv_atom1 … H) -H //
* #K #V #V2 #i #_ #_ #_ #H destruct
qed-.

fact cpr_inv_bind1_aux: ∀L,U1,U2. L ⊢ U1 ➡ U2 →
                        ∀a,I,V1,T1. U1 = ⓑ{a,I} V1. T1 → (
                        ∃∃V2,T2. L ⊢ V1 ➡ V2 &
                                 L. ⓑ{I} V1 ⊢ T1 ➡ T2 &
                                 U2 = ⓑ{a,I} V2. T2
                        ) ∨
                        ∃∃T. L.ⓓV1 ⊢ T1 ➡ T & ⇧[0, 1] U2 ≡ T & a = true & I = Abbr.
#L #U1 #U2 * -L -U1 -U2
[ #I #L #b #J #W1 #U1 #H destruct
| #L #K #V #V2 #W2 #i #_ #_ #_ #b #J #W1 #U1 #H destruct
| #a #I #L #V1 #V2 #T1 #T2 #HV12 #HT12 #b #J #W1 #U1 #H destruct /3 width=5/
| #I #L #V1 #V2 #T1 #T2 #_ #_ #b #J #W1 #U1 #H destruct
| #L #V #T1 #T #T2 #HT1 #HT2 #b #J #W1 #U1 #H destruct /3 width=3/
| #L #V #T1 #T2 #_ #b #J #W1 #U1 #H destruct
| #a #L #V1 #V2 #W #T1 #T2 #_ #_ #b #J #W1 #U1 #H destruct
| #a #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #b #J #W1 #U1 #H destruct
]
qed-.

lemma cpr_inv_bind1: ∀a,I,L,V1,T1,U2. L ⊢ ⓑ{a,I} V1. T1 ➡ U2 → (
                     ∃∃V2,T2. L ⊢ V1 ➡ V2 &
                              L. ⓑ{I} V1 ⊢ T1 ➡ T2 &
                              U2 = ⓑ{a,I} V2. T2
                     ) ∨
                     ∃∃T. L.ⓓV1 ⊢ T1 ➡ T & ⇧[0, 1] U2 ≡ T & a = true & I = Abbr.
/2 width=3 by cpr_inv_bind1_aux/ qed-.

(* Basic_1: includes: pr0_gen_abbr pr2_gen_abbr *)
lemma cpr_inv_abbr1: ∀a,L,V1,T1,U2. L ⊢ ⓓ{a} V1. T1 ➡ U2 → (
                     ∃∃V2,T2. L ⊢ V1 ➡ V2 &
                              L. ⓓ V1 ⊢ T1 ➡ T2 &
                              U2 = ⓓ{a} V2. T2
                     ) ∨
                     ∃∃T. L.ⓓV1 ⊢ T1 ➡ T & ⇧[0, 1] U2 ≡ T & a = true.
#a #L #V1 #T1 #U2 #H
elim (cpr_inv_bind1 … H) -H * /3 width=3/ /3 width=5/
qed-.

(* Basic_1: includes: pr0_gen_abst pr2_gen_abst *)
lemma cpr_inv_abst1: ∀a,L,V1,T1,U2. L ⊢ ⓛ{a} V1. T1 ➡ U2 →
                     ∃∃V2,T2. L ⊢ V1 ➡ V2 & L. ⓛ V1 ⊢ T1 ➡ T2 &
                              U2 = ⓛ{a} V2. T2.
#a #L #V1 #T1 #U2 #H
elim (cpr_inv_bind1 … H) -H *
[ /3 width=5/
| #T #_ #_ #_ #H destruct
]
qed-.

fact cpr_inv_flat1_aux: ∀L,U,U2. L ⊢ U ➡ U2 →
                        ∀I,V1,U1. U = ⓕ{I} V1. U1 →
                        ∨∨ ∃∃V2,T2. L ⊢ V1 ➡ V2 & L ⊢ U1 ➡ T2 &
                                    U2 = ⓕ{I} V2. T2
                         | (L ⊢ U1 ➡ U2 ∧ I = Cast)
                         | ∃∃a,V2,W,T1,T2. L ⊢ V1 ➡ V2 & L.ⓛW ⊢ T1 ➡ T2 &
                                           U1 = ⓛ{a}W. T1 &
                                           U2 = ⓓ{a}V2. T2 & I = Appl
                         | ∃∃a,V,V2,W1,W2,T1,T2. L ⊢ V1 ➡ V & ⇧[0,1] V ≡ V2 &
                                                 L ⊢ W1 ➡ W2 & L.ⓓW1 ⊢ T1 ➡ T2 &
                                                 U1 = ⓓ{a}W1. T1 &
                                                 U2 = ⓓ{a}W2. ⓐV2. T2 & I = Appl.
#L #U #U2 * -L -U -U2
[ #I #L #J #W1 #U1 #H destruct
| #L #K #V #V2 #W2 #i #_ #_ #_ #J #W1 #U1 #H destruct
| #a #I #L #V1 #V2 #T1 #T2 #_ #_ #J #W1 #U1 #H destruct
| #I #L #V1 #V2 #T1 #T2 #HV12 #HT12 #J #W1 #U1 #H destruct /3 width=5/
| #L #V #T1 #T #T2 #_ #_ #J #W1 #U1 #H destruct
| #L #V #T1 #T2 #HT12 #J #W1 #U1 #H destruct /3 width=1/
| #a #L #V1 #V2 #W #T1 #T2 #HV12 #HT12 #J #W1 #U1 #H destruct /3 width=9/
| #a #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 #HW12 #HT12 #J #W1 #U1 #H destruct /3 width=13/
]
qed-.

lemma cpr_inv_flat1: ∀I,L,V1,U1,U2. L ⊢ ⓕ{I} V1. U1 ➡ U2 →
                     ∨∨ ∃∃V2,T2. L ⊢ V1 ➡ V2 & L ⊢ U1 ➡ T2 &
                                 U2 = ⓕ{I} V2. T2
                      | (L ⊢ U1 ➡ U2 ∧ I = Cast)
                      | ∃∃a,V2,W,T1,T2. L ⊢ V1 ➡ V2 & L.ⓛW ⊢ T1 ➡ T2 &
                                        U1 = ⓛ{a}W. T1 &
                                        U2 = ⓓ{a}V2. T2 & I = Appl
                      | ∃∃a,V,V2,W1,W2,T1,T2. L ⊢ V1 ➡ V & ⇧[0,1] V ≡ V2 &
                                              L ⊢ W1 ➡ W2 & L.ⓓW1 ⊢ T1 ➡ T2 &
                                              U1 = ⓓ{a}W1. T1 &
                                              U2 = ⓓ{a}W2. ⓐV2. T2 & I = Appl.
/2 width=3 by cpr_inv_flat1_aux/ qed-.

(* Basic_1: includes: pr0_gen_appl pr2_gen_appl *)
lemma cpr_inv_appl1: ∀L,V1,U1,U2. L ⊢ ⓐ V1. U1 ➡ U2 →
                     ∨∨ ∃∃V2,T2. L ⊢ V1 ➡ V2 & L ⊢ U1 ➡ T2 &
                                 U2 = ⓐ V2. T2
                      | ∃∃a,V2,W,T1,T2. L ⊢ V1 ➡ V2 & L.ⓛW ⊢ T1 ➡ T2 &
                                        U1 = ⓛ{a}W. T1 & U2 = ⓓ{a}V2. T2
                      | ∃∃a,V,V2,W1,W2,T1,T2. L ⊢ V1 ➡ V & ⇧[0,1] V ≡ V2 &
                                              L ⊢ W1 ➡ W2 & L.ⓓW1 ⊢ T1 ➡ T2 &
                                              U1 = ⓓ{a}W1. T1 & U2 = ⓓ{a}W2. ⓐV2. T2.
#L #V1 #U1 #U2 #H elim (cpr_inv_flat1 … H) -H *
[ /3 width=5/
| #_ #H destruct
| /3 width=9/
| /3 width=13/
]
qed-.

(* Note: the main property of simple terms *)
lemma cpr_inv_appl1_simple: ∀L,V1,T1,U. L ⊢ ⓐV1. T1 ➡ U → 𝐒⦃T1⦄ →
                            ∃∃V2,T2. L ⊢ V1 ➡ V2 & L ⊢ T1 ➡ T2 &
                                     U = ⓐV2. T2.
#L #V1 #T1 #U #H #HT1
elim (cpr_inv_appl1 … H) -H *
[ /2 width=5/
| #a #V2 #W #U1 #U2 #_ #_ #H #_ destruct
  elim (simple_inv_bind … HT1)
| #a #V #V2 #W1 #W2 #U1 #U2 #_ #_ #_ #_ #H #_ destruct
  elim (simple_inv_bind … HT1)
]
qed-.

(* Basic_1: includes: pr0_gen_cast pr2_gen_cast *)
lemma cpr_inv_cast1: ∀L,V1,U1,U2. L ⊢ ⓝ V1. U1 ➡ U2 → (
                     ∃∃V2,T2. L ⊢ V1 ➡ V2 & L ⊢ U1 ➡ T2 &
                              U2 = ⓝ V2. T2
                     ) ∨
                     L ⊢ U1 ➡ U2.
#L #V1 #U1 #U2 #H elim (cpr_inv_flat1 … H) -H *
[ /3 width=5/
| /2 width=1/
| #a #V2 #W #T1 #T2 #_ #_ #_ #_ #H destruct
| #a #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #H destruct
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma cpr_fwd_abst1: ∀a,L,V1,T1,U2. L ⊢ ⓛ{a}V1.T1 ➡ U2 → ∀I,W.
                     ∃∃V2,T2. L ⊢ V1 ➡ V2 & L. ⓑ{I} W ⊢ T1 ➡ T2 &
                              U2 = ⓛ{a} V2. T2.
#a #L #V1 #T1 #U2 #H #I #W
elim (cpr_inv_abst1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
lapply (cpr_lsubr_trans … HT12 (L.ⓑ{I}W) ?) -HT12 /2 width=1/ /2 width=5/
qed-.


lemma cpr_fwd_ext_abst1: ∀a,L,V1,T1,U2. L ⊢ ⓛ{a}V1.T1 ➡ U2 → ∀b,I,W.
                         ∃∃V2,T2. L ⊢ V1 ➡ V2 & L ⊢ ⓑ{b,I}W.T1 ➡ ⓑ{b,I}W.T2 &
                                  U2 = ⓛ{a}V2.T2.
#a #L #V1 #T1 #U2 #H #b #I #W
elim (cpr_fwd_abst1 … H I W) -H /3 width=5/
qed-.

lemma cpr_fwd_bind1_minus: ∀I,L,V1,T1,T. L ⊢ -ⓑ{I}V1.T1 ➡ T → ∀b.
                           ∃∃V2,T2. L ⊢ ⓑ{b,I}V1.T1 ➡ ⓑ{b,I}V2.T2 &
                                    T = -ⓑ{I}V2.T2.
#I #L #V1 #T1 #T #H #b
elim (cpr_inv_bind1 … H) -H *
[ #V2 #T2 #HV12 #HT12 #H destruct /3 width=4/
| #T2 #_ #_ #H destruct 
]
qed-.

lemma cpr_fwd_shift1: ∀L1,L,T1,T. L ⊢ L1 @@ T1 ➡ T →
                      ∃∃L2,T2. |L1| = |L2| & T = L2 @@ T2.
#L1 @(lenv_ind_dx … L1) -L1 normalize
[ #L #T1 #T #HT1
  @(ex2_2_intro … (⋆)) // (**) (* explicit constructor *)
| #I #L1 #V1 #IH #L #T1 #X
  >shift_append_assoc normalize #H
  elim (cpr_inv_bind1 … H) -H *
  [ #V0 #T0 #_ #HT10 #H destruct
    elim (IH … HT10) -IH -HT10 #L2 #T2 #HL12 #H destruct
    >append_length >HL12 -HL12
    @(ex2_2_intro … (⋆.ⓑ{I}V0@@L2) T2) [ >append_length ] // /2 width=3/ (**) (* explicit constructor *)
  | #T #_ #_ #H destruct
  ]
]
qed-.

(* Basic_1: removed theorems 12:
            pr0_subst0_back pr0_subst0_fwd pr0_subst0
            pr2_head_2 pr2_cflat clear_pr2_trans
            pr2_gen_csort pr2_gen_cflat pr2_gen_cbind
            pr2_subst1
            pr2_gen_ctail pr2_ctail
*)   
(* Basic_1: removed local theorems 4:
            pr0_delta_tau pr0_cong_delta
            pr2_free_free pr2_free_delta
*)
