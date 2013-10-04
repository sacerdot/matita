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

include "basic_2/notation/relations/pred_6.ma".
include "basic_2/static/sd.ma".
include "basic_2/reduction/cpr.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL REDUCTION FOR TERMS ******************)

(* avtivate genv *)
inductive cpx (h) (g): relation4 genv lenv term term ≝
| cpx_atom : ∀I,G,L. cpx h g G L (⓪{I}) (⓪{I})
| cpx_sort : ∀G,L,k,l. deg h g k (l+1) → cpx h g G L (⋆k) (⋆(next h k))
| cpx_delta: ∀I,G,L,K,V,V2,W2,i.
             ⇩[0, i] L ≡ K.ⓑ{I}V → cpx h g G K V V2 →
             ⇧[0, i + 1] V2 ≡ W2 → cpx h g G L (#i) W2
| cpx_bind : ∀a,I,G,L,V1,V2,T1,T2.
             cpx h g G L V1 V2 → cpx h g G (L.ⓑ{I}V1) T1 T2 →
             cpx h g G L (ⓑ{a,I}V1.T1) (ⓑ{a,I}V2.T2)
| cpx_flat : ∀I,G,L,V1,V2,T1,T2.
             cpx h g G L V1 V2 → cpx h g G L T1 T2 →
             cpx h g G L (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
| cpx_zeta : ∀G,L,V,T1,T,T2. cpx h g G (L.ⓓV) T1 T →
             ⇧[0, 1] T2 ≡ T → cpx h g G L (+ⓓV.T1) T2
| cpx_tau  : ∀G,L,V,T1,T2. cpx h g G L T1 T2 → cpx h g G L (ⓝV.T1) T2
| cpx_ti   : ∀G,L,V1,V2,T. cpx h g G L V1 V2 → cpx h g G L (ⓝV1.T) V2
| cpx_beta : ∀a,G,L,V1,V2,W1,W2,T1,T2.
             cpx h g G L V1 V2 → cpx h g G L W1 W2 → cpx h g G (L.ⓛW1) T1 T2 →
             cpx h g G L (ⓐV1.ⓛ{a}W1.T1) (ⓓ{a}ⓝW2.V2.T2)
| cpx_theta: ∀a,G,L,V1,V,V2,W1,W2,T1,T2.
             cpx h g G L V1 V → ⇧[0, 1] V ≡ V2 → cpx h g G L W1 W2 →
             cpx h g G (L.ⓓW1) T1 T2 →
             cpx h g G L (ⓐV1.ⓓ{a}W1.T1) (ⓓ{a}W2.ⓐV2.T2)
.

interpretation
   "context-sensitive extended parallel reduction (term)"
   'PRed h g G L T1 T2 = (cpx h g G L T1 T2).

(* Basic properties *********************************************************)

lemma lsubr_cpx_trans: ∀h,g,G. lsub_trans … (cpx h g G) lsubr.
#h #g #G #L1 #T1 #T2 #H elim H -G -L1 -T1 -T2
[ //
| /2 width=2/
| #I #G #L1 #K1 #V1 #V2 #W2 #i #HLK1 #_ #HVW2 #IHV12 #L2 #HL12
  elim (lsubr_fwd_ldrop2_bind … HL12 … HLK1) -HL12 -HLK1 *
  [ /3 width=7/ | /4 width=7/ ]
|4,9: /4 width=1/
|5,7,8: /3 width=1/
|6,10: /4 width=3/
]
qed-.

(* Note: this is "∀h,g,L. reflexive … (cpx h g L)" *)
lemma cpx_refl: ∀h,g,G,T,L. ⦃G, L⦄ ⊢ T ➡[h, g] T.
#h #g #G #T elim T -T // * /2 width=1/
qed.

lemma cpr_cpx: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡ T2 → ⦃G, L⦄ ⊢ T1 ➡[h, g] T2.
#h #g #G #L #T1 #T2 #H elim H -L -T1 -T2 // /2 width=1/ /2 width=3/ /2 width=7/
qed.

lemma cpx_pair_sn: ∀h,g,I,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 →
                   ∀T. ⦃G, L⦄ ⊢ ②{I}V1.T ➡[h, g] ②{I}V2.T.
#h #g * /2 width=1/ qed.

lemma cpx_delift: ∀h,g,I,G,K,V,T1,L,d. ⇩[0, d] L ≡ (K.ⓑ{I}V) →
                  ∃∃T2,T.  ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 & ⇧[d, 1] T ≡ T2.
#h #g #I #G #K #V #T1 elim T1 -T1
[ * #i #L #d #HLK /2 width=4/
  elim (lt_or_eq_or_gt i d) #Hid [1,3: /3 width=4/ ]
  destruct
  elim (lift_total V 0 (i+1)) #W #HVW
  elim (lift_split … HVW i i) // /3 width=7/
| * [ #a ] #I #W1 #U1 #IHW1 #IHU1 #L #d #HLK
  elim (IHW1 … HLK) -IHW1 #W2 #W #HW12 #HW2
  [ elim (IHU1 (L. ⓑ{I} W1) (d+1)) -IHU1 /2 width=1/ -HLK /3 width=9/
  | elim (IHU1 … HLK) -IHU1 -HLK /3 width=8/
  ]
]
qed-.

lemma cpx_append: ∀h,g,G. l_appendable_sn … (cpx h g G).
#h #g #G #K #T1 #T2 #H elim H -G -K -T1 -T2 // /2 width=1/ /2 width=3/
#I #G #K #K0 #V1 #V2 #W2 #i #HK0 #_ #HVW2 #IHV12 #L
lapply (ldrop_fwd_length_lt2 … HK0) #H
@(cpx_delta … I … (L@@K0) V1 … HVW2) //
@(ldrop_O1_append_sn_le … HK0) /2 width=2/ (**) (* /3/ does not work *)
qed.

(* Basic inversion lemmas ***************************************************)

fact cpx_inv_atom1_aux: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 → ∀J. T1 = ⓪{J} →
                        ∨∨ T2 = ⓪{J}
                         | ∃∃k,l. deg h g k (l+1) & T2 = ⋆(next h k) & J = Sort k
                         | ∃∃I,K,V,V2,i. ⇩[O, i] L ≡ K.ⓑ{I}V & ⦃G, K⦄ ⊢ V ➡[h, g] V2 &
                                         ⇧[O, i + 1] V2 ≡ T2 & J = LRef i.
#G #h #g #L #T1 #T2 * -L -T1 -T2
[ #I #G #L #J #H destruct /2 width=1/
| #G #L #k #l #Hkl #J #H destruct /3 width=5/
| #I #G #L #K #V #V2 #T2 #i #HLK #HV2 #HVT2 #J #H destruct /3 width=9/
| #a #I #G #L #V1 #V2 #T1 #T2 #_ #_ #J #H destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #J #H destruct
| #G #L #V #T1 #T #T2 #_ #_ #J #H destruct
| #G #L #V #T1 #T2 #_ #J #H destruct
| #G #L #V1 #V2 #T #_ #J #H destruct
| #a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #J #H destruct
| #a #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #J #H destruct
]
qed-.

lemma cpx_inv_atom1: ∀h,g,J,G,L,T2. ⦃G, L⦄ ⊢ ⓪{J} ➡[h, g] T2 →
                     ∨∨ T2 = ⓪{J}
                      | ∃∃k,l. deg h g k (l+1) & T2 = ⋆(next h k) & J = Sort k
                      | ∃∃I,K,V,V2,i. ⇩[O, i] L ≡ K.ⓑ{I}V & ⦃G, K⦄ ⊢ V ➡[h, g] V2 &
                                      ⇧[O, i + 1] V2 ≡ T2 & J = LRef i.
/2 width=3 by cpx_inv_atom1_aux/ qed-.

lemma cpx_inv_sort1: ∀h,g,G,L,T2,k. ⦃G, L⦄ ⊢ ⋆k ➡[h, g] T2 → T2 = ⋆k ∨
                     ∃∃l. deg h g k (l+1) & T2 = ⋆(next h k).
#h #g #G #L #T2 #k #H
elim (cpx_inv_atom1 … H) -H /2 width=1/ *
[ #k0 #l0 #Hkl0 #H1 #H2 destruct /3 width=4/
| #I #K #V #V2 #i #_ #_ #_ #H destruct
]
qed-.

lemma cpx_inv_lref1: ∀h,g,G,L,T2,i. ⦃G, L⦄ ⊢ #i ➡[h, g] T2 →
                     T2 = #i ∨
                     ∃∃I,K,V,V2. ⇩[O, i] L ≡ K. ⓑ{I}V & ⦃G, K⦄ ⊢ V ➡[h, g] V2 &
                                 ⇧[O, i + 1] V2 ≡ T2.
#h #g #G #L #T2 #i #H
elim (cpx_inv_atom1 … H) -H /2 width=1/ *
[ #k #l #_ #_ #H destruct
| #I #K #V #V2 #j #HLK #HV2 #HVT2 #H destruct /3 width=7/
]
qed-.

lemma cpx_inv_gref1: ∀h,g,G,L,T2,p.  ⦃G, L⦄ ⊢ §p ➡[h, g] T2 → T2 = §p.
#h #g #G #L #T2 #p #H
elim (cpx_inv_atom1 … H) -H // *
[ #k #l #_ #_ #H destruct
| #I #K #V #V2 #i #_ #_ #_ #H destruct
]
qed-.

fact cpx_inv_bind1_aux: ∀h,g,G,L,U1,U2. ⦃G, L⦄ ⊢ U1 ➡[h, g] U2 →
                        ∀a,J,V1,T1. U1 = ⓑ{a,J}V1.T1 → (
                        ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 & ⦃G, L.ⓑ{J}V1⦄ ⊢ T1 ➡[h, g] T2 &
                                 U2 = ⓑ{a,J}V2.T2
                        ) ∨
                        ∃∃T. ⦃G, L.ⓓV1⦄ ⊢ T1 ➡[h, g] T & ⇧[0, 1] U2 ≡ T &
                             a = true & J = Abbr.
#h #g #G #L #U1 #U2 * -L -U1 -U2
[ #I #G #L #b #J #W #U1 #H destruct
| #G #L #k #l #_ #b #J #W #U1 #H destruct
| #I #G #L #K #V #V2 #W2 #i #_ #_ #_ #b #J #W #U1 #H destruct
| #a #I #G #L #V1 #V2 #T1 #T2 #HV12 #HT12 #b #J #W #U1 #H destruct /3 width=5/
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #b #J #W #U1 #H destruct
| #G #L #V #T1 #T #T2 #HT1 #HT2 #b #J #W #U1 #H destruct /3 width=3/
| #G #L #V #T1 #T2 #_ #b #J #W #U1 #H destruct
| #G #L #V1 #V2 #T #_ #b #J #W #U1 #H destruct
| #a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #b #J #W #U1 #H destruct
| #a #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #b #J #W #U1 #H destruct
]
qed-.

lemma cpx_inv_bind1: ∀h,g,a,I,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡[h, g] U2 → (
                     ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 & ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ➡[h, g] T2 &
                              U2 = ⓑ{a,I} V2. T2
                     ) ∨
                     ∃∃T. ⦃G, L.ⓓV1⦄ ⊢ T1 ➡[h, g] T & ⇧[0, 1] U2 ≡ T &
                          a = true & I = Abbr.
/2 width=3 by cpx_inv_bind1_aux/ qed-.

lemma cpx_inv_abbr1: ∀h,g,a,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓓ{a}V1.T1 ➡[h, g] U2 → (
                     ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 & ⦃G, L.ⓓV1⦄ ⊢ T1 ➡[h, g] T2 &
                              U2 = ⓓ{a} V2. T2
                     ) ∨
                     ∃∃T. ⦃G, L.ⓓV1⦄ ⊢ T1 ➡[h, g] T & ⇧[0, 1] U2 ≡ T & a = true.
#h #g #a #G #L #V1 #T1 #U2 #H
elim (cpx_inv_bind1 … H) -H * /3 width=3/ /3 width=5/
qed-.

lemma cpx_inv_abst1: ∀h,g,a,G,L,V1,T1,U2.  ⦃G, L⦄ ⊢ ⓛ{a}V1.T1 ➡[h, g] U2 →
                     ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 &  ⦃G, L.ⓛV1⦄ ⊢ T1 ➡[h, g] T2 &
                              U2 = ⓛ{a} V2. T2.
#h #g #a #G #L #V1 #T1 #U2 #H
elim (cpx_inv_bind1 … H) -H *
[ /3 width=5/
| #T #_ #_ #_ #H destruct
]
qed-.

fact cpx_inv_flat1_aux: ∀h,g,G,L,U,U2. ⦃G, L⦄ ⊢ U ➡[h, g] U2 →
                        ∀J,V1,U1. U = ⓕ{J}V1.U1 →
                        ∨∨ ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 & ⦃G, L⦄ ⊢ U1 ➡[h, g] T2 &
                                    U2 = ⓕ{J}V2.T2
                         | (⦃G, L⦄ ⊢ U1 ➡[h, g] U2 ∧ J = Cast)
                         | (⦃G, L⦄ ⊢ V1 ➡[h, g] U2 ∧ J = Cast)
                         | ∃∃a,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 & ⦃G, L⦄ ⊢ W1 ➡[h, g] W2 &
                                               ⦃G, L.ⓛW1⦄ ⊢ T1 ➡[h, g] T2 &
                                               U1 = ⓛ{a}W1.T1 &
                                               U2 = ⓓ{a}ⓝW2.V2.T2 & J = Appl
                         | ∃∃a,V,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V & ⇧[0,1] V ≡ V2 &
                                                 ⦃G, L⦄ ⊢ W1 ➡[h, g] W2 & ⦃G, L.ⓓW1⦄ ⊢ T1 ➡[h, g] T2 &
                                                 U1 = ⓓ{a}W1.T1 &
                                                 U2 = ⓓ{a}W2.ⓐV2.T2 & J = Appl.
#h #g #G #L #U #U2 * -L -U -U2
[ #I #G #L #J #W #U1 #H destruct
| #G #L #k #l #_ #J #W #U1 #H destruct
| #I #G #L #K #V #V2 #W2 #i #_ #_ #_ #J #W #U1 #H destruct
| #a #I #G #L #V1 #V2 #T1 #T2 #_ #_ #J #W #U1 #H destruct
| #I #G #L #V1 #V2 #T1 #T2 #HV12 #HT12 #J #W #U1 #H destruct /3 width=5/
| #G #L #V #T1 #T #T2 #_ #_ #J #W #U1 #H destruct
| #G #L #V #T1 #T2 #HT12 #J #W #U1 #H destruct /3 width=1/
| #G #L #V1 #V2 #T #HV12 #J #W #U1 #H destruct /3 width=1/
| #a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HW12 #HT12 #J #W #U1 #H destruct /3 width=11/
| #a #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 #HW12 #HT12 #J #W #U1 #H destruct /3 width=13/
]
qed-.

lemma cpx_inv_flat1: ∀h,g,I,G,L,V1,U1,U2. ⦃G, L⦄ ⊢ ⓕ{I}V1.U1 ➡[h, g] U2 →
                     ∨∨ ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 & ⦃G, L⦄ ⊢ U1 ➡[h, g] T2 &
                                 U2 = ⓕ{I} V2. T2
                      | (⦃G, L⦄ ⊢ U1 ➡[h, g] U2 ∧ I = Cast)
                      | (⦃G, L⦄ ⊢ V1 ➡[h, g] U2 ∧ I = Cast)
                      | ∃∃a,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 & ⦃G, L⦄ ⊢ W1 ➡[h, g] W2 &
                                            ⦃G, L.ⓛW1⦄ ⊢ T1 ➡[h, g] T2 &
                                            U1 = ⓛ{a}W1.T1 &
                                            U2 = ⓓ{a}ⓝW2.V2.T2 & I = Appl
                      | ∃∃a,V,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V & ⇧[0,1] V ≡ V2 &
                                              ⦃G, L⦄ ⊢ W1 ➡[h, g] W2 & ⦃G, L.ⓓW1⦄ ⊢ T1 ➡[h, g] T2 &
                                              U1 = ⓓ{a}W1.T1 &
                                              U2 = ⓓ{a}W2.ⓐV2.T2 & I = Appl.
/2 width=3 by cpx_inv_flat1_aux/ qed-.

lemma cpx_inv_appl1: ∀h,g,G,L,V1,U1,U2. ⦃G, L⦄ ⊢ ⓐ V1.U1 ➡[h, g] U2 →
                     ∨∨ ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 & ⦃G, L⦄ ⊢ U1 ➡[h, g] T2 &
                                 U2 = ⓐ V2. T2
                      | ∃∃a,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 & ⦃G, L⦄ ⊢ W1 ➡[h, g] W2 &
                                            ⦃G, L.ⓛW1⦄ ⊢ T1 ➡[h, g] T2 &
                                            U1 = ⓛ{a}W1.T1 & U2 = ⓓ{a}ⓝW2.V2.T2
                      | ∃∃a,V,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V & ⇧[0,1] V ≡ V2 &
                                              ⦃G, L⦄ ⊢ W1 ➡[h, g] W2 & ⦃G, L.ⓓW1⦄ ⊢ T1 ➡[h, g] T2 &
                                              U1 = ⓓ{a}W1.T1 & U2 = ⓓ{a}W2. ⓐV2. T2.
#h #g #G #L #V1 #U1 #U2 #H elim (cpx_inv_flat1 … H) -H *
[ /3 width=5/
|2,3: #_ #H destruct
| /3 width=11/
| /3 width=13/
]
qed-.

(* Note: the main property of simple terms *)
lemma cpx_inv_appl1_simple: ∀h,g,G,L,V1,T1,U. ⦃G, L⦄ ⊢ ⓐV1.T1 ➡[h, g] U → 𝐒⦃T1⦄ →
                            ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 & ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 &
                                     U = ⓐV2.T2.
#h #g #G #L #V1 #T1 #U #H #HT1
elim (cpx_inv_appl1 … H) -H *
[ /2 width=5/
| #a #V2 #W1 #W2 #U1 #U2 #_ #_ #_ #H #_ destruct
  elim (simple_inv_bind … HT1)
| #a #V #V2 #W1 #W2 #U1 #U2 #_ #_ #_ #_ #H #_ destruct
  elim (simple_inv_bind … HT1)
]
qed-.

lemma cpx_inv_cast1: ∀h,g,G,L,V1,U1,U2. ⦃G, L⦄ ⊢ ⓝV1.U1 ➡[h, g] U2 →
                     ∨∨ ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 & ⦃G, L⦄ ⊢ U1 ➡[h, g] T2 &
                                 U2 = ⓝ V2. T2
                      | ⦃G, L⦄ ⊢ U1 ➡[h, g] U2
                      | ⦃G, L⦄ ⊢ V1 ➡[h, g] U2.
#h #g #G #L #V1 #U1 #U2 #H elim (cpx_inv_flat1 … H) -H *
[ /3 width=5/
|2,3: /2 width=1/
| #a #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #H destruct
| #a #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #H destruct
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma cpx_fwd_bind1_minus: ∀h,g,I,G,L,V1,T1,T. ⦃G, L⦄ ⊢ -ⓑ{I}V1.T1 ➡[h, g] T → ∀b.
                           ∃∃V2,T2. ⦃G, L⦄ ⊢ ⓑ{b,I}V1.T1 ➡[h, g] ⓑ{b,I}V2.T2 &
                                    T = -ⓑ{I}V2.T2.
#h #g #I #G #L #V1 #T1 #T #H #b
elim (cpx_inv_bind1 … H) -H *
[ #V2 #T2 #HV12 #HT12 #H destruct /3 width=4/
| #T2 #_ #_ #H destruct
]
qed-.

lemma cpx_fwd_shift1: ∀h,g,G,L1,L,T1,T. ⦃G, L⦄ ⊢ L1 @@ T1 ➡[h, g] T →
                      ∃∃L2,T2. |L1| = |L2| & T = L2 @@ T2.
#h #g #G #L1 @(lenv_ind_dx … L1) -L1 normalize
[ #L #T1 #T #HT1
  @(ex2_2_intro … (⋆)) // (**) (* explicit constructor *)
| #I #L1 #V1 #IH #L #T1 #X
  >shift_append_assoc normalize #H
  elim (cpx_inv_bind1 … H) -H *
  [ #V0 #T0 #_ #HT10 #H destruct
    elim (IH … HT10) -IH -HT10 #L2 #T2 #HL12 #H destruct
    >append_length >HL12 -HL12
    @(ex2_2_intro … (⋆.ⓑ{I}V0@@L2) T2) [ >append_length ] // /2 width=3/ (**) (* explicit constructor *)
  | #T #_ #_ #H destruct
  ]
]
qed-.
