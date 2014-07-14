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
| cpx_st   : ∀G,L,k,l. deg h g k (l+1) → cpx h g G L (⋆k) (⋆(next h k))
| cpx_delta: ∀I,G,L,K,V,V2,W2,i.
             ⇩[i] L ≡ K.ⓑ{I}V → cpx h g G K V V2 →
             ⇧[0, i+1] V2 ≡ W2 → cpx h g G L (#i) W2
| cpx_bind : ∀a,I,G,L,V1,V2,T1,T2.
             cpx h g G L V1 V2 → cpx h g G (L.ⓑ{I}V1) T1 T2 →
             cpx h g G L (ⓑ{a,I}V1.T1) (ⓑ{a,I}V2.T2)
| cpx_flat : ∀I,G,L,V1,V2,T1,T2.
             cpx h g G L V1 V2 → cpx h g G L T1 T2 →
             cpx h g G L (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
| cpx_zeta : ∀G,L,V,T1,T,T2. cpx h g G (L.ⓓV) T1 T →
             ⇧[0, 1] T2 ≡ T → cpx h g G L (+ⓓV.T1) T2
| cpx_eps  : ∀G,L,V,T1,T2. cpx h g G L T1 T2 → cpx h g G L (ⓝV.T1) T2
| cpx_ct   : ∀G,L,V1,V2,T. cpx h g G L V1 V2 → cpx h g G L (ⓝV1.T) V2
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
| /2 width=2 by cpx_st/
| #I #G #L1 #K1 #V1 #V2 #W2 #i #HLK1 #_ #HVW2 #IHV12 #L2 #HL12
  elim (lsubr_fwd_drop2_pair … HL12 … HLK1) -HL12 -HLK1 *
  /4 width=7 by cpx_delta, cpx_ct/
|4,9: /4 width=1 by cpx_bind, cpx_beta, lsubr_pair/
|5,7,8: /3 width=1 by cpx_flat, cpx_eps, cpx_ct/
|6,10: /4 width=3 by cpx_zeta, cpx_theta, lsubr_pair/
]
qed-.

(* Note: this is "∀h,g,L. reflexive … (cpx h g L)" *)
lemma cpx_refl: ∀h,g,G,T,L. ⦃G, L⦄ ⊢ T ➡[h, g] T.
#h #g #G #T elim T -T // * /2 width=1 by cpx_bind, cpx_flat/
qed.

lemma cpr_cpx: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡ T2 → ⦃G, L⦄ ⊢ T1 ➡[h, g] T2.
#h #g #G #L #T1 #T2 #H elim H -L -T1 -T2
/2 width=7 by cpx_delta, cpx_bind, cpx_flat, cpx_zeta, cpx_eps, cpx_beta, cpx_theta/
qed.

lemma cpx_pair_sn: ∀h,g,I,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 →
                   ∀T. ⦃G, L⦄ ⊢ ②{I}V1.T ➡[h, g] ②{I}V2.T.
#h #g * /2 width=1 by cpx_bind, cpx_flat/
qed.

lemma cpx_delift: ∀h,g,I,G,K,V,T1,L,d. ⇩[d] L ≡ (K.ⓑ{I}V) →
                  ∃∃T2,T.  ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 & ⇧[d, 1] T ≡ T2.
#h #g #I #G #K #V #T1 elim T1 -T1
[ * #i #L #d /2 width=4 by cpx_atom, lift_sort, lift_gref, ex2_2_intro/
  elim (lt_or_eq_or_gt i d) #Hid [1,3: /3 width=4 by cpx_atom, lift_lref_ge_minus, lift_lref_lt, ex2_2_intro/ ]
  destruct
  elim (lift_total V 0 (i+1)) #W #HVW
  elim (lift_split … HVW i i) /3 width=7 by cpx_delta, ex2_2_intro/
| * [ #a ] #I #W1 #U1 #IHW1 #IHU1 #L #d #HLK
  elim (IHW1 … HLK) -IHW1 #W2 #W #HW12 #HW2
  [ elim (IHU1 (L. ⓑ{I} W1) (d+1)) -IHU1 /3 width=9 by cpx_bind, drop_drop, lift_bind, ex2_2_intro/
  | elim (IHU1 … HLK) -IHU1 -HLK /3 width=8 by cpx_flat, lift_flat, ex2_2_intro/
  ]
]
qed-.

(* Basic inversion lemmas ***************************************************)

fact cpx_inv_atom1_aux: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 → ∀J. T1 = ⓪{J} →
                        ∨∨ T2 = ⓪{J}
                         | ∃∃k,l. deg h g k (l+1) & T2 = ⋆(next h k) & J = Sort k
                         | ∃∃I,K,V,V2,i. ⇩[i] L ≡ K.ⓑ{I}V & ⦃G, K⦄ ⊢ V ➡[h, g] V2 &
                                         ⇧[O, i+1] V2 ≡ T2 & J = LRef i.
#G #h #g #L #T1 #T2 * -L -T1 -T2
[ #I #G #L #J #H destruct /2 width=1 by or3_intro0/
| #G #L #k #l #Hkl #J #H destruct /3 width=5 by or3_intro1, ex3_2_intro/
| #I #G #L #K #V #V2 #T2 #i #HLK #HV2 #HVT2 #J #H destruct /3 width=9 by or3_intro2, ex4_5_intro/
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
                      | ∃∃I,K,V,V2,i. ⇩[i] L ≡ K.ⓑ{I}V & ⦃G, K⦄ ⊢ V ➡[h, g] V2 &
                                      ⇧[O, i+1] V2 ≡ T2 & J = LRef i.
/2 width=3 by cpx_inv_atom1_aux/ qed-.

lemma cpx_inv_sort1: ∀h,g,G,L,T2,k. ⦃G, L⦄ ⊢ ⋆k ➡[h, g] T2 → T2 = ⋆k ∨
                     ∃∃l. deg h g k (l+1) & T2 = ⋆(next h k).
#h #g #G #L #T2 #k #H
elim (cpx_inv_atom1 … H) -H /2 width=1 by or_introl/ *
[ #k0 #l0 #Hkl0 #H1 #H2 destruct /3 width=4 by ex2_intro, or_intror/
| #I #K #V #V2 #i #_ #_ #_ #H destruct
]
qed-.

lemma cpx_inv_lref1: ∀h,g,G,L,T2,i. ⦃G, L⦄ ⊢ #i ➡[h, g] T2 →
                     T2 = #i ∨
                     ∃∃I,K,V,V2. ⇩[i] L ≡ K. ⓑ{I}V & ⦃G, K⦄ ⊢ V ➡[h, g] V2 &
                                 ⇧[O, i+1] V2 ≡ T2.
#h #g #G #L #T2 #i #H
elim (cpx_inv_atom1 … H) -H /2 width=1 by or_introl/ *
[ #k #l #_ #_ #H destruct
| #I #K #V #V2 #j #HLK #HV2 #HVT2 #H destruct /3 width=7 by ex3_4_intro, or_intror/
]
qed-.

lemma cpx_inv_lref1_ge: ∀h,g,G,L,T2,i. ⦃G, L⦄ ⊢ #i ➡[h, g] T2 → |L| ≤ i → T2 = #i.
#h #g #G #L #T2 #i #H elim (cpx_inv_lref1 … H) -H // *
#I #K #V1 #V2 #HLK #_ #_ #HL -h -G -V2 lapply (drop_fwd_length_lt2 … HLK) -K -I -V1
#H elim (lt_refl_false i) /2 width=3 by lt_to_le_to_lt/
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
| #a #I #G #L #V1 #V2 #T1 #T2 #HV12 #HT12 #b #J #W #U1 #H destruct /3 width=5 by ex3_2_intro, or_introl/
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #b #J #W #U1 #H destruct
| #G #L #V #T1 #T #T2 #HT1 #HT2 #b #J #W #U1 #H destruct /3 width=3 by ex4_intro, or_intror/
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
elim (cpx_inv_bind1 … H) -H * /3 width=5 by ex3_2_intro, ex3_intro, or_introl, or_intror/
qed-.

lemma cpx_inv_abst1: ∀h,g,a,G,L,V1,T1,U2.  ⦃G, L⦄ ⊢ ⓛ{a}V1.T1 ➡[h, g] U2 →
                     ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 &  ⦃G, L.ⓛV1⦄ ⊢ T1 ➡[h, g] T2 &
                              U2 = ⓛ{a} V2. T2.
#h #g #a #G #L #V1 #T1 #U2 #H
elim (cpx_inv_bind1 … H) -H *
[ /3 width=5 by ex3_2_intro/
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
| #I #G #L #V1 #V2 #T1 #T2 #HV12 #HT12 #J #W #U1 #H destruct /3 width=5 by or5_intro0, ex3_2_intro/
| #G #L #V #T1 #T #T2 #_ #_ #J #W #U1 #H destruct
| #G #L #V #T1 #T2 #HT12 #J #W #U1 #H destruct /3 width=1 by or5_intro1, conj/
| #G #L #V1 #V2 #T #HV12 #J #W #U1 #H destruct /3 width=1 by or5_intro2, conj/
| #a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HW12 #HT12 #J #W #U1 #H destruct /3 width=11 by or5_intro3, ex6_6_intro/
| #a #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 #HW12 #HT12 #J #W #U1 #H destruct /3 width=13 by or5_intro4, ex7_7_intro/
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
[ /3 width=5 by or3_intro0, ex3_2_intro/
|2,3: #_ #H destruct
| /3 width=11 by or3_intro1, ex5_6_intro/
| /3 width=13 by or3_intro2, ex6_7_intro/
]
qed-.

(* Note: the main property of simple terms *)
lemma cpx_inv_appl1_simple: ∀h,g,G,L,V1,T1,U. ⦃G, L⦄ ⊢ ⓐV1.T1 ➡[h, g] U → 𝐒⦃T1⦄ →
                            ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h, g] V2 & ⦃G, L⦄ ⊢ T1 ➡[h, g] T2 &
                                     U = ⓐV2.T2.
#h #g #G #L #V1 #T1 #U #H #HT1
elim (cpx_inv_appl1 … H) -H *
[ /2 width=5 by ex3_2_intro/
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
[ /3 width=5 by or3_intro0, ex3_2_intro/
|2,3: /2 width=1 by or3_intro1, or3_intro2/
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
[ #V2 #T2 #HV12 #HT12 #H destruct /3 width=4 by cpx_bind, ex2_2_intro/
| #T2 #_ #_ #H destruct
]
qed-.
