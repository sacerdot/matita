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

include "basic_2/notation/relations/pred_4.ma".
include "basic_2/grammar/genv.ma".
include "basic_2/static/lsubr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION FOR TERMS ***************************)

(* activate genv *)
(* Basic_1: includes: pr0_delta1 pr2_delta1 pr2_thin_dx *)
(* Note: cpr_flat: does not hold in basic_1 *)
inductive cpr: relation4 genv lenv term term ≝
| cpr_atom : ∀I,G,L. cpr G L (⓪{I}) (⓪{I})
| cpr_delta: ∀G,L,K,V,V2,W2,i.
             ⇩[i] L ≡ K. ⓓV → cpr G K V V2 →
             ⇧[0, i + 1] V2 ≡ W2 → cpr G L (#i) W2
| cpr_bind : ∀a,I,G,L,V1,V2,T1,T2.
             cpr G L V1 V2 → cpr G (L.ⓑ{I}V1) T1 T2 →
             cpr G L (ⓑ{a,I}V1.T1) (ⓑ{a,I}V2.T2)
| cpr_flat : ∀I,G,L,V1,V2,T1,T2.
             cpr G L V1 V2 → cpr G L T1 T2 →
             cpr G L (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
| cpr_zeta : ∀G,L,V,T1,T,T2. cpr G (L.ⓓV) T1 T →
             ⇧[0, 1] T2 ≡ T → cpr G L (+ⓓV.T1) T2
| cpr_eps  : ∀G,L,V,T1,T2. cpr G L T1 T2 → cpr G L (ⓝV.T1) T2
| cpr_beta : ∀a,G,L,V1,V2,W1,W2,T1,T2.
             cpr G L V1 V2 → cpr G L W1 W2 → cpr G (L.ⓛW1) T1 T2 →
             cpr G L (ⓐV1.ⓛ{a}W1.T1) (ⓓ{a}ⓝW2.V2.T2)
| cpr_theta: ∀a,G,L,V1,V,V2,W1,W2,T1,T2.
             cpr G L V1 V → ⇧[0, 1] V ≡ V2 → cpr G L W1 W2 → cpr G (L.ⓓW1) T1 T2 →
             cpr G L (ⓐV1.ⓓ{a}W1.T1) (ⓓ{a}W2.ⓐV2.T2)
.

interpretation "context-sensitive parallel reduction (term)"
   'PRed G L T1 T2 = (cpr G L T1 T2).

(* Basic properties *********************************************************)

lemma lsubr_cpr_trans: ∀G. lsub_trans … (cpr G) lsubr.
#G #L1 #T1 #T2 #H elim H -G -L1 -T1 -T2
[ //
| #G #L1 #K1 #V1 #V2 #W2 #i #HLK1 #_ #HVW2 #IHV12 #L2 #HL12
  elim (lsubr_fwd_drop2_abbr … HL12 … HLK1) -L1 *
  /3 width=6 by cpr_delta/
|3,7: /4 width=1 by lsubr_pair, cpr_bind, cpr_beta/
|4,6: /3 width=1 by cpr_flat, cpr_eps/
|5,8: /4 width=3 by lsubr_pair, cpr_zeta, cpr_theta/
]
qed-.

(* Basic_1: was by definition: pr2_free *)
lemma tpr_cpr: ∀G,T1,T2. ⦃G, ⋆⦄ ⊢ T1 ➡ T2 → ∀L. ⦃G, L⦄ ⊢ T1 ➡ T2.
#G #T1 #T2 #HT12 #L
lapply (lsubr_cpr_trans … HT12 L ?) //
qed.

(* Basic_1: includes by definition: pr0_refl *)
lemma cpr_refl: ∀G,T,L. ⦃G, L⦄ ⊢ T ➡ T.
#G #T elim T -T // * /2 width=1 by cpr_bind, cpr_flat/
qed.

(* Basic_1: was: pr2_head_1 *)
lemma cpr_pair_sn: ∀I,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡ V2 →
                   ∀T. ⦃G, L⦄ ⊢ ②{I}V1.T ➡ ②{I}V2.T.
* /2 width=1 by cpr_bind, cpr_flat/ qed.

lemma cpr_delift: ∀G,K,V,T1,L,d. ⇩[d] L ≡ (K.ⓓV) →
                  ∃∃T2,T. ⦃G, L⦄ ⊢ T1 ➡ T2 & ⇧[d, 1] T ≡ T2.
#G #K #V #T1 elim T1 -T1
[ * /2 width=4 by cpr_atom, lift_sort, lift_gref, ex2_2_intro/
  #i #L #d #HLK elim (lt_or_eq_or_gt i d)
  #Hid [1,3: /3 width=4 by cpr_atom, lift_lref_ge_minus, lift_lref_lt, ex2_2_intro/ ]
  destruct
  elim (lift_total V 0 (i+1)) #W #HVW
  elim (lift_split … HVW i i) /3 width=6 by cpr_delta, ex2_2_intro/
| * [ #a ] #I #W1 #U1 #IHW1 #IHU1 #L #d #HLK
  elim (IHW1 … HLK) -IHW1 #W2 #W #HW12 #HW2
  [ elim (IHU1 (L. ⓑ{I}W1) (d+1)) -IHU1 /3 width=9 by drop_drop, cpr_bind, lift_bind, ex2_2_intro/
  | elim (IHU1 … HLK) -IHU1 -HLK /3 width=8 by cpr_flat, lift_flat, ex2_2_intro/
  ]
]
qed-.

(* Basic inversion lemmas ***************************************************)

fact cpr_inv_atom1_aux: ∀G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡ T2 → ∀I. T1 = ⓪{I} →
                        T2 = ⓪{I} ∨
                        ∃∃K,V,V2,i. ⇩[i] L ≡ K. ⓓV & ⦃G, K⦄ ⊢ V ➡ V2 &
                                    ⇧[O, i + 1] V2 ≡ T2 & I = LRef i.
#G #L #T1 #T2 * -G -L -T1 -T2
[ #I #G #L #J #H destruct /2 width=1 by or_introl/
| #L #G #K #V #V2 #T2 #i #HLK #HV2 #HVT2 #J #H destruct /3 width=8 by ex4_4_intro, or_intror/
| #a #I #G #L #V1 #V2 #T1 #T2 #_ #_ #J #H destruct
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #J #H destruct
| #G #L #V #T1 #T #T2 #_ #_ #J #H destruct
| #G #L #V #T1 #T2 #_ #J #H destruct
| #a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #J #H destruct
| #a #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #J #H destruct
]
qed-.

lemma cpr_inv_atom1: ∀I,G,L,T2. ⦃G, L⦄ ⊢ ⓪{I} ➡ T2 →
                     T2 = ⓪{I} ∨
                     ∃∃K,V,V2,i. ⇩[i] L ≡ K. ⓓV & ⦃G, K⦄ ⊢ V ➡ V2 &
                                 ⇧[O, i + 1] V2 ≡ T2 & I = LRef i.
/2 width=3 by cpr_inv_atom1_aux/ qed-.

(* Basic_1: includes: pr0_gen_sort pr2_gen_sort *)
lemma cpr_inv_sort1: ∀G,L,T2,k. ⦃G, L⦄ ⊢ ⋆k ➡ T2 → T2 = ⋆k.
#G #L #T2 #k #H
elim (cpr_inv_atom1 … H) -H //
* #K #V #V2 #i #_ #_ #_ #H destruct
qed-.

(* Basic_1: includes: pr0_gen_lref pr2_gen_lref *)
lemma cpr_inv_lref1: ∀G,L,T2,i. ⦃G, L⦄ ⊢ #i ➡ T2 →
                     T2 = #i ∨
                     ∃∃K,V,V2. ⇩[i] L ≡ K. ⓓV & ⦃G, K⦄ ⊢ V ➡ V2 &
                               ⇧[O, i + 1] V2 ≡ T2.
#G #L #T2 #i #H
elim (cpr_inv_atom1 … H) -H /2 width=1 by or_introl/
* #K #V #V2 #j #HLK #HV2 #HVT2 #H destruct /3 width=6 by ex3_3_intro, or_intror/
qed-.

lemma cpr_inv_gref1: ∀G,L,T2,p. ⦃G, L⦄ ⊢ §p ➡ T2 → T2 = §p.
#G #L #T2 #p #H
elim (cpr_inv_atom1 … H) -H //
* #K #V #V2 #i #_ #_ #_ #H destruct
qed-.

fact cpr_inv_bind1_aux: ∀G,L,U1,U2. ⦃G, L⦄ ⊢ U1 ➡ U2 →
                        ∀a,I,V1,T1. U1 = ⓑ{a,I}V1. T1 → (
                        ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡ V2 & ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ➡ T2 &
                                 U2 = ⓑ{a,I}V2.T2
                        ) ∨
                        ∃∃T. ⦃G, L.ⓓV1⦄ ⊢ T1 ➡ T & ⇧[0, 1] U2 ≡ T &
                             a = true & I = Abbr.
#G #L #U1 #U2 * -L -U1 -U2
[ #I #G #L #b #J #W1 #U1 #H destruct
| #L #G #K #V #V2 #W2 #i #_ #_ #_ #b #J #W #U1 #H destruct
| #a #I #G #L #V1 #V2 #T1 #T2 #HV12 #HT12 #b #J #W #U1 #H destruct /3 width=5 by ex3_2_intro, or_introl/
| #I #G #L #V1 #V2 #T1 #T2 #_ #_ #b #J #W #U1 #H destruct
| #G #L #V #T1 #T #T2 #HT1 #HT2 #b #J #W #U1 #H destruct /3 width=3 by ex4_intro, or_intror/
| #G #L #V #T1 #T2 #_ #b #J #W #U1 #H destruct
| #a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #b #J #W #U1 #H destruct
| #a #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #b #J #W #U1 #H destruct
]
qed-.

lemma cpr_inv_bind1: ∀a,I,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡ U2 → (
                     ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡ V2 & ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ➡ T2 &
                              U2 = ⓑ{a,I}V2.T2
                     ) ∨
                     ∃∃T. ⦃G, L.ⓓV1⦄ ⊢ T1 ➡ T & ⇧[0, 1] U2 ≡ T &
                          a = true & I = Abbr.
/2 width=3 by cpr_inv_bind1_aux/ qed-.

(* Basic_1: includes: pr0_gen_abbr pr2_gen_abbr *)
lemma cpr_inv_abbr1: ∀a,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓓ{a}V1.T1 ➡ U2 → (
                     ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡ V2 & ⦃G, L. ⓓV1⦄ ⊢ T1 ➡ T2 &
                              U2 = ⓓ{a}V2.T2
                     ) ∨
                     ∃∃T. ⦃G, L.ⓓV1⦄ ⊢ T1 ➡ T & ⇧[0, 1] U2 ≡ T & a = true.
#a #G #L #V1 #T1 #U2 #H
elim (cpr_inv_bind1 … H) -H *
/3 width=5 by ex3_2_intro, ex3_intro, or_introl, or_intror/
qed-.

(* Basic_1: includes: pr0_gen_abst pr2_gen_abst *)
lemma cpr_inv_abst1: ∀a,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓛ{a}V1.T1 ➡ U2 →
                     ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡ V2 & ⦃G, L.ⓛV1⦄ ⊢ T1 ➡ T2 &
                              U2 = ⓛ{a}V2.T2.
#a #G #L #V1 #T1 #U2 #H
elim (cpr_inv_bind1 … H) -H *
[ /3 width=5 by ex3_2_intro/
| #T #_ #_ #_ #H destruct
]
qed-.

fact cpr_inv_flat1_aux: ∀G,L,U,U2. ⦃G, L⦄ ⊢ U ➡ U2 →
                        ∀I,V1,U1. U = ⓕ{I}V1.U1 →
                        ∨∨ ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡ V2 & ⦃G, L⦄ ⊢ U1 ➡ T2 &
                                    U2 = ⓕ{I} V2. T2
                         | (⦃G, L⦄ ⊢ U1 ➡ U2 ∧ I = Cast)
                         | ∃∃a,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡ V2 & ⦃G, L⦄ ⊢ W1 ➡ W2 &
                                               ⦃G, L.ⓛW1⦄ ⊢ T1 ➡ T2 & U1 = ⓛ{a}W1.T1 &
                                               U2 = ⓓ{a}ⓝW2.V2.T2 & I = Appl
                         | ∃∃a,V,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡ V & ⇧[0,1] V ≡ V2 &
                                                 ⦃G, L⦄ ⊢ W1 ➡ W2 & ⦃G, L.ⓓW1⦄ ⊢ T1 ➡ T2 &
                                                 U1 = ⓓ{a}W1.T1 &
                                                 U2 = ⓓ{a}W2.ⓐV2.T2 & I = Appl.
#G #L #U #U2 * -L -U -U2
[ #I #G #L #J #W1 #U1 #H destruct
| #G #L #K #V #V2 #W2 #i #_ #_ #_ #J #W #U1 #H destruct
| #a #I #G #L #V1 #V2 #T1 #T2 #_ #_ #J #W #U1 #H destruct
| #I #G #L #V1 #V2 #T1 #T2 #HV12 #HT12 #J #W #U1 #H destruct /3 width=5 by or4_intro0, ex3_2_intro/
| #G #L #V #T1 #T #T2 #_ #_ #J #W #U1 #H destruct
| #G #L #V #T1 #T2 #HT12 #J #W #U1 #H destruct /3 width=1 by or4_intro1, conj/
| #a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HW12 #HT12 #J #W #U1 #H destruct /3 width=11 by or4_intro2, ex6_6_intro/
| #a #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 #HW12 #HT12 #J #W #U1 #H destruct /3 width=13 by or4_intro3, ex7_7_intro/
]
qed-.

lemma cpr_inv_flat1: ∀I,G,L,V1,U1,U2. ⦃G, L⦄ ⊢ ⓕ{I}V1.U1 ➡ U2 →
                     ∨∨ ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡ V2 & ⦃G, L⦄ ⊢ U1 ➡ T2 &
                                 U2 = ⓕ{I}V2.T2
                      | (⦃G, L⦄ ⊢ U1 ➡ U2 ∧ I = Cast)
                      | ∃∃a,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡ V2 & ⦃G, L⦄ ⊢ W1 ➡ W2 &
                                            ⦃G, L.ⓛW1⦄ ⊢ T1 ➡ T2 & U1 = ⓛ{a}W1.T1 &
                                            U2 = ⓓ{a}ⓝW2.V2.T2 & I = Appl
                      | ∃∃a,V,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡ V & ⇧[0,1] V ≡ V2 &
                                              ⦃G, L⦄ ⊢ W1 ➡ W2 & ⦃G, L.ⓓW1⦄ ⊢ T1 ➡ T2 &
                                              U1 = ⓓ{a}W1.T1 &
                                              U2 = ⓓ{a}W2.ⓐV2.T2 & I = Appl.
/2 width=3 by cpr_inv_flat1_aux/ qed-.

(* Basic_1: includes: pr0_gen_appl pr2_gen_appl *)
lemma cpr_inv_appl1: ∀G,L,V1,U1,U2. ⦃G, L⦄ ⊢ ⓐV1.U1 ➡ U2 →
                     ∨∨ ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡ V2 & ⦃G, L⦄ ⊢ U1 ➡ T2 &
                                 U2 = ⓐV2.T2
                      | ∃∃a,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡ V2 & ⦃G, L⦄ ⊢ W1 ➡ W2 &
                                            ⦃G, L.ⓛW1⦄ ⊢ T1 ➡ T2 &
                                            U1 = ⓛ{a}W1.T1 & U2 = ⓓ{a}ⓝW2.V2.T2
                      | ∃∃a,V,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡ V & ⇧[0,1] V ≡ V2 &
                                              ⦃G, L⦄ ⊢ W1 ➡ W2 & ⦃G, L.ⓓW1⦄ ⊢ T1 ➡ T2 &
                                              U1 = ⓓ{a}W1.T1 & U2 = ⓓ{a}W2.ⓐV2.T2.
#G #L #V1 #U1 #U2 #H elim (cpr_inv_flat1 … H) -H *
[ /3 width=5 by or3_intro0, ex3_2_intro/
| #_ #H destruct
| /3 width=11 by or3_intro1, ex5_6_intro/
| /3 width=13 by or3_intro2, ex6_7_intro/
]
qed-.

(* Note: the main property of simple terms *)
lemma cpr_inv_appl1_simple: ∀G,L,V1,T1,U. ⦃G, L⦄ ⊢ ⓐV1. T1 ➡ U → 𝐒⦃T1⦄ →
                            ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡ V2 & ⦃G, L⦄ ⊢ T1 ➡ T2 &
                                     U = ⓐV2. T2.
#G #L #V1 #T1 #U #H #HT1
elim (cpr_inv_appl1 … H) -H *
[ /2 width=5/
| #a #V2 #W1 #W2 #U1 #U2 #_ #_ #_ #H #_ destruct
  elim (simple_inv_bind … HT1)
| #a #V #V2 #W1 #W2 #U1 #U2 #_ #_ #_ #_ #H #_ destruct
  elim (simple_inv_bind … HT1)
]
qed-.

(* Basic_1: includes: pr0_gen_cast pr2_gen_cast *)
lemma cpr_inv_cast1: ∀G,L,V1,U1,U2. ⦃G, L⦄ ⊢ ⓝ V1. U1 ➡ U2 → (
                     ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡ V2 & ⦃G, L⦄ ⊢ U1 ➡ T2 &
                              U2 = ⓝ V2. T2
                     ) ∨ ⦃G, L⦄ ⊢ U1 ➡ U2.
#G #L #V1 #U1 #U2 #H elim (cpr_inv_flat1 … H) -H *
[ /3 width=5 by ex3_2_intro, or_introl/
| /2 width=1 by or_intror/
| #a #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #H destruct
| #a #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #_ #_ #_ #H destruct
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma cpr_fwd_bind1_minus: ∀I,G,L,V1,T1,T. ⦃G, L⦄ ⊢ -ⓑ{I}V1.T1 ➡ T → ∀b.
                           ∃∃V2,T2. ⦃G, L⦄ ⊢ ⓑ{b,I}V1.T1 ➡ ⓑ{b,I}V2.T2 &
                                    T = -ⓑ{I}V2.T2.
#I #G #L #V1 #T1 #T #H #b
elim (cpr_inv_bind1 … H) -H *
[ #V2 #T2 #HV12 #HT12 #H destruct /3 width=4 by cpr_bind, ex2_2_intro/
| #T2 #_ #_ #H destruct
]
qed-.

(* Basic_1: removed theorems 11:
            pr0_subst0_back pr0_subst0_fwd pr0_subst0
            pr2_head_2 pr2_cflat clear_pr2_trans
            pr2_gen_csort pr2_gen_cflat pr2_gen_cbind
            pr2_gen_ctail pr2_ctail
*)
(* Basic_1: removed local theorems 4:
            pr0_delta_eps pr0_cong_delta
            pr2_free_free pr2_free_delta
*)
