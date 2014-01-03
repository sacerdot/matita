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

include "ground_2/ynat/ynat_max.ma".
include "basic_2/notation/relations/extpsubst_6.ma".
include "basic_2/grammar/genv.ma".
include "basic_2/grammar/cl_shift.ma".
include "basic_2/relocation/ldrop_append.ma".
include "basic_2/relocation/lsuby.ma".

(* CONTEXT-SENSITIVE EXTENDED ORDINARY SUBSTITUTION FOR TERMS ***************)

(* activate genv *)
inductive cpy: ynat → ynat → relation4 genv lenv term term ≝
| cpy_atom : ∀I,G,L,d,e. cpy d e G L (⓪{I}) (⓪{I})
| cpy_subst: ∀I,G,L,K,V,W,i,d,e. d ≤ yinj i → i < d+e →
             ⇩[0, i] L ≡ K.ⓑ{I}V → ⇧[0, i+1] V ≡ W → cpy d e G L (#i) W
| cpy_bind : ∀a,I,G,L,V1,V2,T1,T2,d,e.
             cpy d e G L V1 V2 → cpy (⫯d) e G (L.ⓑ{I}V2) T1 T2 →
             cpy d e G L (ⓑ{a,I}V1.T1) (ⓑ{a,I}V2.T2)
| cpy_flat : ∀I,G,L,V1,V2,T1,T2,d,e.
             cpy d e G L V1 V2 → cpy d e G L T1 T2 →
             cpy d e G L (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
.

interpretation "context-sensitive extended ordinary substritution (term)"
   'ExtPSubst G L T1 d e T2 = (cpy d e G L T1 T2).

(* Basic properties *********************************************************)

lemma lsuby_cpy_trans: ∀G,d,e. lsub_trans … (cpy d e G) (lsuby d e). 
#G #d #e #L1 #T1 #T2 #H elim H -G -L1 -T1 -T2 -d -e
[ //
| #I #G #L1 #K1 #V #W #i #d #e #Hdi #Hide #HLK1 #HVW #L2 #HL12
  elim (lsuby_fwd_ldrop2_be … HL12 … HLK1) -HL12 -HLK1 /2 width=5 by cpy_subst/
| /4 width=1 by lsuby_succ, cpy_bind/
| /3 width=1 by cpy_flat/
]
qed-.

lemma cpy_refl: ∀G,T,L,d,e. ⦃G, L⦄ ⊢ T ▶×[d, e] T.
#G #T elim T -T // * /2 width=1 by cpy_bind, cpy_flat/
qed.

lemma cpy_full: ∀I,G,K,V,T1,L,d. ⇩[0, d] L ≡ K.ⓑ{I}V →
                ∃∃T2,T. ⦃G, L⦄ ⊢ T1 ▶×[d, 1] T2 & ⇧[d, 1] T ≡ T2.
#I #G #K #V #T1 elim T1 -T1
[ * #i #L #d #HLK
  /2 width=4 by lift_sort, lift_gref, ex2_2_intro/
  elim (lt_or_eq_or_gt i d) #Hid
  /3 width=4 by lift_lref_ge_minus, lift_lref_lt, ex2_2_intro/
  destruct
  elim (lift_total V 0 (i+1)) #W #HVW
  elim (lift_split … HVW i i)
  /4 width=5 by cpy_subst, ylt_inj, ex2_2_intro/
| * [ #a ] #J #W1 #U1 #IHW1 #IHU1 #L #d #HLK
  elim (IHW1 … HLK) -IHW1 #W2 #W #HW12 #HW2
  [ elim (IHU1 (L.ⓑ{J}W2) (d+1)) -IHU1
    /3 width=9 by cpy_bind, ldrop_ldrop, lift_bind, ex2_2_intro/
  | elim (IHU1 … HLK) -IHU1 -HLK
    /3 width=8 by cpy_flat, lift_flat, ex2_2_intro/
  ]
]
qed-.

lemma cpy_weak: ∀G,L,T1,T2,d1,e1. ⦃G, L⦄ ⊢ T1 ▶×[d1, e1] T2 →
                ∀d2,e2. d2 ≤ d1 → d1 + e1 ≤ d2 + e2 →
                ⦃G, L⦄ ⊢ T1 ▶×[d2, e2] T2.
#G #L #T1 #T2 #d1 #e1 #H elim H -G -L -T1 -T2 -d1 -e1 //
[ /3 width=5 by cpy_subst, ylt_yle_trans, yle_trans/
| /4 width=3 by cpy_bind, ylt_yle_trans, yle_succ/
| /3 width=1 by cpy_flat/
]
qed-.

lemma cpy_weak_top: ∀G,L,T1,T2,d,e.
                    ⦃G, L⦄ ⊢ T1 ▶×[d, e] T2 → ⦃G, L⦄ ⊢ T1 ▶×[d, |L| - d] T2.
#G #L #T1 #T2 #d #e #H elim H -G -L -T1 -T2 -d -e //
[ #I #G #L #K #V #W #i #d #e #Hdi #_ #HLK #HVW
  lapply (ldrop_fwd_length_lt2 … HLK)
  /4 width=5 by cpy_subst, ylt_yle_trans, ylt_inj/
| #a #I #G #L #V1 #V2 normalize in match (|L.ⓑ{I}V2|); (**) (* |?| does not work *)
  /2 width=1 by cpy_bind/
| /2 width=1 by cpy_flat/
]
qed-.

lemma cpy_weak_full: ∀G,L,T1,T2,d,e.
                     ⦃G, L⦄ ⊢ T1 ▶×[d, e] T2 → ⦃G, L⦄ ⊢ T1 ▶×[0, |L|] T2.
#G #L #T1 #T2 #d #e #HT12
lapply (cpy_weak … HT12 0 (d + e) ? ?) -HT12
/2 width=2 by cpy_weak_top/
qed-.

lemma cpy_split_up: ∀G,L,T1,T2,d,e. ⦃G, L⦄ ⊢ T1 ▶×[d, e] T2 → ∀i. i ≤ d + e →
                    ∃∃T. ⦃G, L⦄ ⊢ T1 ▶×[d, i-d] T & ⦃G, L⦄ ⊢ T ▶×[i, d+e-i] T2.
#G #L #T1 #T2 #d #e #H elim H -G -L -T1 -T2 -d -e
[ /2 width=3 by ex2_intro/
| #I #G #L #K #V #W #i #d #e #Hdi #Hide #HLK #HVW #j #Hjde
  elim (ylt_split i j) [ -Hide -Hjde | -Hdi ]
  /4 width=9 by cpy_subst, ylt_yle_trans, ex2_intro/
| #a #I #G #L #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #i #Hide
  elim (IHV12 i) -IHV12 // #V
  elim (IHT12 (i+1)) -IHT12 /2 width=1 by yle_succ/ -Hide
  >yplus_SO2 >yplus_succ1 #T #HT1 #HT2
  lapply (lsuby_cpy_trans … HT1 (L.ⓑ{I}V) ?) -HT1
  /3 width=5 by lsuby_succ, ex2_intro, cpy_bind/
| #I #G #L #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #i #Hide
  elim (IHV12 i) -IHV12 // elim (IHT12 i) -IHT12 // -Hide
  /3 width=5 by ex2_intro, cpy_flat/
]
qed-.

lemma cpy_split_down: ∀G,L,T1,T2,d,e. ⦃G, L⦄ ⊢ T1 ▶×[d, e] T2 → ∀i. i ≤ d + e →
                      ∃∃T. ⦃G, L⦄ ⊢ T1 ▶×[i, d+e-i] T & ⦃G, L⦄ ⊢ T ▶×[d, i-d] T2.
#G #L #T1 #T2 #d #e #H elim H -G -L -T1 -T2 -d -e
[ /2 width=3 by ex2_intro/
| #I #G #L #K #V #W #i #d #e #Hdi #Hide #HLK #HVW #j #Hjde
  elim (ylt_split i j) [ -Hide -Hjde | -Hdi ]
  /4 width=9 by cpy_subst, ylt_yle_trans, ex2_intro/
| #a #I #G #L #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #i #Hide
  elim (IHV12 i) -IHV12 // #V
  elim (IHT12 (i+1)) -IHT12 /2 width=1 by yle_succ/ -Hide
  >yplus_SO2 >yplus_succ1 #T #HT1 #HT2
  lapply (lsuby_cpy_trans … HT1 (L. ⓑ{I} V) ?) -HT1
  /3 width=5 by lsuby_succ, ex2_intro, cpy_bind/
| #I #G #L #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #i #Hide
  elim (IHV12 i) -IHV12 // elim (IHT12 i) -IHT12 // -Hide
  /3 width=5 by ex2_intro, cpy_flat/
]
qed-.

lemma cpy_append: ∀G,d,e. l_appendable_sn … (cpy d e G).
#G #d #e #K #T1 #T2 #H elim H -G -K -T1 -T2 -d -e
/2 width=1 by cpy_atom, cpy_bind, cpy_flat/
#I #G #K #K0 #V #W #i #d #e #Hdi #Hide #HK0 #HVW #L
lapply (ldrop_fwd_length_lt2 … HK0) #H
@(cpy_subst I … (L@@K0) … HVW) // (**) (* /4/ does not work *)
@(ldrop_O1_append_sn_le … HK0) /2 width=2 by lt_to_le/
qed-.

(* Basic inversion lemmas ***************************************************)

fact cpy_inv_atom1_aux: ∀G,L,T1,T2,d,e. ⦃G, L⦄ ⊢ T1 ▶×[d, e] T2 → ∀J. T1 = ⓪{J} →
                        T2 = ⓪{J} ∨
                        ∃∃I,K,V,i. d ≤ yinj i & i < d + e &
                                   ⇩[O, i] L ≡ K.ⓑ{I}V &
                                   ⇧[O, i + 1] V ≡ T2 &
                                   J = LRef i.
#G #L #T1 #T2 #d #e * -G -L -T1 -T2 -d -e
[ #I #G #L #d #e #J #H destruct /2 width=1 by or_introl/
| #I #G #L #K #V #T2 #i #d #e #Hdi #Hide #HLK #HVT2 #J #H destruct /3 width=9 by ex5_4_intro, or_intror/
| #a #I #G #L #V1 #V2 #T1 #T2 #d #e #_ #_ #J #H destruct
| #I #G #L #V1 #V2 #T1 #T2 #d #e #_ #_ #J #H destruct
]
qed-.

lemma cpy_inv_atom1: ∀I,G,L,T2,d,e. ⦃G, L⦄ ⊢ ⓪{I} ▶×[d, e] T2 →
                     T2 = ⓪{I} ∨
                     ∃∃J,K,V,i. d ≤ yinj i & i < d + e &
                                ⇩[O, i] L ≡ K.ⓑ{J}V &
                                ⇧[O, i + 1] V ≡ T2 &
                                I = LRef i.
/2 width=4 by cpy_inv_atom1_aux/ qed-.

lemma cpy_inv_sort1: ∀G,L,T2,k,d,e. ⦃G, L⦄ ⊢ ⋆k ▶×[d, e] T2 → T2 = ⋆k.
#G #L #T2 #k #d #e #H
elim (cpy_inv_atom1 … H) -H //
* #I #K #V #i #_ #_ #_ #_ #H destruct
qed-.

lemma cpy_inv_lref1: ∀G,L,T2,i,d,e. ⦃G, L⦄ ⊢ #i ▶×[d, e] T2 →
                     T2 = #i ∨
                     ∃∃I,K,V. d ≤ i & i < d + e &
                              ⇩[O, i] L ≡ K.ⓑ{I}V &
                              ⇧[O, i + 1] V ≡ T2.
#G #L #T2 #i #d #e #H
elim (cpy_inv_atom1 … H) -H /2 width=1 by or_introl/
* #I #K #V #j #Hdj #Hjde #HLK #HVT2 #H destruct /3 width=5 by ex4_3_intro, or_intror/
qed-.

lemma cpy_inv_gref1: ∀G,L,T2,p,d,e. ⦃G, L⦄ ⊢ §p ▶×[d, e] T2 → T2 = §p.
#G #L #T2 #p #d #e #H
elim (cpy_inv_atom1 … H) -H //
* #I #K #V #i #_ #_ #_ #_ #H destruct
qed-.

fact cpy_inv_bind1_aux: ∀G,L,U1,U2,d,e. ⦃G, L⦄ ⊢ U1 ▶×[d, e] U2 →
                        ∀a,I,V1,T1. U1 = ⓑ{a,I}V1.T1 →
                        ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ▶×[d, e] V2 &
                                 ⦃G, L. ⓑ{I}V2⦄ ⊢ T1 ▶×[⫯d, e] T2 &
                                 U2 = ⓑ{a,I}V2.T2.
#G #L #U1 #U2 #d #e * -G -L -U1 -U2 -d -e
[ #I #G #L #d #e #b #J #W1 #U1 #H destruct
| #I #G #L #K #V #W #i #d #e #_ #_ #_ #_ #b #J #W1 #U1 #H destruct
| #a #I #G #L #V1 #V2 #T1 #T2 #d #e #HV12 #HT12 #b #J #W1 #U1 #H destruct /2 width=5 by ex3_2_intro/
| #I #G #L #V1 #V2 #T1 #T2 #d #e #_ #_ #b #J #W1 #U1 #H destruct
]
qed-.

lemma cpy_inv_bind1: ∀a,I,G,L,V1,T1,U2,d,e. ⦃G, L⦄ ⊢ ⓑ{a,I} V1. T1 ▶×[d, e] U2 →
                     ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ▶×[d, e] V2 &
                              ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ▶×[⫯d, e] T2 &
                              U2 = ⓑ{a,I}V2.T2.
/2 width=3 by cpy_inv_bind1_aux/ qed-.

fact cpy_inv_flat1_aux: ∀G,L,U1,U2,d,e. ⦃G, L⦄ ⊢ U1 ▶×[d, e] U2 →
                        ∀I,V1,T1. U1 = ⓕ{I}V1.T1 →
                        ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ▶×[d, e] V2 &
                                 ⦃G, L⦄ ⊢ T1 ▶×[d, e] T2 &
                                 U2 = ⓕ{I}V2.T2.
#G #L #U1 #U2 #d #e * -G -L -U1 -U2 -d -e
[ #I #G #L #d #e #J #W1 #U1 #H destruct
| #I #G #L #K #V #W #i #d #e #_ #_ #_ #_ #J #W1 #U1 #H destruct
| #a #I #G #L #V1 #V2 #T1 #T2 #d #e #_ #_ #J #W1 #U1 #H destruct
| #I #G #L #V1 #V2 #T1 #T2 #d #e #HV12 #HT12 #J #W1 #U1 #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma cpy_inv_flat1: ∀I,G,L,V1,T1,U2,d,e. ⦃G, L⦄ ⊢ ⓕ{I} V1. T1 ▶×[d, e] U2 →
                     ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ▶×[d, e] V2 &
                              ⦃G, L⦄ ⊢ T1 ▶×[d, e] T2 &
                              U2 = ⓕ{I}V2.T2.
/2 width=3 by cpy_inv_flat1_aux/ qed-.


fact cpy_inv_refl_O2_aux: ∀G,L,T1,T2,d,e. ⦃G, L⦄ ⊢ T1 ▶×[d, e] T2 → e = 0 → T1 = T2.
#G #L #T1 #T2 #d #e #H elim H -G -L -T1 -T2 -d -e
[ //
| #I #G #L #K #V #W #i #d #e #Hdi #Hide #_ #_ #H destruct
  elim (ylt_yle_false … Hdi) -Hdi //
| /3 width=1 by eq_f2/
| /3 width=1 by eq_f2/
]
qed-.

lemma cpy_inv_refl_O2: ∀G,L,T1,T2,d. ⦃G, L⦄ ⊢ T1 ▶×[d, 0] T2 → T1 = T2.
/2 width=6 by cpy_inv_refl_O2_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma cpy_fwd_tw: ∀G,L,T1,T2,d,e. ⦃G, L⦄ ⊢ T1 ▶×[d, e] T2 → ♯{T1} ≤ ♯{T2}.
#G #L #T1 #T2 #d #e #H elim H -G -L -T1 -T2 -d -e normalize
/3 width=1 by monotonic_le_plus_l, le_plus/
qed-.

lemma cpy_fwd_shift1: ∀G,L1,L,T1,T,d,e. ⦃G, L⦄ ⊢ L1 @@ T1 ▶×[d, e] T →
                      ∃∃L2,T2. |L1| = |L2| & T = L2 @@ T2.
#G #L1 @(lenv_ind_dx … L1) -L1 normalize
[ #L #T1 #T #d #e #HT1
  @(ex2_2_intro … (⋆)) // (**) (* explicit constructor *)
| #I #L1 #V1 #IH #L #T1 #X #d #e
  >shift_append_assoc normalize #H
  elim (cpy_inv_bind1 … H) -H
  #V0 #T0 #_ #HT10 #H destruct
  elim (IH … HT10) -IH -HT10 #L2 #T2 #HL12 #H destruct
  >append_length >HL12 -HL12
  @(ex2_2_intro … (⋆.ⓑ{I}V0@@L2) T2) [ >append_length ] (**) (* explicit constructor *)
  /2 width=3 by trans_eq/
]
qed-.
