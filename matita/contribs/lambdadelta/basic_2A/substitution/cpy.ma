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

include "ground_2A/ynat/ynat_max.ma".
include "basic_2A/notation/relations/psubst_6.ma".
include "basic_2A/grammar/genv.ma".
include "basic_2A/substitution/lsuby.ma".

(* CONTEXT-SENSITIVE EXTENDED ORDINARY SUBSTITUTION FOR TERMS ***************)

(* activate genv *)
inductive cpy: ynat → ynat → relation4 genv lenv term term ≝
| cpy_atom : ∀I,G,L,l,m. cpy l m G L (⓪{I}) (⓪{I})
| cpy_subst: ∀I,G,L,K,V,W,i,l,m. l ≤ yinj i → i < l+m →
             ⬇[i] L ≡ K.ⓑ{I}V → ⬆[0, i+1] V ≡ W → cpy l m G L (#i) W
| cpy_bind : ∀a,I,G,L,V1,V2,T1,T2,l,m.
             cpy l m G L V1 V2 → cpy (⫯l) m G (L.ⓑ{I}V1) T1 T2 →
             cpy l m G L (ⓑ{a,I}V1.T1) (ⓑ{a,I}V2.T2)
| cpy_flat : ∀I,G,L,V1,V2,T1,T2,l,m.
             cpy l m G L V1 V2 → cpy l m G L T1 T2 →
             cpy l m G L (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
.

interpretation "context-sensitive extended ordinary substritution (term)"
   'PSubst G L T1 l m T2 = (cpy l m G L T1 T2).

(* Basic properties *********************************************************)

lemma lsuby_cpy_trans: ∀G,l,m. lsub_trans … (cpy l m G) (lsuby l m).
#G #l #m #L1 #T1 #T2 #H elim H -G -L1 -T1 -T2 -l -m
[ //
| #I #G #L1 #K1 #V #W #i #l #m #Hli #Hilm #HLK1 #HVW #L2 #HL12
  elim (lsuby_drop_trans_be … HL12 … HLK1) -HL12 -HLK1 /2 width=5 by cpy_subst/
| /4 width=1 by lsuby_succ, cpy_bind/
| /3 width=1 by cpy_flat/
]
qed-.

lemma cpy_refl: ∀G,T,L,l,m. ⦃G, L⦄ ⊢ T ▶[l, m] T.
#G #T elim T -T // * /2 width=1 by cpy_bind, cpy_flat/
qed.

(* Basic_1: was: subst1_ex *)
lemma cpy_full: ∀I,G,K,V,T1,L,l. ⬇[l] L ≡ K.ⓑ{I}V →
                ∃∃T2,T. ⦃G, L⦄ ⊢ T1 ▶[l, 1] T2 & ⬆[l, 1] T ≡ T2.
#I #G #K #V #T1 elim T1 -T1
[ * #i #L #l #HLK
  /2 width=4 by lift_sort, lift_gref, ex2_2_intro/
  elim (lt_or_eq_or_gt i l) #Hil
  /3 width=4 by lift_lref_ge_minus, lift_lref_lt, ex2_2_intro/
  destruct
  elim (lift_total V 0 (i+1)) #W #HVW
  elim (lift_split … HVW i i)
  /4 width=5 by cpy_subst, ylt_inj, ex2_2_intro/
| * [ #a ] #J #W1 #U1 #IHW1 #IHU1 #L #l #HLK
  elim (IHW1 … HLK) -IHW1 #W2 #W #HW12 #HW2
  [ elim (IHU1 (L.ⓑ{J}W1) (l+1)) -IHU1
    /3 width=9 by cpy_bind, drop_drop, lift_bind, ex2_2_intro/
  | elim (IHU1 … HLK) -IHU1 -HLK
    /3 width=8 by cpy_flat, lift_flat, ex2_2_intro/
  ]
]
qed-.

lemma cpy_weak: ∀G,L,T1,T2,l1,m1. ⦃G, L⦄ ⊢ T1 ▶[l1, m1] T2 →
                ∀l2,m2. l2 ≤ l1 → l1 + m1 ≤ l2 + m2 →
                ⦃G, L⦄ ⊢ T1 ▶[l2, m2] T2.
#G #L #T1 #T2 #l1 #m1 #H elim H -G -L -T1 -T2 -l1 -m1 //
[ /3 width=5 by cpy_subst, ylt_yle_trans, yle_trans/
| /4 width=3 by cpy_bind, ylt_yle_trans, yle_succ/
| /3 width=1 by cpy_flat/
]
qed-.

lemma cpy_weak_top: ∀G,L,T1,T2,l,m.
                    ⦃G, L⦄ ⊢ T1 ▶[l, m] T2 → ⦃G, L⦄ ⊢ T1 ▶[l, |L| - l] T2.
#G #L #T1 #T2 #l #m #H elim H -G -L -T1 -T2 -l -m //
[ #I #G #L #K #V #W #i #l #m #Hli #_ #HLK #HVW
  lapply (drop_fwd_length_lt2 … HLK)
  /4 width=5 by cpy_subst, ylt_yle_trans, ylt_inj/
| #a #I #G #L #V1 #V2 normalize in match (|L.ⓑ{I}V2|); (**) (* |?| does not work *)
  /2 width=1 by cpy_bind/
| /2 width=1 by cpy_flat/
]
qed-.

lemma cpy_weak_full: ∀G,L,T1,T2,l,m.
                     ⦃G, L⦄ ⊢ T1 ▶[l, m] T2 → ⦃G, L⦄ ⊢ T1 ▶[0, |L|] T2.
#G #L #T1 #T2 #l #m #HT12
lapply (cpy_weak … HT12 0 (l + m) ? ?) -HT12
/2 width=2 by cpy_weak_top/
qed-.

lemma cpy_split_up: ∀G,L,T1,T2,l,m. ⦃G, L⦄ ⊢ T1 ▶[l, m] T2 → ∀i. i ≤ l + m →
                    ∃∃T. ⦃G, L⦄ ⊢ T1 ▶[l, i-l] T & ⦃G, L⦄ ⊢ T ▶[i, l+m-i] T2.
#G #L #T1 #T2 #l #m #H elim H -G -L -T1 -T2 -l -m
[ /2 width=3 by ex2_intro/
| #I #G #L #K #V #W #i #l #m #Hli #Hilm #HLK #HVW #j #Hjlm
  elim (ylt_split i j) [ -Hilm -Hjlm | -Hli ]
  /4 width=9 by cpy_subst, ylt_yle_trans, ex2_intro/
| #a #I #G #L #V1 #V2 #T1 #T2 #l #m #_ #_ #IHV12 #IHT12 #i #Hilm
  elim (IHV12 i) -IHV12 // #V
  elim (IHT12 (i+1)) -IHT12 /2 width=1 by yle_succ/ -Hilm
  >yplus_SO2 >yplus_succ1 #T #HT1 #HT2
  lapply (lsuby_cpy_trans … HT2 (L.ⓑ{I}V) ?) -HT2
  /3 width=5 by lsuby_succ, ex2_intro, cpy_bind/
| #I #G #L #V1 #V2 #T1 #T2 #l #m #_ #_ #IHV12 #IHT12 #i #Hilm
  elim (IHV12 i) -IHV12 // elim (IHT12 i) -IHT12 // -Hilm
  /3 width=5 by ex2_intro, cpy_flat/
]
qed-.

lemma cpy_split_down: ∀G,L,T1,T2,l,m. ⦃G, L⦄ ⊢ T1 ▶[l, m] T2 → ∀i. i ≤ l + m →
                      ∃∃T. ⦃G, L⦄ ⊢ T1 ▶[i, l+m-i] T & ⦃G, L⦄ ⊢ T ▶[l, i-l] T2.
#G #L #T1 #T2 #l #m #H elim H -G -L -T1 -T2 -l -m
[ /2 width=3 by ex2_intro/
| #I #G #L #K #V #W #i #l #m #Hli #Hilm #HLK #HVW #j #Hjlm
  elim (ylt_split i j) [ -Hilm -Hjlm | -Hli ]
  /4 width=9 by cpy_subst, ylt_yle_trans, ex2_intro/
| #a #I #G #L #V1 #V2 #T1 #T2 #l #m #_ #_ #IHV12 #IHT12 #i #Hilm
  elim (IHV12 i) -IHV12 // #V
  elim (IHT12 (i+1)) -IHT12 /2 width=1 by yle_succ/ -Hilm
  >yplus_SO2 >yplus_succ1 #T #HT1 #HT2
  lapply (lsuby_cpy_trans … HT2 (L.ⓑ{I}V) ?) -HT2
  /3 width=5 by lsuby_succ, ex2_intro, cpy_bind/
| #I #G #L #V1 #V2 #T1 #T2 #l #m #_ #_ #IHV12 #IHT12 #i #Hilm
  elim (IHV12 i) -IHV12 // elim (IHT12 i) -IHT12 // -Hilm
  /3 width=5 by ex2_intro, cpy_flat/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma cpy_fwd_up: ∀G,L,U1,U2,lt,mt. ⦃G, L⦄ ⊢ U1 ▶[lt, mt] U2 →
                  ∀T1,l,m. ⬆[l, m] T1 ≡ U1 →
                  l ≤ lt → l + m ≤ lt + mt →
                  ∃∃T2. ⦃G, L⦄ ⊢ U1 ▶[l+m, lt+mt-(l+m)] U2 & ⬆[l, m] T2 ≡ U2.
#G #L #U1 #U2 #lt #mt #H elim H -G -L -U1 -U2 -lt -mt
[ * #i #G #L #lt #mt #T1 #l #m #H #_
  [ lapply (lift_inv_sort2 … H) -H #H destruct /2 width=3 by ex2_intro/
  | elim (lift_inv_lref2 … H) -H * #Hil #H destruct /3 width=3 by lift_lref_ge_minus, lift_lref_lt, ex2_intro/
  | lapply (lift_inv_gref2 … H) -H #H destruct /2 width=3 by ex2_intro/
  ]
| #I #G #L #K #V #W #i #lt #mt #Hlti #Hilmt #HLK #HVW #T1 #l #m #H #Hllt #Hlmlmt
  elim (lift_inv_lref2 … H) -H * #Hil #H destruct [ -V -Hilmt -Hlmlmt | -Hlti -Hllt ]
  [ elim (ylt_yle_false … Hllt) -Hllt /3 width=3 by yle_ylt_trans, ylt_inj/
  | elim (le_inv_plus_l … Hil) #Hlim #Hmi
    elim (lift_split … HVW l (i-m+1) ? ? ?) [2,3,4: /2 width=1 by le_S_S, le_S/ ] -Hlim
    #T2 #_ >plus_minus // <minus_minus /2 width=1 by le_S/ <minus_n_n <plus_n_O #H -Hmi
    @(ex2_intro … H) -H @(cpy_subst … HLK HVW) /2 width=1 by yle_inj/ >ymax_pre_sn_comm // (**) (* explicit constructor *)
  ]
| #a #I #G #L #W1 #W2 #U1 #U2 #lt #mt #_ #_ #IHW12 #IHU12 #X #l #m #H #Hllt #Hlmlmt
  elim (lift_inv_bind2 … H) -H #V1 #T1 #HVW1 #HTU1 #H destruct
  elim (IHW12 … HVW1) -V1 -IHW12 //
  elim (IHU12 … HTU1) -T1 -IHU12 /2 width=1 by yle_succ/
  <yplus_inj >yplus_SO2 >yplus_succ1 >yplus_succ1
  /3 width=2 by cpy_bind, lift_bind, ex2_intro/
| #I #G #L #W1 #W2 #U1 #U2 #lt #mt #_ #_ #IHW12 #IHU12 #X #l #m #H #Hllt #Hlmlmt
  elim (lift_inv_flat2 … H) -H #V1 #T1 #HVW1 #HTU1 #H destruct
  elim (IHW12 … HVW1) -V1 -IHW12 // elim (IHU12 … HTU1) -T1 -IHU12
  /3 width=2 by cpy_flat, lift_flat, ex2_intro/
]
qed-.

lemma cpy_fwd_tw: ∀G,L,T1,T2,l,m. ⦃G, L⦄ ⊢ T1 ▶[l, m] T2 → ♯{T1} ≤ ♯{T2}.
#G #L #T1 #T2 #l #m #H elim H -G -L -T1 -T2 -l -m normalize
/3 width=1 by monotonic_le_plus_l, le_plus/
qed-.

(* Basic inversion lemmas ***************************************************)

fact cpy_inv_atom1_aux: ∀G,L,T1,T2,l,m. ⦃G, L⦄ ⊢ T1 ▶[l, m] T2 → ∀J. T1 = ⓪{J} →
                        T2 = ⓪{J} ∨
                        ∃∃I,K,V,i. l ≤ yinj i & i < l + m &
                                   ⬇[i] L ≡ K.ⓑ{I}V &
                                   ⬆[O, i+1] V ≡ T2 &
                                   J = LRef i.
#G #L #T1 #T2 #l #m * -G -L -T1 -T2 -l -m
[ #I #G #L #l #m #J #H destruct /2 width=1 by or_introl/
| #I #G #L #K #V #T2 #i #l #m #Hli #Hilm #HLK #HVT2 #J #H destruct /3 width=9 by ex5_4_intro, or_intror/
| #a #I #G #L #V1 #V2 #T1 #T2 #l #m #_ #_ #J #H destruct
| #I #G #L #V1 #V2 #T1 #T2 #l #m #_ #_ #J #H destruct
]
qed-.

lemma cpy_inv_atom1: ∀I,G,L,T2,l,m. ⦃G, L⦄ ⊢ ⓪{I} ▶[l, m] T2 →
                     T2 = ⓪{I} ∨
                     ∃∃J,K,V,i. l ≤ yinj i & i < l + m &
                                ⬇[i] L ≡ K.ⓑ{J}V &
                                ⬆[O, i+1] V ≡ T2 &
                                I = LRef i.
/2 width=4 by cpy_inv_atom1_aux/ qed-.

(* Basic_1: was: subst1_gen_sort *)
lemma cpy_inv_sort1: ∀G,L,T2,k,l,m. ⦃G, L⦄ ⊢ ⋆k ▶[l, m] T2 → T2 = ⋆k.
#G #L #T2 #k #l #m #H
elim (cpy_inv_atom1 … H) -H //
* #I #K #V #i #_ #_ #_ #_ #H destruct
qed-.

(* Basic_1: was: subst1_gen_lref *)
lemma cpy_inv_lref1: ∀G,L,T2,i,l,m. ⦃G, L⦄ ⊢ #i ▶[l, m] T2 →
                     T2 = #i ∨
                     ∃∃I,K,V. l ≤ i & i < l + m &
                              ⬇[i] L ≡ K.ⓑ{I}V &
                              ⬆[O, i+1] V ≡ T2.
#G #L #T2 #i #l #m #H
elim (cpy_inv_atom1 … H) -H /2 width=1 by or_introl/
* #I #K #V #j #Hlj #Hjlm #HLK #HVT2 #H destruct /3 width=5 by ex4_3_intro, or_intror/
qed-.

lemma cpy_inv_gref1: ∀G,L,T2,p,l,m. ⦃G, L⦄ ⊢ §p ▶[l, m] T2 → T2 = §p.
#G #L #T2 #p #l #m #H
elim (cpy_inv_atom1 … H) -H //
* #I #K #V #i #_ #_ #_ #_ #H destruct
qed-.

fact cpy_inv_bind1_aux: ∀G,L,U1,U2,l,m. ⦃G, L⦄ ⊢ U1 ▶[l, m] U2 →
                        ∀a,I,V1,T1. U1 = ⓑ{a,I}V1.T1 →
                        ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ▶[l, m] V2 &
                                 ⦃G, L. ⓑ{I}V1⦄ ⊢ T1 ▶[⫯l, m] T2 &
                                 U2 = ⓑ{a,I}V2.T2.
#G #L #U1 #U2 #l #m * -G -L -U1 -U2 -l -m
[ #I #G #L #l #m #b #J #W1 #U1 #H destruct
| #I #G #L #K #V #W #i #l #m #_ #_ #_ #_ #b #J #W1 #U1 #H destruct
| #a #I #G #L #V1 #V2 #T1 #T2 #l #m #HV12 #HT12 #b #J #W1 #U1 #H destruct /2 width=5 by ex3_2_intro/
| #I #G #L #V1 #V2 #T1 #T2 #l #m #_ #_ #b #J #W1 #U1 #H destruct
]
qed-.

lemma cpy_inv_bind1: ∀a,I,G,L,V1,T1,U2,l,m. ⦃G, L⦄ ⊢ ⓑ{a,I} V1. T1 ▶[l, m] U2 →
                     ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ▶[l, m] V2 &
                              ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ▶[⫯l, m] T2 &
                              U2 = ⓑ{a,I}V2.T2.
/2 width=3 by cpy_inv_bind1_aux/ qed-.

fact cpy_inv_flat1_aux: ∀G,L,U1,U2,l,m. ⦃G, L⦄ ⊢ U1 ▶[l, m] U2 →
                        ∀I,V1,T1. U1 = ⓕ{I}V1.T1 →
                        ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ▶[l, m] V2 &
                                 ⦃G, L⦄ ⊢ T1 ▶[l, m] T2 &
                                 U2 = ⓕ{I}V2.T2.
#G #L #U1 #U2 #l #m * -G -L -U1 -U2 -l -m
[ #I #G #L #l #m #J #W1 #U1 #H destruct
| #I #G #L #K #V #W #i #l #m #_ #_ #_ #_ #J #W1 #U1 #H destruct
| #a #I #G #L #V1 #V2 #T1 #T2 #l #m #_ #_ #J #W1 #U1 #H destruct
| #I #G #L #V1 #V2 #T1 #T2 #l #m #HV12 #HT12 #J #W1 #U1 #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma cpy_inv_flat1: ∀I,G,L,V1,T1,U2,l,m. ⦃G, L⦄ ⊢ ⓕ{I} V1. T1 ▶[l, m] U2 →
                     ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ▶[l, m] V2 &
                              ⦃G, L⦄ ⊢ T1 ▶[l, m] T2 &
                              U2 = ⓕ{I}V2.T2.
/2 width=3 by cpy_inv_flat1_aux/ qed-.


fact cpy_inv_refl_O2_aux: ∀G,L,T1,T2,l,m. ⦃G, L⦄ ⊢ T1 ▶[l, m] T2 → m = 0 → T1 = T2.
#G #L #T1 #T2 #l #m #H elim H -G -L -T1 -T2 -l -m
[ //
| #I #G #L #K #V #W #i #l #m #Hli #Hilm #_ #_ #H destruct
  elim (ylt_yle_false … Hli) -Hli //
| /3 width=1 by eq_f2/
| /3 width=1 by eq_f2/
]
qed-.

lemma cpy_inv_refl_O2: ∀G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 ▶[l, 0] T2 → T1 = T2.
/2 width=6 by cpy_inv_refl_O2_aux/ qed-.

(* Basic_1: was: subst1_gen_lift_eq *)
lemma cpy_inv_lift1_eq: ∀G,T1,U1,l,m. ⬆[l, m] T1 ≡ U1 →
                        ∀L,U2. ⦃G, L⦄ ⊢ U1 ▶[l, m] U2 → U1 = U2.
#G #T1 #U1 #l #m #HTU1 #L #U2 #HU12 elim (cpy_fwd_up … HU12 … HTU1) -HU12 -HTU1
/2 width=4 by cpy_inv_refl_O2/
qed-.

(* Basic_1: removed theorems 25:
            subst0_gen_sort subst0_gen_lref subst0_gen_head subst0_gen_lift_lt
            subst0_gen_lift_false subst0_gen_lift_ge subst0_refl subst0_trans
            subst0_lift_lt subst0_lift_ge subst0_lift_ge_S subst0_lift_ge_s
            subst0_subst0 subst0_subst0_back subst0_weight_le subst0_weight_lt
            subst0_confluence_neq subst0_confluence_eq subst0_tlt_head
            subst0_confluence_lift subst0_tlt
            subst1_head subst1_gen_head subst1_lift_S subst1_confluence_lift
*)
