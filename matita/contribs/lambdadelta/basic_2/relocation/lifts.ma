
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

include "ground_2/relocation/nstream_after.ma".
include "basic_2/notation/relations/rliftstar_3.ma".
include "basic_2/grammar/term.ma".

(* GENERIC RELOCATION FOR TERMS *********************************************)

(* Basic_1: includes:
            lift_sort lift_lref_lt lift_lref_ge lift_bind lift_flat
            lifts_nil lifts_cons
*)
inductive lifts: rtmap → relation term ≝
| lifts_sort: ∀s,f. lifts f (⋆s) (⋆s)
| lifts_lref: ∀i1,i2,f. @⦃i1, f⦄ ≡ i2 → lifts f (#i1) (#i2)
| lifts_gref: ∀l,f. lifts f (§l) (§l)
| lifts_bind: ∀p,I,V1,V2,T1,T2,f.
              lifts f V1 V2 → lifts (↑f) T1 T2 →
              lifts f (ⓑ{p,I}V1.T1) (ⓑ{p,I}V2.T2)
| lifts_flat: ∀I,V1,V2,T1,T2,f.
              lifts f V1 V2 → lifts f T1 T2 →
              lifts f (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
.

interpretation "uniform relocation (term)"
   'RLiftStar i T1 T2 = (lifts (uni i) T1 T2).

interpretation "generic relocation (term)"
   'RLiftStar f T1 T2 = (lifts f T1 T2).


(* Basic inversion lemmas ***************************************************)

fact lifts_inv_sort1_aux: ∀X,Y,f. ⬆*[f] X ≡ Y → ∀s. X = ⋆s → Y = ⋆s.
#X #Y #f * -X -Y -f //
[ #i1 #i2 #f #_ #x #H destruct
| #p #I #V1 #V2 #T1 #T2 #f #_ #_ #x #H destruct
| #I #V1 #V2 #T1 #T2 #f #_ #_ #x #H destruct
]
qed-.

(* Basic_1: was: lift1_sort *)
(* Basic_2A1: includes: lift_inv_sort1 *)
lemma lifts_inv_sort1: ∀Y,s,f. ⬆*[f] ⋆s ≡ Y → Y = ⋆s.
/2 width=4 by lifts_inv_sort1_aux/ qed-.

fact lifts_inv_lref1_aux: ∀X,Y,f. ⬆*[f] X ≡ Y → ∀i1. X = #i1 →
                          ∃∃i2. @⦃i1, f⦄ ≡ i2 & Y = #i2.
#X #Y #f * -X -Y -f
[ #s #f #x #H destruct
| #i1 #i2 #f #Hi12 #x #H destruct /2 width=3 by ex2_intro/
| #l #f #x #H destruct
| #p #I #V1 #V2 #T1 #T2 #f #_ #_ #x #H destruct
| #I #V1 #V2 #T1 #T2 #f #_ #_ #x #H destruct
]
qed-.

(* Basic_1: was: lift1_lref *)
(* Basic_2A1: includes: lift_inv_lref1 lift_inv_lref1_lt lift_inv_lref1_ge *)
lemma lifts_inv_lref1: ∀Y,i1,f. ⬆*[f] #i1 ≡ Y →
                       ∃∃i2. @⦃i1, f⦄ ≡ i2 & Y = #i2.
/2 width=3 by lifts_inv_lref1_aux/ qed-.

fact lifts_inv_gref1_aux: ∀X,Y,f. ⬆*[f] X ≡ Y → ∀l. X = §l → Y = §l.
#X #Y #f * -X -Y -f //
[ #i1 #i2 #f #_ #x #H destruct
| #p #I #V1 #V2 #T1 #T2 #f #_ #_ #x #H destruct
| #I #V1 #V2 #T1 #T2 #f #_ #_ #x #H destruct
]
qed-.

(* Basic_2A1: includes: lift_inv_gref1 *)
lemma lifts_inv_gref1: ∀Y,l,f. ⬆*[f] §l ≡ Y → Y = §l.
/2 width=4 by lifts_inv_gref1_aux/ qed-.

fact lifts_inv_bind1_aux: ∀X,Y,f. ⬆*[f] X ≡ Y →
                          ∀p,I,V1,T1. X = ⓑ{p,I}V1.T1 →
                          ∃∃V2,T2. ⬆*[f] V1 ≡ V2 & ⬆*[↑f] T1 ≡ T2 &
                                   Y = ⓑ{p,I}V2.T2.
#X #Y #f * -X -Y -f
[ #s #f #q #J #W1 #U1 #H destruct
| #i1 #i2 #f #_ #q #J #W1 #U1 #H destruct
| #l #f #b #J #W1 #U1 #H destruct
| #p #I #V1 #V2 #T1 #T2 #f #HV12 #HT12 #q #J #W1 #U1 #H destruct /2 width=5 by ex3_2_intro/
| #I #V1 #V2 #T1 #T2 #f #_ #_ #q #J #W1 #U1 #H destruct
]
qed-.

(* Basic_1: was: lift1_bind *)
(* Basic_2A1: includes: lift_inv_bind1 *)
lemma lifts_inv_bind1: ∀p,I,V1,T1,Y,f. ⬆*[f] ⓑ{p,I}V1.T1 ≡ Y →
                       ∃∃V2,T2. ⬆*[f] V1 ≡ V2 & ⬆*[↑f] T1 ≡ T2 &
                                Y = ⓑ{p,I}V2.T2.
/2 width=3 by lifts_inv_bind1_aux/ qed-.

fact lifts_inv_flat1_aux: ∀X,Y. ∀f:rtmap. ⬆*[f] X ≡ Y →
                          ∀I,V1,T1. X = ⓕ{I}V1.T1 →
                          ∃∃V2,T2. ⬆*[f] V1 ≡ V2 & ⬆*[f] T1 ≡ T2 &
                                   Y = ⓕ{I}V2.T2.
#X #Y #f * -X -Y -f
[ #s #f #J #W1 #U1 #H destruct
| #i1 #i2 #f #_ #J #W1 #U1 #H destruct
| #l #f #J #W1 #U1 #H destruct
| #p #I #V1 #V2 #T1 #T2 #f #_ #_ #J #W1 #U1 #H destruct
| #I #V1 #V2 #T1 #T2 #f #HV12 #HT12 #J #W1 #U1 #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_1: was: lift1_flat *)
(* Basic_2A1: includes: lift_inv_flat1 *)
lemma lifts_inv_flat1: ∀I,V1,T1,Y. ∀f:rtmap. ⬆*[f] ⓕ{I}V1.T1 ≡ Y →
                       ∃∃V2,T2. ⬆*[f] V1 ≡ V2 & ⬆*[f] T1 ≡ T2 &
                                Y = ⓕ{I}V2.T2.
/2 width=3 by lifts_inv_flat1_aux/ qed-.

fact lifts_inv_sort2_aux: ∀X,Y,f. ⬆*[f] X ≡ Y → ∀s. Y = ⋆s → X = ⋆s.
#X #Y #f * -X -Y -f //
[ #i1 #i2 #f #_ #x #H destruct
| #p #I #V1 #V2 #T1 #T2 #f #_ #_ #x #H destruct
| #I #V1 #V2 #T1 #T2 #f #_ #_ #x #H destruct
]
qed-.

(* Basic_1: includes: lift_gen_sort *)
(* Basic_2A1: includes: lift_inv_sort2 *)
lemma lifts_inv_sort2: ∀X,s,f. ⬆*[f] X ≡ ⋆s → X = ⋆s.
/2 width=4 by lifts_inv_sort2_aux/ qed-.

fact lifts_inv_lref2_aux: ∀X,Y,f. ⬆*[f] X ≡ Y → ∀i2. Y = #i2 →
                          ∃∃i1. @⦃i1, f⦄ ≡ i2 & X = #i1.
#X #Y #f * -X -Y -f
[ #s #f #x #H destruct
| #i1 #i2 #f #Hi12 #x #H destruct /2 width=3 by ex2_intro/
| #l #f #x #H destruct
| #p #I #V1 #V2 #T1 #T2 #f #_ #_ #x #H destruct
| #I #V1 #V2 #T1 #T2 #f #_ #_ #x #H destruct
]
qed-.

(* Basic_1: includes: lift_gen_lref lift_gen_lref_lt lift_gen_lref_false lift_gen_lref_ge *)
(* Basic_2A1: includes: lift_inv_lref2 lift_inv_lref2_lt lift_inv_lref2_be lift_inv_lref2_ge lift_inv_lref2_plus *)
lemma lifts_inv_lref2: ∀X,i2,f. ⬆*[f] X ≡ #i2 →
                       ∃∃i1. @⦃i1, f⦄ ≡ i2 & X = #i1.
/2 width=3 by lifts_inv_lref2_aux/ qed-.

fact lifts_inv_gref2_aux: ∀X,Y,f. ⬆*[f] X ≡ Y → ∀l. Y = §l → X = §l.
#X #Y #f * -X -Y -f //
[ #i1 #i2 #f #_ #x #H destruct
| #p #I #V1 #V2 #T1 #T2 #f #_ #_ #x #H destruct
| #I #V1 #V2 #T1 #T2 #f #_ #_ #x #H destruct
]
qed-.

(* Basic_2A1: includes: lift_inv_gref1 *)
lemma lifts_inv_gref2: ∀X,l,f. ⬆*[f] X ≡ §l → X = §l.
/2 width=4 by lifts_inv_gref2_aux/ qed-.

fact lifts_inv_bind2_aux: ∀X,Y,f. ⬆*[f] X ≡ Y →
                          ∀p,I,V2,T2. Y = ⓑ{p,I}V2.T2 →
                          ∃∃V1,T1. ⬆*[f] V1 ≡ V2 & ⬆*[↑f] T1 ≡ T2 &
                                   X = ⓑ{p,I}V1.T1.
#X #Y #f * -X -Y -f
[ #s #f #q #J #W2 #U2 #H destruct
| #i1 #i2 #f #_ #q #J #W2 #U2 #H destruct
| #l #f #q #J #W2 #U2 #H destruct
| #p #I #V1 #V2 #T1 #T2 #f #HV12 #HT12 #q #J #W2 #U2 #H destruct /2 width=5 by ex3_2_intro/
| #I #V1 #V2 #T1 #T2 #f #_ #_ #q #J #W2 #U2 #H destruct
]
qed-.

(* Basic_1: includes: lift_gen_bind *)
(* Basic_2A1: includes: lift_inv_bind2 *)
lemma lifts_inv_bind2: ∀p,I,V2,T2,X,f. ⬆*[f] X ≡ ⓑ{p,I}V2.T2 →
                       ∃∃V1,T1. ⬆*[f] V1 ≡ V2 & ⬆*[↑f] T1 ≡ T2 &
                                X = ⓑ{p,I}V1.T1.
/2 width=3 by lifts_inv_bind2_aux/ qed-.

fact lifts_inv_flat2_aux: ∀X,Y. ∀f:rtmap. ⬆*[f] X ≡ Y →
                          ∀I,V2,T2. Y = ⓕ{I}V2.T2 →
                          ∃∃V1,T1. ⬆*[f] V1 ≡ V2 & ⬆*[f] T1 ≡ T2 &
                                   X = ⓕ{I}V1.T1.
#X #Y #f * -X -Y -f
[ #s #f #J #W2 #U2 #H destruct
| #i1 #i2 #f #_ #J #W2 #U2 #H destruct
| #l #f #J #W2 #U2 #H destruct
| #p #I #V1 #V2 #T1 #T2 #f #_ #_ #J #W2 #U2 #H destruct
| #I #V1 #V2 #T1 #T2 #f #HV12 #HT12 #J #W2 #U2 #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_1: includes: lift_gen_flat *)
(* Basic_2A1: includes: lift_inv_flat2 *)
lemma lifts_inv_flat2: ∀I,V2,T2,X. ∀f:rtmap. ⬆*[f] X ≡ ⓕ{I}V2.T2 →
                       ∃∃V1,T1. ⬆*[f] V1 ≡ V2 & ⬆*[f] T1 ≡ T2 &
                                X = ⓕ{I}V1.T1.
/2 width=3 by lifts_inv_flat2_aux/ qed-.

(* Basic_2A1: includes: lift_inv_pair_xy_x *)
lemma lifts_inv_pair_xy_x: ∀I,V,T,f. ⬆*[f] ②{I}V.T ≡ V → ⊥.
#J #V elim V -V
[ * #i #U #f #H
  [ lapply (lifts_inv_sort2 … H) -H #H destruct
  | elim (lifts_inv_lref2 … H) -H
    #x #_ #H destruct
  | lapply (lifts_inv_gref2 … H) -H #H destruct
  ]
| * [ #p ] #I #V2 #T2 #IHV2 #_ #U #f #H
  [ elim (lifts_inv_bind2 … H) -H #V1 #T1 #HV12 #_ #H destruct /2 width=3 by/
  | elim (lifts_inv_flat2 … H) -H #V1 #T1 #HV12 #_ #H destruct /2 width=3 by/
  ]
]
qed-.

(* Basic_1: includes: thead_x_lift_y_y *)
(* Basic_2A1: includes: lift_inv_pair_xy_y *)
lemma lifts_inv_pair_xy_y: ∀I,T,V,f. ⬆*[f] ②{I}V.T ≡ T → ⊥.
#J #T elim T -T
[ * #i #W #f #H
  [ lapply (lifts_inv_sort2 … H) -H #H destruct
  | elim (lifts_inv_lref2 … H) -H
    #x #_ #H destruct
  | lapply (lifts_inv_gref2 … H) -H #H destruct
  ]
| * [ #p ] #I #V2 #T2 #_ #IHT2 #W #f #H
  [ elim (lifts_inv_bind2 … H) -H #V1 #T1 #_ #HT12 #H destruct /2 width=4 by/
  | elim (lifts_inv_flat2 … H) -H #V1 #T1 #_ #HT12 #H destruct /2 width=4 by/
  ]
]
qed-.

(* Basic forward lemmas *****************************************************)

(* Basic_2A1: includes: lift_inv_O2 *)
lemma lifts_fwd_isid: ∀T1,T2,f. ⬆*[f] T1 ≡ T2 → 𝐈⦃f⦄ → T1 = T2.
#T1 #T2 #f #H elim H -T1 -T2 -f
/4 width=3 by isid_inv_at_mono, isid_push, eq_f2, eq_f/
qed-.

(* Basic_2A1: includes: lift_fwd_pair1 *)
lemma lifts_fwd_pair1: ∀I,V1,T1,Y. ∀f:rtmap. ⬆*[f] ②{I}V1.T1 ≡ Y →
                       ∃∃V2,T2. ⬆*[f] V1 ≡ V2 & Y = ②{I}V2.T2.
* [ #p ] #I #V1 #T1 #Y #f #H
[ elim (lifts_inv_bind1 … H) -H /2 width=4 by ex2_2_intro/
| elim (lifts_inv_flat1 … H) -H /2 width=4 by ex2_2_intro/
]
qed-.

(* Basic_2A1: includes: lift_fwd_pair2 *)
lemma lifts_fwd_pair2: ∀I,V2,T2,X. ∀f:rtmap. ⬆*[f] X ≡ ②{I}V2.T2 →
                       ∃∃V1,T1. ⬆*[f] V1 ≡ V2 & X = ②{I}V1.T1.
* [ #p ] #I #V2 #T2 #X #f #H
[ elim (lifts_inv_bind2 … H) -H /2 width=4 by ex2_2_intro/
| elim (lifts_inv_flat2 … H) -H /2 width=4 by ex2_2_intro/
]
qed-.

(* Basic properties *********************************************************)

lemma lifts_eq_repl_back: ∀T1,T2. eq_repl_back … (λf. ⬆*[f] T1 ≡ T2).
#T1 #T2 #f1 #H elim H -T1 -T2 -f1
/4 width=5 by lifts_flat, lifts_bind, lifts_lref, at_eq_repl_back, eq_push/
qed-.

lemma lifts_eq_repl_fwd: ∀T1,T2. eq_repl_fwd … (λf. ⬆*[f] T1 ≡ T2).
#T1 #T2 @eq_repl_sym /2 width=3 by lifts_eq_repl_back/ (**) (* full auto fails *)
qed-.

(* Basic_1: includes: lift_r *)
(* Basic_2A1: includes: lift_refl *)
lemma lifts_refl: ∀T,f. 𝐈⦃f⦄ → ⬆*[f] T ≡ T.
#T elim T -T *
/4 width=3 by lifts_flat, lifts_bind, lifts_lref, isid_inv_at, isid_push/
qed.

(* Basic_2A1: includes: lift_total *)
lemma lifts_total: ∀T1,f. ∃T2. ⬆*[f] T1 ≡ T2.
#T1 elim T1 -T1 *
/3 width=2 by lifts_lref, lifts_sort, lifts_gref, ex_intro/
[ #p ] #I #V1 #T1 #IHV1 #IHT1 #f
elim (IHV1 f) -IHV1 #V2 #HV12
[ elim (IHT1 (↑f)) -IHT1 /3 width=2 by lifts_bind, ex_intro/
| elim (IHT1 f) -IHT1 /3 width=2 by lifts_flat, ex_intro/
]
qed-.

lemma lift_lref_uni: ∀l,i. ⬆*[l] #i ≡ #(l+i).
#l elim l -l /2 width=1 by lifts_lref/
qed.

(* Basic_1: includes: lift_free (right to left) *)
(* Basic_2A1: includes: lift_split *)
lemma lifts_split_trans: ∀T1,T2,f. ⬆*[f] T1 ≡ T2 →
                         ∀f1,f2. f2 ⊚ f1 ≡ f →
                         ∃∃T. ⬆*[f1] T1 ≡ T & ⬆*[f2] T ≡ T2.
#T1 #T2 #f #H elim H -T1 -T2 -f
[ /3 width=3 by lifts_sort, ex2_intro/
| #i1 #i2 #f #Hi #f1 #f2 #Ht elim (after_at_fwd … Hi … Ht) -Hi -Ht
  /3 width=3 by lifts_lref, ex2_intro/
| /3 width=3 by lifts_gref, ex2_intro/
| #p #I #V1 #V2 #T1 #T2 #f #_ #_ #IHV #IHT #f1 #f2 #Ht
  elim (IHV … Ht) elim (IHT (↑f1) (↑f2)) -IHV -IHT
  /3 width=5 by lifts_bind, after_O2, ex2_intro/
| #I #V1 #V2 #T1 #T2 #f #_ #_ #IHV #IHT #f1 #f2 #Ht
  elim (IHV … Ht) elim (IHT … Ht) -IHV -IHT -Ht
  /3 width=5 by lifts_flat, ex2_intro/
]
qed-.

(* Note: apparently, this was missing in Basic_2A1 *)
lemma lifts_split_div: ∀T1,T2,f1. ⬆*[f1] T1 ≡ T2 →
                       ∀f2,f. f2 ⊚ f1 ≡ f →
                       ∃∃T. ⬆*[f2] T2 ≡ T & ⬆*[f] T1 ≡ T.
#T1 #T2 #f1 #H elim H -T1 -T2 -f1
[ /3 width=3 by lifts_sort, ex2_intro/
| #i1 #i2 #f1 #Hi #f2 #f #Ht elim (after_at1_fwd … Hi … Ht) -Hi -Ht
  /3 width=3 by lifts_lref, ex2_intro/
| /3 width=3 by lifts_gref, ex2_intro/
| #p #I #V1 #V2 #T1 #T2 #f1 #_ #_ #IHV #IHT #f2 #f #Ht
  elim (IHV … Ht) elim (IHT (↑f2) (↑f)) -IHV -IHT
  /3 width=5 by lifts_bind, after_O2, ex2_intro/
| #I #V1 #V2 #T1 #T2 #f1 #_ #_ #IHV #IHT #f2 #f #Ht
  elim (IHV … Ht) elim (IHT … Ht) -IHV -IHT -Ht
  /3 width=5 by lifts_flat, ex2_intro/
]
qed-.

(* Basic_1: includes: dnf_dec2 dnf_dec *)
(* Basic_2A1: includes: is_lift_dec *)
lemma is_lifts_dec: ∀T2,f. Decidable (∃T1. ⬆*[f] T1 ≡ T2).
#T1 elim T1 -T1
[ * [1,3: /3 width=2 by lifts_sort, lifts_gref, ex_intro, or_introl/ ]
  #i2 #f elim (is_at_dec f i2) //
  [ * /4 width=3 by lifts_lref, ex_intro, or_introl/
  | #H @or_intror *
    #X #HX elim (lifts_inv_lref2 … HX) -HX
    /3 width=2 by ex_intro/
  ]
| * [ #p ] #I #V2 #T2 #IHV2 #IHT2 #f
  [ elim (IHV2 f) -IHV2
    [ * #V1 #HV12 elim (IHT2 (↑f)) -IHT2
      [ * #T1 #HT12 @or_introl /3 width=2 by lifts_bind, ex_intro/
      | -V1 #HT2 @or_intror * #X #H
        elim (lifts_inv_bind2 … H) -H /3 width=2 by ex_intro/
      ]
    | -IHT2 #HV2 @or_intror * #X #H
      elim (lifts_inv_bind2 … H) -H /3 width=2 by ex_intro/
    ]
  | elim (IHV2 f) -IHV2
    [ * #V1 #HV12 elim (IHT2 f) -IHT2
      [ * #T1 #HT12 /4 width=2 by lifts_flat, ex_intro, or_introl/
      | -V1 #HT2 @or_intror * #X #H
        elim (lifts_inv_flat2 … H) -H /3 width=2 by ex_intro/
      ]
    | -IHT2 #HV2 @or_intror * #X #H
      elim (lifts_inv_flat2 … H) -H /3 width=2 by ex_intro/
    ]
  ]
]
qed-.

(* Basic_2A1: removed theorems 14:
              lifts_inv_nil lifts_inv_cons
              lift_inv_Y1 lift_inv_Y2 lift_inv_lref_Y1 lift_inv_lref_Y2 lift_lref_Y lift_Y1
              lift_lref_lt_eq lift_lref_ge_eq lift_lref_plus lift_lref_pred
              lift_lref_ge_minus lift_lref_ge_minus_eq
*)
(* Basic_1: removed theorems 8:
            lift_lref_gt            
            lift_head lift_gen_head 
            lift_weight_map lift_weight lift_weight_add lift_weight_add_O
            lift_tlt_dx
*)
