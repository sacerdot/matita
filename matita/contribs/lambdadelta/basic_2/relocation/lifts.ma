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

include "ground_2/relocation/trace_isid.ma".
include "basic_2/notation/relations/rliftstar_3.ma".
include "basic_2/grammar/term.ma".

(* GENERIC RELOCATION FOR TERMS *********************************************)

(* Basic_1: includes:
            lift_sort lift_lref_lt lift_lref_ge lift_bind lift_flat
            lifts_nil lifts_cons
*)
inductive lifts: trace → relation term ≝
| lifts_sort: ∀k,t. lifts t (⋆k) (⋆k)
| lifts_lref: ∀i1,i2,t. @⦃i1, t⦄ ≡ i2 → lifts t (#i1) (#i2)
| lifts_gref: ∀p,t. lifts t (§p) (§p)
| lifts_bind: ∀a,I,V1,V2,T1,T2,t.
              lifts t V1 V2 → lifts (Ⓣ@t) T1 T2 →
              lifts t (ⓑ{a,I}V1.T1) (ⓑ{a,I}V2.T2)
| lifts_flat: ∀I,V1,V2,T1,T2,t.
              lifts t V1 V2 → lifts t T1 T2 →
              lifts t (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
.

interpretation "generic relocation (term)"
   'RLiftStar cs T1 T2 = (lifts cs T1 T2).

(* Basic inversion lemmas ***************************************************)

fact lifts_inv_sort1_aux: ∀X,Y,t. ⬆*[t] X ≡ Y → ∀k. X = ⋆k → Y = ⋆k.
#X #Y #t * -X -Y -t //
[ #i1 #i2 #t #_ #x #H destruct
| #a #I #V1 #V2 #T1 #T2 #t #_ #_ #x #H destruct
| #I #V1 #V2 #T1 #T2 #t #_ #_ #x #H destruct
]
qed-.

(* Basic_1: was: lift1_sort *)
(* Basic_2A1: includes: lift_inv_sort1 *)
lemma lifts_inv_sort1: ∀Y,k,t. ⬆*[t] ⋆k ≡ Y → Y = ⋆k.
/2 width=4 by lifts_inv_sort1_aux/ qed-.

fact lifts_inv_lref1_aux: ∀X,Y,t. ⬆*[t] X ≡ Y → ∀i1. X = #i1 →
                          ∃∃i2. @⦃i1, t⦄ ≡ i2 & Y = #i2.
#X #Y #t * -X -Y -t
[ #k #t #x #H destruct
| #i1 #i2 #t #Hi12 #x #H destruct /2 width=3 by ex2_intro/
| #p #t #x #H destruct
| #a #I #V1 #V2 #T1 #T2 #t #_ #_ #x #H destruct
| #I #V1 #V2 #T1 #T2 #t #_ #_ #x #H destruct
]
qed-.

(* Basic_1: was: lift1_lref *)
(* Basic_2A1: includes: lift_inv_lref1 lift_inv_lref1_lt lift_inv_lref1_ge *)
lemma lifts_inv_lref1: ∀Y,i1,t. ⬆*[t] #i1 ≡ Y →
                       ∃∃i2. @⦃i1, t⦄ ≡ i2 & Y = #i2.
/2 width=3 by lifts_inv_lref1_aux/ qed-.

fact lifts_inv_gref1_aux: ∀X,Y,t. ⬆*[t] X ≡ Y → ∀p. X = §p → Y = §p.
#X #Y #t * -X -Y -t //
[ #i1 #i2 #t #_ #x #H destruct
| #a #I #V1 #V2 #T1 #T2 #t #_ #_ #x #H destruct
| #I #V1 #V2 #T1 #T2 #t #_ #_ #x #H destruct
]
qed-.

(* Basic_2A1: includes: lift_inv_gref1 *)
lemma lifts_inv_gref1: ∀Y,p,t. ⬆*[t] §p ≡ Y → Y = §p.
/2 width=4 by lifts_inv_gref1_aux/ qed-.

fact lifts_inv_bind1_aux: ∀X,Y,t. ⬆*[t] X ≡ Y →
                          ∀a,I,V1,T1. X = ⓑ{a,I}V1.T1 →
                          ∃∃V2,T2. ⬆*[t] V1 ≡ V2 & ⬆*[Ⓣ@t] T1 ≡ T2 &
                                   Y = ⓑ{a,I}V2.T2.
#X #Y #t * -X -Y -t
[ #k #t #b #J #W1 #U1 #H destruct
| #i1 #i2 #t #_ #b #J #W1 #U1 #H destruct
| #p #t #b #J #W1 #U1 #H destruct
| #a #I #V1 #V2 #T1 #T2 #t #HV12 #HT12 #b #J #W1 #U1 #H destruct /2 width=5 by ex3_2_intro/
| #I #V1 #V2 #T1 #T2 #t #_ #_ #b #J #W1 #U1 #H destruct
]
qed-.

(* Basic_1: was: lift1_bind *)
(* Basic_2A1: includes: lift_inv_bind1 *)
lemma lifts_inv_bind1: ∀a,I,V1,T1,Y,t. ⬆*[t] ⓑ{a,I}V1.T1 ≡ Y →
                       ∃∃V2,T2. ⬆*[t] V1 ≡ V2 & ⬆*[Ⓣ@t] T1 ≡ T2 &
                                Y = ⓑ{a,I}V2.T2.
/2 width=3 by lifts_inv_bind1_aux/ qed-.

fact lifts_inv_flat1_aux: ∀X,Y,t. ⬆*[t] X ≡ Y →
                          ∀I,V1,T1. X = ⓕ{I}V1.T1 →
                          ∃∃V2,T2. ⬆*[t] V1 ≡ V2 & ⬆*[t] T1 ≡ T2 &
                                   Y = ⓕ{I}V2.T2.
#X #Y #t * -X -Y -t
[ #k #t #J #W1 #U1 #H destruct
| #i1 #i2 #t #_ #J #W1 #U1 #H destruct
| #p #t #J #W1 #U1 #H destruct
| #a #I #V1 #V2 #T1 #T2 #t #_ #_ #J #W1 #U1 #H destruct
| #I #V1 #V2 #T1 #T2 #t #HV12 #HT12 #J #W1 #U1 #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_1: was: lift1_flat *)
(* Basic_2A1: includes: lift_inv_flat1 *)
lemma lifts_inv_flat1: ∀I,V1,T1,Y,t. ⬆*[t] ⓕ{I}V1.T1 ≡ Y →
                       ∃∃V2,T2. ⬆*[t] V1 ≡ V2 & ⬆*[t] T1 ≡ T2 &
                                Y = ⓕ{I}V2.T2.
/2 width=3 by lifts_inv_flat1_aux/ qed-.

fact lifts_inv_sort2_aux: ∀X,Y,t. ⬆*[t] X ≡ Y → ∀k. Y = ⋆k → X = ⋆k.
#X #Y #t * -X -Y -t //
[ #i1 #i2 #t #_ #x #H destruct
| #a #I #V1 #V2 #T1 #T2 #t #_ #_ #x #H destruct
| #I #V1 #V2 #T1 #T2 #t #_ #_ #x #H destruct
]
qed-.

(* Basic_1: includes: lift_gen_sort *)
(* Basic_2A1: includes: lift_inv_sort2 *)
lemma lifts_inv_sort2: ∀X,k,t. ⬆*[t] X ≡ ⋆k → X = ⋆k.
/2 width=4 by lifts_inv_sort2_aux/ qed-.

fact lifts_inv_lref2_aux: ∀X,Y,t. ⬆*[t] X ≡ Y → ∀i2. Y = #i2 →
                          ∃∃i1. @⦃i1, t⦄ ≡ i2 & X = #i1.
#X #Y #t * -X -Y -t
[ #k #t #x #H destruct
| #i1 #i2 #t #Hi12 #x #H destruct /2 width=3 by ex2_intro/
| #p #t #x #H destruct
| #a #I #V1 #V2 #T1 #T2 #t #_ #_ #x #H destruct
| #I #V1 #V2 #T1 #T2 #t #_ #_ #x #H destruct
]
qed-.

(* Basic_1: includes: lift_gen_lref lift_gen_lref_lt lift_gen_lref_false lift_gen_lref_ge *)
(* Basic_2A1: includes: lift_inv_lref2 lift_inv_lref2_lt lift_inv_lref2_be lift_inv_lref2_ge lift_inv_lref2_plus *)
lemma lifts_inv_lref2: ∀X,i2,t. ⬆*[t] X ≡ #i2 →
                       ∃∃i1. @⦃i1, t⦄ ≡ i2 & X = #i1.
/2 width=3 by lifts_inv_lref2_aux/ qed-.

fact lifts_inv_gref2_aux: ∀X,Y,t. ⬆*[t] X ≡ Y → ∀p. Y = §p → X = §p.
#X #Y #t * -X -Y -t //
[ #i1 #i2 #t #_ #x #H destruct
| #a #I #V1 #V2 #T1 #T2 #t #_ #_ #x #H destruct
| #I #V1 #V2 #T1 #T2 #t #_ #_ #x #H destruct
]
qed-.

(* Basic_2A1: includes: lift_inv_gref1 *)
lemma lifts_inv_gref2: ∀X,p,t. ⬆*[t] X ≡ §p → X = §p.
/2 width=4 by lifts_inv_gref2_aux/ qed-.

fact lifts_inv_bind2_aux: ∀X,Y,t. ⬆*[t] X ≡ Y →
                          ∀a,I,V2,T2. Y = ⓑ{a,I}V2.T2 →
                          ∃∃V1,T1. ⬆*[t] V1 ≡ V2 & ⬆*[Ⓣ@t] T1 ≡ T2 &
                                   X = ⓑ{a,I}V1.T1.
#X #Y #t * -X -Y -t
[ #k #t #b #J #W2 #U2 #H destruct
| #i1 #i2 #t #_ #b #J #W2 #U2 #H destruct
| #p #t #b #J #W2 #U2 #H destruct
| #a #I #V1 #V2 #T1 #T2 #t #HV12 #HT12 #b #J #W2 #U2 #H destruct /2 width=5 by ex3_2_intro/
| #I #V1 #V2 #T1 #T2 #t #_ #_ #b #J #W2 #U2 #H destruct
]
qed-.

(* Basic_1: includes: lift_gen_bind *)
(* Basic_2A1: includes: lift_inv_bind2 *)
lemma lifts_inv_bind2: ∀a,I,V2,T2,X,t. ⬆*[t] X ≡ ⓑ{a,I}V2.T2 →
                       ∃∃V1,T1. ⬆*[t] V1 ≡ V2 & ⬆*[Ⓣ@t] T1 ≡ T2 &
                                X = ⓑ{a,I}V1.T1.
/2 width=3 by lifts_inv_bind2_aux/ qed-.

fact lifts_inv_flat2_aux: ∀X,Y,t. ⬆*[t] X ≡ Y →
                          ∀I,V2,T2. Y = ⓕ{I}V2.T2 →
                          ∃∃V1,T1. ⬆*[t] V1 ≡ V2 & ⬆*[t] T1 ≡ T2 &
                                   X = ⓕ{I}V1.T1.
#X #Y #t * -X -Y -t
[ #k #t #J #W2 #U2 #H destruct
| #i1 #i2 #t #_ #J #W2 #U2 #H destruct
| #p #t #J #W2 #U2 #H destruct
| #a #I #V1 #V2 #T1 #T2 #t #_ #_ #J #W2 #U2 #H destruct
| #I #V1 #V2 #T1 #T2 #t #HV12 #HT12 #J #W2 #U2 #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_1: includes: lift_gen_flat *)
(* Basic_2A1: includes: lift_inv_flat2 *)
lemma lifts_inv_flat2: ∀I,V2,T2,X,t. ⬆*[t] X ≡ ⓕ{I}V2.T2 →
                       ∃∃V1,T1. ⬆*[t] V1 ≡ V2 & ⬆*[t] T1 ≡ T2 &
                                X = ⓕ{I}V1.T1.
/2 width=3 by lifts_inv_flat2_aux/ qed-.

(* Basic_2A1: includes: lift_inv_pair_xy_x *)
lemma lifts_inv_pair_xy_x: ∀I,V,T,t. ⬆*[t] ②{I}V.T ≡ V → ⊥.
#J #V elim V -V
[ * #i #U #t #H
  [ lapply (lifts_inv_sort2 … H) -H #H destruct
  | elim (lifts_inv_lref2 … H) -H
    #x #_ #H destruct
  | lapply (lifts_inv_gref2 … H) -H #H destruct
  ]
| * [ #a ] #I #V2 #T2 #IHV2 #_ #U #t #H
  [ elim (lifts_inv_bind2 … H) -H #V1 #T1 #HV12 #_ #H destruct /2 width=3 by/
  | elim (lifts_inv_flat2 … H) -H #V1 #T1 #HV12 #_ #H destruct /2 width=3 by/
  ]
]
qed-.

(* Basic_1: includes: thead_x_lift_y_y *)
(* Basic_2A1: includes: lift_inv_pair_xy_y *)
lemma lifts_inv_pair_xy_y: ∀I,T,V,t. ⬆*[t] ②{I}V.T ≡ T → ⊥.
#J #T elim T -T
[ * #i #W #t #H
  [ lapply (lifts_inv_sort2 … H) -H #H destruct
  | elim (lifts_inv_lref2 … H) -H
    #x #_ #H destruct
  | lapply (lifts_inv_gref2 … H) -H #H destruct
  ]
| * [ #a ] #I #V2 #T2 #_ #IHT2 #W #t #H
  [ elim (lifts_inv_bind2 … H) -H #V1 #T1 #_ #HT12 #H destruct /2 width=4 by/
  | elim (lifts_inv_flat2 … H) -H #V1 #T1 #_ #HT12 #H destruct /2 width=4 by/
  ]
]
qed-.

(* Basic forward lemmas *****************************************************)

(* Basic_2A1: includes: lift_inv_O2 *)
lemma lifts_fwd_isid: ∀T1,T2,t. ⬆*[t] T1 ≡ T2 → 𝐈⦃t⦄ → T1 = T2.
#T1 #T2 #t #H elim H -T1 -T2 -t /4 width=3 by isid_inv_at, eq_f2, eq_f/
qed-.

(* Basic_2A1: includes: lift_fwd_pair1 *)
lemma lifts_fwd_pair1: ∀I,V1,T1,Y,t. ⬆*[t] ②{I}V1.T1 ≡ Y →
                       ∃∃V2,T2. ⬆*[t] V1 ≡ V2 & Y = ②{I}V2.T2.
* [ #a ] #I #V1 #T1 #Y #t #H
[ elim (lifts_inv_bind1 … H) -H /2 width=4 by ex2_2_intro/
| elim (lifts_inv_flat1 … H) -H /2 width=4 by ex2_2_intro/
]
qed-.

(* Basic_2A1: includes: lift_fwd_pair2 *)
lemma lifts_fwd_pair2: ∀I,V2,T2,X,t. ⬆*[t] X ≡ ②{I}V2.T2 →
                       ∃∃V1,T1. ⬆*[t] V1 ≡ V2 & X = ②{I}V1.T1.
* [ #a ] #I #V2 #T2 #X #t #H
[ elim (lifts_inv_bind2 … H) -H /2 width=4 by ex2_2_intro/
| elim (lifts_inv_flat2 … H) -H /2 width=4 by ex2_2_intro/
]
qed-.

(* Basic properties *********************************************************)

(* Basic_1: includes: lift_free (right to left) *)
(* Basic_2A1: includes: lift_split *)
lemma lifts_split_trans: ∀T1,T2,t. ⬆*[t] T1 ≡ T2 →
                         ∀t1,t2. t2 ⊚ t1 ≡ t →
                         ∃∃T. ⬆*[t1] T1 ≡ T & ⬆*[t2] T ≡ T2.
#T1 #T2 #t #H elim H -T1 -T2 -t
[ /3 width=3 by lifts_sort, ex2_intro/
| #i1 #i2 #t #Hi #t1 #t2 #Ht elim (after_at_fwd … Ht … Hi) -Ht -Hi
  /3 width=3 by lifts_lref, ex2_intro/
| /3 width=3 by lifts_gref, ex2_intro/
| #a #I #V1 #V2 #T1 #T2 #t #_ #_ #IHV #IHT #t1 #t2 #Ht
  elim (IHV … Ht) elim (IHT (Ⓣ@t1) (Ⓣ@t2)) -IHV -IHT
  /3 width=5 by lifts_bind, after_true, ex2_intro/
| #I #V1 #V2 #T1 #T2 #t #_ #_ #IHV #IHT #t1 #t2 #Ht
  elim (IHV … Ht) elim (IHT … Ht) -IHV -IHT -Ht
  /3 width=5 by lifts_flat, ex2_intro/
]
qed-.

(* Note: apparently, this was missing in Basic_2A1 *)
lemma lifts_split_div: ∀T1,T2,t1. ⬆*[t1] T1 ≡ T2 →
                       ∀t2,t. t2 ⊚ t1 ≡ t →
                       ∃∃T. ⬆*[t2] T2 ≡ T & ⬆*[t] T1 ≡ T.
#T1 #T2 #t1 #H elim H -T1 -T2 -t1
[ /3 width=3 by lifts_sort, ex2_intro/
| #i1 #i2 #t1 #Hi #t2 #t #Ht elim (after_at1_fwd … Ht … Hi) -Ht -Hi
  /3 width=3 by lifts_lref, ex2_intro/
| /3 width=3 by lifts_gref, ex2_intro/
| #a #I #V1 #V2 #T1 #T2 #t1 #_ #_ #IHV #IHT #t2 #t #Ht
  elim (IHV … Ht) elim (IHT (Ⓣ@t2) (Ⓣ@t)) -IHV -IHT
  /3 width=5 by lifts_bind, after_true, ex2_intro/
| #I #V1 #V2 #T1 #T2 #t1 #_ #_ #IHV #IHT #t2 #t #Ht
  elim (IHV … Ht) elim (IHT … Ht) -IHV -IHT -Ht
  /3 width=5 by lifts_flat, ex2_intro/
]
qed-.

(* Basic_1: includes: dnf_dec2 dnf_dec *)
(* Basic_2A1: includes: is_lift_dec *)
lemma is_lifts_dec: ∀T2,t. Decidable (∃T1. ⬆*[t] T1 ≡ T2).
#T1 elim T1 -T1
[ * [1,3: /3 width=2 by lifts_sort, lifts_gref, ex_intro, or_introl/ ]
  #i2 #t elim (is_at_dec t i2)
  [ * /4 width=3 by lifts_lref, ex_intro, or_introl/
  | #H @or_intror *
    #X #HX elim (lifts_inv_lref2 … HX) -HX
    /3 width=2 by ex_intro/
  ]
| * [ #a ] #I #V2 #T2 #IHV2 #IHT2 #t
  [ elim (IHV2 t) -IHV2
    [ * #V1 #HV12 elim (IHT2 (Ⓣ@t)) -IHT2
      [ * #T1 #HT12 @or_introl /3 width=2 by lifts_bind, ex_intro/
      | -V1 #HT2 @or_intror * #X #H
        elim (lifts_inv_bind2 … H) -H /3 width=2 by ex_intro/
      ]
    | -IHT2 #HV2 @or_intror * #X #H
      elim (lifts_inv_bind2 … H) -H /3 width=2 by ex_intro/
    ]
  | elim (IHV2 t) -IHV2
    [ * #V1 #HV12 elim (IHT2 t) -IHT2
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
