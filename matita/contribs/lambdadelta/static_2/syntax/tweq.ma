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

include "ground_2/xoa/ex_1_2.ma".
include "ground_2/xoa/ex_3_2.ma".
include "static_2/notation/relations/approxeq_2.ma".
include "static_2/syntax/term_weight.ma".

(* SORT-IRRELEVANT WHD EQUIVALENCE ON TERMS *********************************)

inductive tweq: relation term ≝
| tweq_sort: ∀s1,s2. tweq (⋆s1) (⋆s2)
| tweq_lref: ∀i. tweq (#i) (#i)
| tweq_gref: ∀l. tweq (§l) (§l)
| tweq_abbr: ∀p,V1,V2,T1,T2. (p=Ⓣ→tweq T1 T2) → tweq (ⓓ{p}V1.T1) (ⓓ{p}V2.T2)
| tweq_abst: ∀p,V1,V2,T1,T2. tweq (ⓛ{p}V1.T1) (ⓛ{p}V2.T2)
| tweq_appl: ∀V1,V2,T1,T2. tweq T1 T2 → tweq (ⓐV1.T1) (ⓐV2.T2)
| tweq_cast: ∀V1,V2,T1,T2. tweq V1 V2 → tweq T1 T2 → tweq (ⓝV1.T1) (ⓝV2.T2)
.

interpretation
   "context-free tail sort-irrelevant equivalence (term)"
   'ApproxEq T1 T2 = (tweq T1 T2).

(* Basic properties *********************************************************)

lemma tweq_abbr_pos: ∀V1,V2,T1,T2. T1 ≅ T2 → +ⓓV1.T1 ≅ +ⓓV2.T2.
/3 width=1 by tweq_abbr/ qed.

lemma tweq_abbr_neg: ∀V1,V2,T1,T2. -ⓓV1.T1 ≅ -ⓓV2.T2.
#V1 #V2 #T1 #T2
@tweq_abbr #H destruct
qed.

lemma tweq_refl: reflexive … tweq.
#T elim T -T * [||| #p * | * ]
/2 width=1 by tweq_sort, tweq_lref, tweq_gref, tweq_abbr, tweq_abst, tweq_appl, tweq_cast/
qed.

lemma tweq_sym: symmetric … tweq.
#T1 #T2 #H elim H -T1 -T2
/3 width=3 by tweq_sort, tweq_lref, tweq_gref, tweq_abbr, tweq_abst, tweq_appl, tweq_cast/
qed-.

(* Left basic inversion lemmas **********************************************)

fact tweq_inv_sort_sn_aux:
     ∀X,Y. X ≅ Y → ∀s1. X = ⋆s1 → ∃s2. Y = ⋆s2.
#X #Y * -X -Y
[1  : #s1 #s2 #s #H destruct /2 width=2 by ex_intro/
|2,3: #i #s #H destruct
|4  : #p #V1 #V2 #T1 #T2 #_ #s #H destruct
|5  : #p #V1 #V2 #T1 #T2 #s #H destruct
|6  : #V1 #V2 #T1 #T2 #_ #s #H destruct
|7  : #V1 #V2 #T1 #T2 #_ #_ #s #H destruct
]
qed-.

lemma tweq_inv_sort_sn:
      ∀Y,s1. ⋆s1 ≅ Y → ∃s2. Y = ⋆s2.
/2 width=4 by tweq_inv_sort_sn_aux/ qed-.

fact tweq_inv_lref_sn_aux:
     ∀X,Y. X ≅ Y → ∀i. X = #i → Y = #i.
#X #Y * -X -Y
[1  : #s1 #s2 #j #H destruct
|2,3: //
|4  : #p #V1 #V2 #T1 #T2 #_ #j #H destruct
|5  : #p #V1 #V2 #T1 #T2 #j #H destruct
|6  : #V1 #V2 #T1 #T2 #_ #j #H destruct
|7  : #V1 #V2 #T1 #T2 #_ #_ #j #H destruct
]
qed-.

lemma tweq_inv_lref_sn: ∀Y,i. #i ≅ Y → Y = #i.
/2 width=5 by tweq_inv_lref_sn_aux/ qed-.

fact tweq_inv_gref_sn_aux:
     ∀X,Y. X ≅ Y → ∀l. X = §l → Y = §l.
#X #Y * -X -Y
[1  : #s1 #s2 #k #H destruct
|2,3: //
|4  : #p #V1 #V2 #T1 #T2 #_ #k #H destruct
|5  : #p #V1 #V2 #T1 #T2 #k #H destruct
|6  : #V1 #V2 #T1 #T2 #_ #k #H destruct
|7  : #V1 #V2 #T1 #T2 #_ #_ #j #H destruct
]
qed-.

lemma tweq_inv_gref_sn:
      ∀Y,l. §l ≅ Y → Y = §l.
/2 width=5 by tweq_inv_gref_sn_aux/ qed-.

fact tweq_inv_abbr_sn_aux:
     ∀X,Y. X ≅ Y → ∀p,V1,T1. X = ⓓ{p}V1.T1 →
     ∃∃V2,T2. p = Ⓣ → T1 ≅ T2 & Y = ⓓ{p}V2.T2.
#X #Y * -X -Y
[1  : #s1 #s2 #q #W1 #U1 #H destruct
|2,3: #i #q #W1 #U1 #H destruct
|4  : #p #V1 #V2 #T1 #T2 #HT #q #W1 #U1 #H destruct /3 width=4 by ex2_2_intro/
|5  : #p #V1 #V2 #T1 #T2 #q #W1 #U1 #H destruct
|6  : #V1 #V2 #T1 #T2 #_ #q #W1 #U1 #H destruct
|7  : #V1 #V2 #T1 #T2 #_ #_ #q #W1 #U1 #H destruct
]
qed-.

lemma tweq_inv_abbr_sn:
      ∀p,V1,T1,Y. ⓓ{p}V1.T1 ≅ Y →
      ∃∃V2,T2. p = Ⓣ → T1 ≅ T2 & Y = ⓓ{p}V2.T2.
/2 width=4 by tweq_inv_abbr_sn_aux/ qed-.

fact tweq_inv_abst_sn_aux:
     ∀X,Y. X ≅ Y → ∀p,V1,T1. X = ⓛ{p}V1.T1 →
     ∃∃V2,T2. Y = ⓛ{p}V2.T2.
#X #Y * -X -Y
[1  : #s1 #s2 #q #W1 #U1 #H destruct
|2,3: #i #q #W1 #U1 #H destruct
|4  : #p #V1 #V2 #T1 #T2 #_ #q #W1 #U1 #H destruct
|5  : #p #V1 #V2 #T1 #T2 #q #W1 #U1 #H destruct /2 width=3 by ex1_2_intro/
|6  : #V1 #V2 #T1 #T2 #_ #q #W1 #U1 #H destruct
|7  : #V1 #V2 #T1 #T2 #_ #_ #q #W1 #U1 #H destruct
]
qed-.

lemma tweq_inv_abst_sn:
      ∀p,V1,T1,Y. ⓛ{p}V1.T1 ≅ Y →
      ∃∃V2,T2. Y = ⓛ{p}V2.T2.
/2 width=5 by tweq_inv_abst_sn_aux/ qed-.

fact tweq_inv_appl_sn_aux:
     ∀X,Y. X ≅ Y → ∀V1,T1. X = ⓐV1.T1 →
     ∃∃V2,T2. T1 ≅ T2 & Y = ⓐV2.T2.
#X #Y * -X -Y
[1  : #s1 #s2 #W1 #U1 #H destruct
|2,3: #i #W1 #U1 #H destruct
|4  : #p #V1 #V2 #T1 #T2 #HT #W1 #U1 #H destruct
|5  : #p #V1 #V2 #T1 #T2 #W1 #U1 #H destruct
|6  : #V1 #V2 #T1 #T2 #HT #W1 #U1 #H destruct /2 width=4 by ex2_2_intro/
|7  : #V1 #V2 #T1 #T2 #_ #_ #W1 #U1 #H destruct
]
qed-.

lemma tweq_inv_appl_sn:
      ∀V1,T1,Y. ⓐV1.T1 ≅ Y →
      ∃∃V2,T2. T1 ≅ T2 & Y = ⓐV2.T2.
/2 width=4 by tweq_inv_appl_sn_aux/ qed-.

fact tweq_inv_cast_sn_aux:
     ∀X,Y. X ≅ Y → ∀V1,T1. X = ⓝV1.T1 →
     ∃∃V2,T2. V1 ≅ V2 & T1 ≅ T2 & Y = ⓝV2.T2.
#X #Y * -X -Y
[1  : #s1 #s2 #W1 #U1 #H destruct
|2,3: #i #W1 #U1 #H destruct
|4  : #p #V1 #V2 #T1 #T2 #_ #W1 #U1 #H destruct
|5  : #p #V1 #V2 #T1 #T2 #W1 #U1 #H destruct
|6  : #V1 #V2 #T1 #T2 #_ #W1 #U1 #H destruct
|7  : #V1 #V2 #T1 #T2 #HV #HT #W1 #U1 #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma tweq_inv_cast_sn:
      ∀V1,T1,Y. ⓝV1.T1 ≅ Y →
      ∃∃V2,T2. V1 ≅ V2 & T1 ≅ T2 & Y = ⓝV2.T2.
/2 width=3 by tweq_inv_cast_sn_aux/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma tweq_inv_abbr_pos_sn:
      ∀V1,T1,Y. +ⓓV1.T1 ≅ Y → ∃∃V2,T2. T1 ≅ T2 & Y = +ⓓV2.T2.
#V1 #V2 #Y #H
elim (tweq_inv_abbr_sn … H) -H #V2 #T2
/3 width=4 by ex2_2_intro/
qed-.

lemma tweq_inv_abbr_neg_sn:
      ∀V1,T1,Y. -ⓓV1.T1 ≅ Y → ∃∃V2,T2. Y = -ⓓV2.T2.
#V1 #V2 #Y #H
elim (tweq_inv_abbr_sn … H) -H #V2 #T2 #_
/2 width=3 by ex1_2_intro/
qed-.

lemma tweq_inv_abbr_pos_bi:
      ∀V1,V2,T1,T2. +ⓓV1.T1 ≅ +ⓓV2.T2 → T1 ≅ T2.
#V1 #V2 #T1 #T2 #H
elim (tweq_inv_abbr_pos_sn … H) -H #W2 #U2 #HTU #H destruct //
qed-.

lemma tweq_inv_appl_bi:
      ∀V1,V2,T1,T2. ⓐV1.T1 ≅ ⓐV2.T2 → T1 ≅ T2.
#V1 #V2 #T1 #T2 #H
elim (tweq_inv_appl_sn … H) -H #W2 #U2 #HTU #H destruct //
qed-.

lemma tweq_inv_cast_bi:
      ∀V1,V2,T1,T2. ⓝV1.T1 ≅ ⓝV2.T2 → ∧∧ V1 ≅ V2 & T1 ≅ T2.
#V1 #V2 #T1 #T2 #H
elim (tweq_inv_cast_sn … H) -H #W2 #U2 #HVW #HTU #H destruct
/2 width=1 by conj/
qed-.

lemma tweq_inv_cast_xy_y: ∀T,V. ⓝV.T ≅ T → ⊥.
@(f_ind … tw) #n #IH #T #Hn #V #H destruct
elim (tweq_inv_cast_sn … H) -H #X1 #X2 #_ #HX2 #H destruct -V
/2 width=4 by/
qed-.

(* Advanced forward lemmas **************************************************)

lemma tweq_fwd_pair_sn (I):
      ∀V1,T1,X2. ②{I}V1.T1 ≅ X2 → ∃∃V2,T2. X2 = ②{I}V2.T2.
* [ #p ] * [ cases p -p ] #V1 #T1 #X2 #H
[ elim (tweq_inv_abbr_pos_sn … H) -H #V2 #T2 #_ #H
| elim (tweq_inv_abbr_neg_sn … H) -H #V2 #T2 #H
| elim (tweq_inv_abst_sn … H) -H #V2 #T2 #H
| elim (tweq_inv_appl_sn … H) -H #V2 #T2 #_ #H
| elim (tweq_inv_cast_sn … H) -H #V2 #T2 #_ #_ #H
] /2 width=3 by ex1_2_intro/
qed-.

lemma tweq_fwd_pair_bi (I1) (I2):
      ∀V1,V2,T1,T2. ②{I1}V1.T1 ≅ ②{I2}V2.T2 → I1 = I2.
#I1 #I2 #V1 #V2 #T1 #T2 #H
elim (tweq_fwd_pair_sn … H) -H #W2 #U2 #H destruct //
qed-.

(* Advanced properties ******************************************************)

lemma tweq_dec: ∀T1,T2. Decidable (T1 ≅ T2).
#T1 elim T1 -T1 [ * #s1 | #I1 #V1 #T1 #IHV #IHT ] * [1,3,5,7: * #s2 |*: #I2 #V2 #T2 ]
[ /3 width=1 by tweq_sort, or_introl/
|2,3,13:
  @or_intror #H
  elim (tweq_inv_sort_sn … H) -H #x #H destruct
|4,6,14:
  @or_intror #H
  lapply (tweq_inv_lref_sn … H) -H #H destruct
|5:
  elim (eq_nat_dec s1 s2) #Hs12 destruct /2 width=1 by or_introl/
  @or_intror #H
  lapply (tweq_inv_lref_sn … H) -H #H destruct /2 width=1 by/
|7,8,15:
  @or_intror #H
  lapply (tweq_inv_gref_sn … H) -H #H destruct
|9:
  elim (eq_nat_dec s1 s2) #Hs12 destruct /2 width=1 by or_introl/
  @or_intror #H
  lapply (tweq_inv_gref_sn … H) -H #H destruct /2 width=1 by/
|10,11,12:
  @or_intror #H
  elim (tweq_fwd_pair_sn … H) -H #X1 #X2 #H destruct
|16:
  elim (eq_item2_dec I1 I2) #HI12 destruct
  [ cases I2 -I2 [ #p ] * [ cases p -p ]
    [ elim (IHT T2) -IHT #HT12
      [ /3 width=1 by tweq_abbr_pos, or_introl/
      | /4 width=3 by tweq_inv_abbr_pos_bi, or_intror/
      ]
    | /3 width=1 by tweq_abbr_neg, or_introl/
    | /3 width=1 by tweq_abst, or_introl/
    | elim (IHT T2) -IHT #HT12
      [ /3 width=1 by tweq_appl, or_introl/
      | /4 width=3 by tweq_inv_appl_bi, or_intror/
      ]
    | elim (IHV V2) -IHV #HV12
      elim (IHT T2) -IHT #HT12
      [1: /3 width=1 by tweq_cast, or_introl/
      |*: @or_intror #H
          elim (tweq_inv_cast_bi … H) -H #HV12 #HT12
          /2 width=1 by/
      ]
    ]
  | /4 width=5 by tweq_fwd_pair_bi, or_intror/
  ]
]
qed-.
