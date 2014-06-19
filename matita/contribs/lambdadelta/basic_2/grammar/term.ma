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

include "basic_2/notation/constructors/item0_1.ma".
include "basic_2/notation/constructors/snitem2_3.ma".
include "basic_2/notation/constructors/snbind2_4.ma".
include "basic_2/notation/constructors/snbind2pos_3.ma".
include "basic_2/notation/constructors/snbind2neg_3.ma".
include "basic_2/notation/constructors/snflat2_3.ma".
include "basic_2/notation/constructors/star_1.ma".
include "basic_2/notation/constructors/lref_1.ma".
include "basic_2/notation/constructors/gref_1.ma".
include "basic_2/notation/constructors/snabbr_3.ma".
include "basic_2/notation/constructors/snabbrpos_2.ma".
include "basic_2/notation/constructors/snabbrneg_2.ma".
include "basic_2/notation/constructors/snabst_3.ma".
include "basic_2/notation/constructors/snabstpos_2.ma".
include "basic_2/notation/constructors/snabstneg_2.ma".
include "basic_2/notation/constructors/snappl_2.ma".
include "basic_2/notation/constructors/sncast_2.ma".
include "basic_2/grammar/item.ma".

(* TERMS ********************************************************************)

(* terms *)
inductive term: Type[0] ≝
  | TAtom: item0 → term               (* atomic item construction *)
  | TPair: item2 → term → term → term (* binary item construction *)
.

interpretation "term construction (atomic)"
   'Item0 I = (TAtom I).

interpretation "term construction (binary)"
   'SnItem2 I T1 T2 = (TPair I T1 T2).

interpretation "term binding construction (binary)"
   'SnBind2 a I T1 T2 = (TPair (Bind2 a I) T1 T2).

interpretation "term positive binding construction (binary)"
   'SnBind2Pos I T1 T2 = (TPair (Bind2 true I) T1 T2).

interpretation "term negative binding construction (binary)"
   'SnBind2Neg I T1 T2 = (TPair (Bind2 false I) T1 T2).

interpretation "term flat construction (binary)"
   'SnFlat2 I T1 T2 = (TPair (Flat2 I) T1 T2).

interpretation "sort (term)"
   'Star k = (TAtom (Sort k)).

interpretation "local reference (term)"
   'LRef i = (TAtom (LRef i)).

interpretation "global reference (term)"
   'GRef p = (TAtom (GRef p)).

interpretation "abbreviation (term)"
   'SnAbbr a T1 T2 = (TPair (Bind2 a Abbr) T1 T2).

interpretation "positive abbreviation (term)"
   'SnAbbrPos T1 T2 = (TPair (Bind2 true Abbr) T1 T2).

interpretation "negative abbreviation (term)"
   'SnAbbrNeg T1 T2 = (TPair (Bind2 false Abbr) T1 T2).

interpretation "abstraction (term)"
   'SnAbst a T1 T2 = (TPair (Bind2 a Abst) T1 T2).

interpretation "positive abstraction (term)"
   'SnAbstPos T1 T2 = (TPair (Bind2 true Abst) T1 T2).

interpretation "negative abstraction (term)"
   'SnAbstNeg T1 T2 = (TPair (Bind2 false Abst) T1 T2).

interpretation "application (term)"
   'SnAppl T1 T2 = (TPair (Flat2 Appl) T1 T2).

interpretation "native type annotation (term)"
   'SnCast T1 T2 = (TPair (Flat2 Cast) T1 T2).

(* Basic properties *********************************************************)

(* Basic_1: was: term_dec *)
lemma eq_term_dec: ∀T1,T2:term. Decidable (T1 = T2).
#T1 elim T1 -T1 #I1 [| #V1 #T1 #IHV1 #IHT1 ] * #I2 [2,4: #V2 #T2 ]
[1,4: @or_intror #H destruct
| elim (eq_item2_dec I1 I2) #HI
  [ elim (IHV1 V2) -IHV1 #HV
    [ elim (IHT1 T2) -IHT1 /2 width=1 by or_introl/ #HT ]
  ]
  @or_intror #H destruct /2 width=1 by/
| elim (eq_item0_dec I1 I2) /2 width=1 by or_introl/ #HI
  @or_intror #H destruct /2 width=1 by/
]
qed-.

(* Basic inversion lemmas ***************************************************)

lemma destruct_tpair_tpair: ∀I1,I2,T1,T2,V1,V2. ②{I1}T1.V1 = ②{I2}T2.V2 →
                            ∧∧T1 = T2 & I1 = I2 & V1 = V2.
#I1 #I2 #T1 #T2 #V1 #V2 #H destruct /2 width=1 by and3_intro/
qed-.

lemma discr_tpair_xy_x: ∀I,T,V. ②{I} V. T = V → ⊥.
#I #T #V elim V -V
[ #J #H destruct
| #J #W #U #IHW #_ #H elim (destruct_tpair_tpair … H) -H /2 width=1 by/ (**) (* destruct lemma needed *)
]
qed-.

(* Basic_1: was: thead_x_y_y *)
lemma discr_tpair_xy_y: ∀I,V,T. ②{I} V. T = T → ⊥.
#I #V #T elim T -T
[ #J #H destruct
| #J #W #U #_ #IHU #H elim (destruct_tpair_tpair … H) -H /2 width=1 by/ (**) (* destruct lemma needed *)
]
qed-.

lemma eq_false_inv_tpair_sn: ∀I,V1,T1,V2,T2.
                             (②{I} V1. T1 = ②{I} V2. T2 → ⊥) →
                             (V1 = V2 → ⊥) ∨ (V1 = V2 ∧ (T1 = T2 → ⊥)).
#I #V1 #T1 #V2 #T2 #H
elim (eq_term_dec V1 V2) /3 width=1 by or_introl/ #HV12 destruct
@or_intror @conj // #HT12 destruct /2 width=1 by/
qed-.

lemma eq_false_inv_tpair_dx: ∀I,V1,T1,V2,T2.
                             (②{I} V1. T1 = ②{I} V2. T2 → ⊥) →
                             (T1 = T2 → ⊥) ∨ (T1 = T2 ∧ (V1 = V2 → ⊥)).
#I #V1 #T1 #V2 #T2 #H
elim (eq_term_dec T1 T2) /3 width=1 by or_introl/ #HT12 destruct
@or_intror @conj // #HT12 destruct /2 width=1 by/
qed-.

(* Basic_1: removed theorems 3:
            not_void_abst not_abbr_void not_abst_void
*)
