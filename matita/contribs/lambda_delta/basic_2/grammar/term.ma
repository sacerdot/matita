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
   'SnBind2 I T1 T2 = (TPair (Bind2 I) T1 T2).

interpretation "term flat construction (binary)"
   'SnFlat2 I T1 T2 = (TPair (Flat2 I) T1 T2).

interpretation "sort (term)"
   'Star k = (TAtom (Sort k)).

interpretation "local reference (term)"
   'LRef i = (TAtom (LRef i)).

interpretation "global reference (term)"
   'GRef p = (TAtom (GRef p)).

interpretation "abbreviation (term)"
   'SnAbbr T1 T2 = (TPair (Bind2 Abbr) T1 T2).

interpretation "abstraction (term)"
   'SnAbst T1 T2 = (TPair (Bind2 Abst) T1 T2).

interpretation "application (term)"
   'SnAppl T1 T2 = (TPair (Flat2 Appl) T1 T2).

interpretation "native type annotation (term)"
   'SnCast T1 T2 = (TPair (Flat2 Cast) T1 T2).

(* Basic properties *********************************************************)

(* Basic_1: was: term_dec *)
axiom term_eq_dec: ∀T1,T2:term. Decidable (T1 = T2).

(* Basic inversion lemmas ***************************************************)

lemma discr_tpair_xy_x: ∀I,T,V. ②{I} V. T = V → ⊥.
#I #T #V elim V -V
[ #J #H destruct
| #J #W #U #IHW #_ #H destruct
  -H >e0 in e1; normalize (**) (* destruct: one quality is not simplified, the destucted equality is not erased *)
  /2 width=1/
]
qed-.

(* Basic_1: was: thead_x_y_y *)
lemma discr_tpair_xy_y: ∀I,V,T. ②{I} V. T = T → ⊥.
#I #V #T elim T -T
[ #J #H destruct
| #J #W #U #_ #IHU #H destruct
  -H (**) (* destruct: the destucted equality is not erased *)
  /2 width=1/
]
qed-.

lemma eq_false_inv_tpair_sn: ∀I,V1,T1,V2,T2.
                             (②{I} V1. T1 = ②{I} V2. T2 → ⊥) →
                             (V1 = V2 → ⊥) ∨ (V1 = V2 ∧ (T1 = T2 → ⊥)).
#I #V1 #T1 #V2 #T2 #H
elim (term_eq_dec V1 V2) /3 width=1/ #HV12 destruct
@or_intror @conj // #HT12 destruct /2 width=1/ 
qed-.

lemma eq_false_inv_tpair_dx: ∀I,V1,T1,V2,T2.
                             (②{I} V1. T1 = ②{I} V2. T2 → ⊥) →
                             (T1 = T2 → ⊥) ∨ (T1 = T2 ∧ (V1 = V2 → ⊥)).
#I #V1 #T1 #V2 #T2 #H
elim (term_eq_dec T1 T2) /3 width=1/ #HT12 destruct
@or_intror @conj // #HT12 destruct /2 width=1/
qed-.

lemma eq_false_inv_beta: ∀V1,V2,W1,W2,T1,T2.
                         (ⓐV1. ⓛW1. T1 = ⓐV2. ⓛW2 .T2 →⊥) →
                         (W1 = W2 → ⊥) ∨
                         (W1 = W2 ∧ (ⓓV1. T1 = ⓓV2. T2 → ⊥)).
#V1 #V2 #W1 #W2 #T1 #T2 #H
elim (eq_false_inv_tpair_sn … H) -H
[ #HV12 elim (term_eq_dec W1 W2) /3 width=1/
  #H destruct @or_intror @conj // #H destruct /2 width=1/
| * #H1 #H2 destruct
  elim (eq_false_inv_tpair_sn … H2) -H2 /3 width=1/
  * #H #HT12 destruct
  @or_intror @conj // #H destruct /2 width=1/
]
qed.

(* Basic_1: removed theorems 3:
            not_void_abst not_abbr_void not_abst_void
*)
