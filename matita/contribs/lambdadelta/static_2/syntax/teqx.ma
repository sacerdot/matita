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

include "static_2/notation/relations/stareq_2.ma".
include "static_2/syntax/term.ma".

(* SORT-IRRELEVANT EQUIVALENCE ON TERMS *************************************)

inductive teqx: relation term ≝
| teqx_sort: ∀s1,s2. teqx (⋆s1) (⋆s2)
| teqx_lref: ∀i. teqx (#i) (#i)
| teqx_gref: ∀l. teqx (§l) (§l)
| teqx_pair: ∀I,V1,V2,T1,T2. teqx V1 V2 → teqx T1 T2 → teqx (②{I}V1.T1) (②{I}V2.T2)
.

interpretation
   "context-free sort-irrelevant equivalence (term)"
   'StarEq T1 T2 = (teqx T1 T2).

(* Basic properties *********************************************************)

lemma teqx_refl: reflexive … teqx.
#T elim T -T /2 width=1 by teqx_pair/
* /2 width=1 by teqx_lref, teqx_gref/
qed.

lemma teqx_sym: symmetric … teqx.
#T1 #T2 #H elim H -T1 -T2
/2 width=3 by teqx_sort, teqx_lref, teqx_gref, teqx_pair/
qed-.

(* Basic inversion lemmas ***************************************************)

fact teqx_inv_sort1_aux: ∀X,Y. X ≛ Y → ∀s1. X = ⋆s1 →
                         ∃s2. Y = ⋆s2.
#X #Y * -X -Y
[ #s1 #s2 #s #H destruct /2 width=2 by ex_intro/
| #i #s #H destruct
| #l #s #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #s #H destruct
]
qed-.

lemma teqx_inv_sort1: ∀Y,s1. ⋆s1 ≛ Y →
                      ∃s2. Y = ⋆s2.
/2 width=4 by teqx_inv_sort1_aux/ qed-.

fact teqx_inv_lref1_aux: ∀X,Y. X ≛ Y → ∀i. X = #i → Y = #i.
#X #Y * -X -Y //
[ #s1 #s2 #j #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #j #H destruct
]
qed-.

lemma teqx_inv_lref1: ∀Y,i. #i ≛ Y → Y = #i.
/2 width=5 by teqx_inv_lref1_aux/ qed-.

fact teqx_inv_gref1_aux: ∀X,Y. X ≛ Y → ∀l. X = §l → Y = §l.
#X #Y * -X -Y //
[ #s1 #s2 #k #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #k #H destruct
]
qed-.

lemma teqx_inv_gref1: ∀Y,l. §l ≛ Y → Y = §l.
/2 width=5 by teqx_inv_gref1_aux/ qed-.

fact teqx_inv_pair1_aux: ∀X,Y. X ≛ Y → ∀I,V1,T1. X = ②{I}V1.T1 →
                         ∃∃V2,T2. V1 ≛ V2 & T1 ≛ T2 & Y = ②{I}V2.T2.
#X #Y * -X -Y
[ #s1 #s2 #J #W1 #U1 #H destruct
| #i #J #W1 #U1 #H destruct
| #l #J #W1 #U1 #H destruct
| #I #V1 #V2 #T1 #T2 #HV #HT #J #W1 #U1 #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma teqx_inv_pair1: ∀I,V1,T1,Y. ②{I}V1.T1 ≛ Y →
                      ∃∃V2,T2. V1 ≛ V2 & T1 ≛ T2 & Y = ②{I}V2.T2.
/2 width=3 by teqx_inv_pair1_aux/ qed-.

lemma teqx_inv_sort2: ∀X1,s2. X1 ≛ ⋆s2 →
                      ∃s1. X1 = ⋆s1.
#X1 #s2 #H
elim (teqx_inv_sort1 X1 s2)
/2 width=2 by teqx_sym, ex_intro/
qed-.

lemma teqx_inv_pair2: ∀I,X1,V2,T2. X1 ≛ ②{I}V2.T2 →
                      ∃∃V1,T1. V1 ≛ V2 & T1 ≛ T2 & X1 = ②{I}V1.T1.
#I #X1 #V2 #T2 #H
elim (teqx_inv_pair1 I V2 T2 X1)
[ #V1 #T1 #HV #HT #H destruct ]
/3 width=5 by teqx_sym, ex3_2_intro/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma teqx_inv_pair: ∀I1,I2,V1,V2,T1,T2. ②{I1}V1.T1 ≛ ②{I2}V2.T2 →
                     ∧∧ I1 = I2 & V1 ≛ V2 & T1 ≛ T2.
#I1 #I2 #V1 #V2 #T1 #T2 #H elim (teqx_inv_pair1 … H) -H
#V0 #T0 #HV #HT #H destruct /2 width=1 by and3_intro/
qed-.

lemma teqx_inv_pair_xy_x: ∀I,V,T. ②{I}V.T ≛ V → ⊥.
#I #V elim V -V
[ #J #T #H elim (teqx_inv_pair1 … H) -H #X #Y #_ #_ #H destruct
| #J #X #Y #IHX #_ #T #H elim (teqx_inv_pair … H) -H #H #HY #_ destruct /2 width=2 by/
]
qed-.

lemma teqx_inv_pair_xy_y: ∀I,T,V. ②{I}V.T ≛ T → ⊥.
#I #T elim T -T
[ #J #V #H elim (teqx_inv_pair1 … H) -H #X #Y #_ #_ #H destruct
| #J #X #Y #_ #IHY #V #H elim (teqx_inv_pair … H) -H #H #_ #HY destruct /2 width=2 by/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma teqx_fwd_atom1: ∀I,Y. ⓪{I} ≛ Y → ∃J. Y = ⓪{J}.
* #x #Y #H [ elim (teqx_inv_sort1 … H) -H ]
/3 width=4 by teqx_inv_gref1, teqx_inv_lref1, ex_intro/
qed-.

(* Advanced properties ******************************************************)

lemma teqx_dec: ∀T1,T2. Decidable (T1 ≛ T2).
#T1 elim T1 -T1 [ * #s1 | #I1 #V1 #T1 #IHV #IHT ] * [1,3,5,7: * #s2 |*: #I2 #V2 #T2 ]
[ /3 width=1 by teqx_sort, or_introl/
|2,3,13:
  @or_intror #H
  elim (teqx_inv_sort1 … H) -H #x #H destruct
|4,6,14:
  @or_intror #H
  lapply (teqx_inv_lref1 … H) -H #H destruct
|5:
  elim (eq_nat_dec s1 s2) #Hs12 destruct /2 width=1 by or_introl/
  @or_intror #H
  lapply (teqx_inv_lref1 … H) -H #H destruct /2 width=1 by/
|7,8,15:
  @or_intror #H
  lapply (teqx_inv_gref1 … H) -H #H destruct
|9:
  elim (eq_nat_dec s1 s2) #Hs12 destruct /2 width=1 by or_introl/
  @or_intror #H
  lapply (teqx_inv_gref1 … H) -H #H destruct /2 width=1 by/
|10,11,12:
  @or_intror #H
  elim (teqx_inv_pair1 … H) -H #X1 #X2 #_ #_ #H destruct
|16:
  elim (eq_item2_dec I1 I2) #HI12 destruct
  [ elim (IHV V2) -IHV #HV12
    elim (IHT T2) -IHT #HT12
    [ /3 width=1 by teqx_pair, or_introl/ ]
  ]
  @or_intror #H
  elim (teqx_inv_pair … H) -H /2 width=1 by/
]
qed-.

(* Negated inversion lemmas *************************************************)

lemma tneqx_inv_pair: ∀I1,I2,V1,V2,T1,T2.
                      (②{I1}V1.T1 ≛ ②{I2}V2.T2 → ⊥) → 
                      ∨∨ I1 = I2 → ⊥
                      |  (V1 ≛ V2 → ⊥)
                      |  (T1 ≛ T2 → ⊥).
#I1 #I2 #V1 #V2 #T1 #T2 #H12
elim (eq_item2_dec I1 I2) /3 width=1 by or3_intro0/ #H destruct
elim (teqx_dec V1 V2) /3 width=1 by or3_intro1/
elim (teqx_dec T1 T2) /4 width=1 by teqx_pair, or3_intro2/
qed-.
