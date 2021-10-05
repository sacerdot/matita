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

include "ground/xoa/or_3.ma".
include "ground/xoa/ex_3_2.ma".
include "static_2/notation/relations/stareq_3.ma".
include "static_2/syntax/term.ma".

(* GENERIC EQUIVALENCE ON TERMS *********************************************)

inductive teqg (S:relation …): relation term ≝
| teqg_sort: ∀s1,s2. S s1 s2 → teqg S (⋆s1) (⋆s2)
| teqg_lref: ∀i. teqg S (#i) (#i)
| teqg_gref: ∀l. teqg S (§l) (§l)
| teqg_pair: ∀I,V1,V2,T1,T2. teqg S V1 V2 → teqg S T1 T2 → teqg S (②[I]V1.T1) (②[I]V2.T2)
.

interpretation
  "context-free generic equivalence (term)"
  'StarEq S T1 T2 = (teqg S T1 T2).

(* Basic properties *********************************************************)

lemma teqg_refl (S):
      reflexive … S → reflexive … (teqg S).
#S #HS #T elim T -T /2 width=1 by teqg_pair/
* /2 width=1 by teqg_sort, teqg_lref, teqg_gref/
qed.

lemma teqg_sym (S):
      symmetric … S → symmetric … (teqg S).
#S #HS #T1 #T2 #H elim H -T1 -T2
/3 width=3 by teqg_sort, teqg_lref, teqg_gref, teqg_pair/
qed-.

alias symbol "subseteq" (instance 3) = "relation inclusion".
lemma teqg_co (S1) (S2):
      S1 ⊆ S2 →
      ∀T1,T2. T1 ≛[S1] T2 → T1 ≛[S2] T2.
#S1 #S2 #HS #T1 #T2 #H elim H -T1 -T2
/3 width=1 by teqg_pair, teqg_sort/
qed-.

(* Basic inversion lemmas ***************************************************)

fact teqg_inv_sort1_aux (S):
     ∀X,Y. X ≛[S] Y → ∀s1. X = ⋆s1 →
     ∃∃s2. S s1 s2 & Y = ⋆s2.
#S #X #Y * -X -Y
[ #s1 #s2 #Hs12 #s #H destruct /2 width=3 by ex2_intro/
| #i #s #H destruct
| #l #s #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #s #H destruct
]
qed-.

lemma teqg_inv_sort1 (S):
      ∀Y,s1. ⋆s1 ≛[S] Y →
      ∃∃s2. S s1 s2 & Y = ⋆s2.
/2 width=4 by teqg_inv_sort1_aux/ qed-.

fact teqg_inv_lref1_aux (S):
     ∀X,Y. X ≛[S] Y → ∀i. X = #i → Y = #i.
#S #X #Y * -X -Y //
[ #s1 #s2 #_ #j #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #j #H destruct
]
qed-.

lemma teqg_inv_lref1 (S):
      ∀Y,i. #i ≛[S] Y → Y = #i.
/2 width=5 by teqg_inv_lref1_aux/ qed-.

fact teqg_inv_gref1_aux (S):
     ∀X,Y. X ≛[S] Y → ∀l. X = §l → Y = §l.
#S #X #Y * -X -Y //
[ #s1 #s2 #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #k #H destruct
]
qed-.

lemma teqg_inv_gref1 (S):
      ∀Y,l. §l ≛[S] Y → Y = §l.
/2 width=5 by teqg_inv_gref1_aux/ qed-.

fact teqg_inv_pair1_aux (S):
     ∀X,Y. X ≛[S] Y → ∀I,V1,T1. X = ②[I]V1.T1 →
     ∃∃V2,T2. V1 ≛[S] V2 & T1 ≛[S] T2 & Y = ②[I]V2.T2.
#S #X #Y * -X -Y
[ #s1 #s2 #_ #J #W1 #U1 #H destruct
| #i #J #W1 #U1 #H destruct
| #l #J #W1 #U1 #H destruct
| #I #V1 #V2 #T1 #T2 #HV #HT #J #W1 #U1 #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma teqg_inv_pair1 (S):
      ∀I,V1,T1,Y. ②[I]V1.T1 ≛[S] Y →
      ∃∃V2,T2. V1 ≛[S] V2 & T1 ≛[S] T2 & Y = ②[I]V2.T2.
/2 width=3 by teqg_inv_pair1_aux/ qed-.

fact teqg_inv_sort2_aux (S):
     ∀X,Y. X ≛[S] Y → ∀s2. Y = ⋆s2 →
     ∃∃s1. S s1 s2 & X = ⋆s1.
#S #X #Y * -X -Y
[ #s1 #s2 #Hs12 #s #H destruct /2 width=3 by ex2_intro/
| #i #s #H destruct
| #l #s #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #s #H destruct
]
qed-.

lemma teqg_inv_sort2 (S):
      ∀X1,s2. X1 ≛[S] ⋆s2 →
      ∃∃s1. S s1 s2 & X1 = ⋆s1.
/2 width=3 by teqg_inv_sort2_aux/ qed-.

fact teqg_inv_pair2_aux (S):
     ∀X,Y. X ≛[S] Y → ∀I,V2,T2. Y = ②[I]V2.T2 →
     ∃∃V1,T1. V1 ≛[S] V2 & T1 ≛[S] T2 & X = ②[I]V1.T1.
#S #X #Y * -X -Y
[ #s1 #s2 #_ #J #W2 #U2 #H destruct
| #i #J #W2 #U2 #H destruct
| #l #J #W2 #U2 #H destruct
| #I #V1 #V2 #T1 #T2 #HV #HT #J #W2 #U2 #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma teqg_inv_pair2 (S):
      ∀I,X1,V2,T2. X1 ≛[S] ②[I]V2.T2 →
      ∃∃V1,T1. V1 ≛[S] V2 & T1 ≛[S] T2 & X1 = ②[I]V1.T1.
/2 width=3 by teqg_inv_pair2_aux/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma teqg_inv_pair (S):
      ∀I1,I2,V1,V2,T1,T2. ②[I1]V1.T1 ≛[S] ②[I2]V2.T2 →
      ∧∧ I1 = I2 & V1 ≛[S] V2 & T1 ≛[S] T2.
#S #I1 #I2 #V1 #V2 #T1 #T2 #H elim (teqg_inv_pair1 … H) -H
#V0 #T0 #HV #HT #H destruct /2 width=1 by and3_intro/
qed-.

lemma teqg_inv_pair_xy_x (S):
      ∀I,V,T. ②[I]V.T ≛[S] V → ⊥.
#S #I #V elim V -V
[ #J #T #H elim (teqg_inv_pair1 … H) -H #X #Y #_ #_ #H destruct
| #J #X #Y #IHX #_ #T #H elim (teqg_inv_pair … H) -H #H #HY #_ destruct /2 width=2 by/
]
qed-.

lemma teqg_inv_pair_xy_y (S):
      ∀I,T,V. ②[I]V.T ≛[S] T → ⊥.
#S #I #T elim T -T
[ #J #V #H elim (teqg_inv_pair1 … H) -H #X #Y #_ #_ #H destruct
| #J #X #Y #_ #IHY #V #H elim (teqg_inv_pair … H) -H #H #_ #HY destruct /2 width=2 by/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma teqg_fwd_atom1 (S):
      ∀I,Y. ⓪[I] ≛[S] Y → ∃J. Y = ⓪[J].
#S * #x #Y #H [ elim (teqg_inv_sort1 … H) -H ]
/3 width=4 by teqg_inv_gref1, teqg_inv_lref1, ex_intro/
qed-.

(* Advanced properties ******************************************************)

lemma teqg_dec (S):
      (∀s1,s2. Decidable (S s1 s2)) →
      ∀T1,T2. Decidable (T1 ≛[S] T2).
#S #HS #T1 elim T1 -T1 [ * #s1 | #I1 #V1 #T1 #IHV #IHT ] * [1,3,5,7: * #s2 |*: #I2 #V2 #T2 ]
[ elim (HS s1 s2) -HS [ /3 width=1 by or_introl, teqg_sort/ ] #HS
  @or_intror #H
  elim (teqg_inv_sort1 … H) -H #x #Hx #H destruct /2 width=1 by/
|2,3,13:
  @or_intror #H
  elim (teqg_inv_sort1 … H) -H #x #_ #H destruct
|4,6,14:
  @or_intror #H
  lapply (teqg_inv_lref1 … H) -H #H destruct
|5:
  elim (eq_nat_dec s1 s2) #Hs12 destruct /2 width=1 by or_introl/
  @or_intror #H
  lapply (teqg_inv_lref1 … H) -H #H destruct /2 width=1 by/
|7,8,15:
  @or_intror #H
  lapply (teqg_inv_gref1 … H) -H #H destruct
|9:
  elim (eq_nat_dec s1 s2) #Hs12 destruct /2 width=1 by or_introl/
  @or_intror #H
  lapply (teqg_inv_gref1 … H) -H #H destruct /2 width=1 by/
|10,11,12:
  @or_intror #H
  elim (teqg_inv_pair1 … H) -H #X1 #X2 #_ #_ #H destruct
|16:
  elim (eq_item2_dec I1 I2) #HI12 destruct
  [ elim (IHV V2) -IHV #HV12
    elim (IHT T2) -IHT #HT12
    [ /3 width=1 by teqg_pair, or_introl/ ]
  ]
  @or_intror #H
  elim (teqg_inv_pair … H) -H /2 width=1 by/
]
qed-.

(* Negated inversion lemmas *************************************************)

lemma tneqg_inv_pair (S):
      (∀s1,s2. Decidable (S s1 s2)) →
      ∀I1,I2,V1,V2,T1,T2.
      (②[I1]V1.T1 ≛[S] ②[I2]V2.T2 → ⊥) →
      ∨∨ I1 = I2 → ⊥
       | (V1 ≛[S] V2 → ⊥)
       | (T1 ≛[S] T2 → ⊥).
#S #HS #I1 #I2 #V1 #V2 #T1 #T2 #H12
elim (eq_item2_dec I1 I2) /3 width=1 by or3_intro0/ #H destruct
elim (teqg_dec S … V1 V2) /3 width=1 by or3_intro1/
elim (teqg_dec S … T1 T2) /4 width=1 by teqg_pair, or3_intro2/
qed-.
