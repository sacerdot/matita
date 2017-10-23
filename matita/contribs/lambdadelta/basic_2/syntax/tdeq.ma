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

include "basic_2/notation/relations/lazyeq_4.ma".
include "basic_2/syntax/item_sd.ma".
include "basic_2/syntax/term.ma".

(* DEGREE-BASED EQUIVALENCE ON TERMS ****************************************)

inductive tdeq (h) (o): relation term ≝
| tdeq_sort: ∀s1,s2,d. deg h o s1 d → deg h o s2 d → tdeq h o (⋆s1) (⋆s2)
| tdeq_lref: ∀i. tdeq h o (#i) (#i)
| tdeq_gref: ∀l. tdeq h o (§l) (§l)
| tdeq_pair: ∀I,V1,V2,T1,T2. tdeq h o V1 V2 → tdeq h o T1 T2 → tdeq h o (②{I}V1.T1) (②{I}V2.T2)
.

interpretation
   "context-free degree-based equivalence (term)"
   'LazyEq h o T1 T2 = (tdeq h o T1 T2).

(* Basic inversion lemmas ***************************************************)

fact tdeq_inv_sort1_aux: ∀h,o,X,Y. X ≡[h, o] Y → ∀s1. X = ⋆s1 →
                         ∃∃s2,d. deg h o s1 d & deg h o s2 d & Y = ⋆s2.
#h #o #X #Y * -X -Y
[ #s1 #s2 #d #Hs1 #Hs2 #s #H destruct /2 width=5 by ex3_2_intro/
| #i #s #H destruct
| #l #s #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #s #H destruct
]
qed-.

lemma tdeq_inv_sort1: ∀h,o,Y,s1. ⋆s1 ≡[h, o] Y →
                      ∃∃s2,d. deg h o s1 d & deg h o s2 d & Y = ⋆s2.
/2 width=3 by tdeq_inv_sort1_aux/ qed-.

fact tdeq_inv_lref1_aux: ∀h,o,X,Y. X ≡[h, o] Y → ∀i. X = #i → Y = #i.
#h #o #X #Y * -X -Y //
[ #s1 #s2 #d #_ #_ #j #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #j #H destruct
]
qed-.

lemma tdeq_inv_lref1: ∀h,o,Y,i. #i ≡[h, o] Y → Y = #i.
/2 width=5 by tdeq_inv_lref1_aux/ qed-.

fact tdeq_inv_gref1_aux: ∀h,o,X,Y. X ≡[h, o] Y → ∀l. X = §l → Y = §l.
#h #o #X #Y * -X -Y //
[ #s1 #s2 #d #_ #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #_ #_ #k #H destruct
]
qed-.

lemma tdeq_inv_gref1: ∀h,o,Y,l. §l ≡[h, o] Y → Y = §l.
/2 width=5 by tdeq_inv_gref1_aux/ qed-.

fact tdeq_inv_pair1_aux: ∀h,o,X,Y. X ≡[h, o] Y → ∀I,V1,T1. X = ②{I}V1.T1 →
                         ∃∃V2,T2. V1 ≡[h, o] V2 & T1 ≡[h, o] T2 & Y = ②{I}V2.T2.
#h #o #X #Y * -X -Y
[ #s1 #s2 #d #_ #_ #J #W1 #U1 #H destruct
| #i #J #W1 #U1 #H destruct
| #l #J #W1 #U1 #H destruct
| #I #V1 #V2 #T1 #T2 #HV #HT #J #W1 #U1 #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma tdeq_inv_pair1: ∀h,o,I,V1,T1,Y. ②{I}V1.T1 ≡[h, o] Y →
                      ∃∃V2,T2. V1 ≡[h, o] V2 & T1 ≡[h, o] T2 & Y = ②{I}V2.T2.
/2 width=3 by tdeq_inv_pair1_aux/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma tdeq_inv_sort1_deg: ∀h,o,Y,s1. ⋆s1 ≡[h, o] Y → ∀d. deg h o s1 d →
                          ∃∃s2. deg h o s2 d & Y = ⋆s2.
#h #o #Y #s1 #H #d #Hs1 elim (tdeq_inv_sort1 … H) -H
#s2 #x #Hx <(deg_mono h o … Hx … Hs1) -s1 -d /2 width=3 by ex2_intro/
qed-.

lemma tdeq_inv_sort_deg: ∀h,o,s1,s2. ⋆s1 ≡[h, o] ⋆s2 →
                         ∀d1,d2. deg h o s1 d1 → deg h o s2 d2 →
                         d1 = d2.
#h #o #s1 #y #H #d1 #d2 #Hs1 #Hy
elim (tdeq_inv_sort1_deg … H … Hs1) -s1 #s2 #Hs2 #H destruct
<(deg_mono h o … Hy … Hs2) -s2 -d1 //
qed-.

lemma tdeq_inv_pair: ∀h,o,I1,I2,V1,V2,T1,T2. ②{I1}V1.T1 ≡[h, o] ②{I2}V2.T2 →
                     ∧∧ I1 = I2 & V1 ≡[h, o] V2 & T1 ≡[h, o] T2.
#h #o #I1 #I2 #V1 #V2 #T1 #T2 #H elim (tdeq_inv_pair1 … H) -H
#V0 #T0 #HV #HT #H destruct /2 width=1 by and3_intro/
qed-.

lemma tdeq_inv_pair_xy_y: ∀h,o,I,T,V. ②{I}V.T ≡[h, o] T → ⊥.
#h #o #I #T elim T -T
[ #J #V #H elim (tdeq_inv_pair1 … H) -H #X #Y #_ #_ #H destruct
| #J #X #Y #_ #IHY #V #H elim (tdeq_inv_pair … H) -H #H #_ #HY destruct /2 width=2 by/
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma tdeq_fwd_atom1: ∀h,o,I,Y. ⓪{I} ≡[h, o] Y → ∃J. Y = ⓪{J}.
#h #o * #x #Y #H [ elim (tdeq_inv_sort1 … H) -H ]
/3 width=4 by tdeq_inv_gref1, tdeq_inv_lref1, ex_intro/
qed-.

(* Basic properties *********************************************************)

lemma tdeq_refl: ∀h,o. reflexive … (tdeq h o).
#h #o #T elim T -T /2 width=1 by tdeq_pair/
* /2 width=1 by tdeq_lref, tdeq_gref/
#s elim (deg_total h o s) /2 width=3 by tdeq_sort/
qed.

lemma tdeq_sym: ∀h,o. symmetric … (tdeq h o).
#h #o #T1 #T2 #H elim H -T1 -T2
/2 width=3 by tdeq_sort, tdeq_lref, tdeq_gref, tdeq_pair/
qed-.

lemma tdeq_dec: ∀h,o,T1,T2. Decidable (T1 ≡[h, o] T2).
#h #o #T1 elim T1 -T1 [ * #s1 | #I1 #V1 #T1 #IHV #IHT ] * [1,3,5,7: * #s2 |*: #I2 #V2 #T2 ]
[ elim (deg_total h o s1) #d1 #H1
  elim (deg_total h o s2) #d2 #H2
  elim (eq_nat_dec d1 d2) #Hd12 destruct /3 width=3 by tdeq_sort, or_introl/
  @or_intror #H
  lapply (tdeq_inv_sort_deg … H … H1 H2) -H -H1 -H2 /2 width=1 by/
|2,3,13:
  @or_intror #H
  elim (tdeq_inv_sort1 … H) -H #x1 #x2 #_ #_ #H destruct
|4,6,14:
  @or_intror #H
  lapply (tdeq_inv_lref1 … H) -H #H destruct
|5:
  elim (eq_nat_dec s1 s2) #Hs12 destruct /2 width=1 by or_introl/
  @or_intror #H
  lapply (tdeq_inv_lref1 … H) -H #H destruct /2 width=1 by/
|7,8,15:
  @or_intror #H
  lapply (tdeq_inv_gref1 … H) -H #H destruct
|9:
  elim (eq_nat_dec s1 s2) #Hs12 destruct /2 width=1 by or_introl/
  @or_intror #H
  lapply (tdeq_inv_gref1 … H) -H #H destruct /2 width=1 by/
|10,11,12:
  @or_intror #H
  elim (tdeq_inv_pair1 … H) -H #X1 #X2 #_ #_ #H destruct
|16:
  elim (eq_item2_dec I1 I2) #HI12 destruct
  [ elim (IHV V2) -IHV #HV12
    elim (IHT T2) -IHT #HT12
    [ /3 width=1 by tdeq_pair, or_introl/ ]
  ]
  @or_intror #H
  elim (tdeq_inv_pair … H) -H /2 width=1 by/
]
qed-.

(* Negated inversion lemmas *************************************************)

lemma tdneq_inv_pair: ∀h,o,I1,I2,V1,V2,T1,T2.
                      (②{I1}V1.T1 ≡[h, o] ②{I2}V2.T2 → ⊥) → 
                      ∨∨ I1 = I2 → ⊥
                      |  (V1 ≡[h, o] V2 → ⊥)
                      |  (T1 ≡[h, o] T2 → ⊥).
#h #o #I1 #I2 #V1 #V2 #T1 #T2 #H12
elim (eq_item2_dec I1 I2) /3 width=1 by or3_intro0/ #H destruct
elim (tdeq_dec h o V1 V2) /3 width=1 by or3_intro1/
elim (tdeq_dec h o T1 T2) /4 width=1 by tdeq_pair, or3_intro2/
qed-.
