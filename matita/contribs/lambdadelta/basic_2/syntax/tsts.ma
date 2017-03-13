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

include "basic_2/notation/relations/topiso_4.ma".
include "basic_2/syntax/item_sd.ma".
include "basic_2/syntax/term.ma".

(* SAME TOP TERM STRUCTURE **************************************************)

(* Basic_2A1: includes: tsts_atom *)
inductive tsts (h) (o): relation term ≝
| tsts_sort: ∀s1,s2,d. deg h o s1 d → deg h o s2 d → tsts h o (⋆s1) (⋆s2)
| tsts_lref: ∀i. tsts h o (#i) (#i)
| tsts_gref: ∀l. tsts h o (§l) (§l)
| tsts_pair: ∀I,V1,V2,T1,T2. tsts h o (②{I}V1.T1) (②{I}V2.T2)
.

interpretation "same top structure (term)" 'TopIso h o T1 T2 = (tsts h o T1 T2).

(* Basic inversion lemmas ***************************************************)

fact tsts_inv_sort1_aux: ∀h,o,X,Y. X ⩳[h, o] Y → ∀s1. X = ⋆s1 →
                         ∃∃s2,d. deg h o s1 d & deg h o s2 d & Y = ⋆s2.
#h #o #X #Y * -X -Y
[ #s1 #s2 #d #Hs1 #Hs2 #s #H destruct /2 width=5 by ex3_2_intro/
| #i #s #H destruct
| #l #s #H destruct
| #I #V1 #V2 #T1 #T2 #s #H destruct
]
qed-.

(* Basic_1: was just: iso_gen_sort *)
lemma tsts_inv_sort1: ∀h,o,Y,s1. ⋆s1 ⩳[h, o] Y →
                      ∃∃s2,d. deg h o s1 d & deg h o s2 d & Y = ⋆s2.
/2 width=3 by tsts_inv_sort1_aux/ qed-.

fact tsts_inv_lref1_aux: ∀h,o,X,Y. X ⩳[h, o] Y → ∀i. X = #i → Y = #i.
#h #o #X #Y * -X -Y //
[ #s1 #s2 #d #_ #_ #j #H destruct
| #I #V1 #V2 #T1 #T2 #j #H destruct
]
qed-.

(* Basic_1: was: iso_gen_lref *)
lemma tsts_inv_lref1: ∀h,o,Y,i. #i ⩳[h, o] Y → Y = #i.
/2 width=5 by tsts_inv_lref1_aux/ qed-.

fact tsts_inv_gref1_aux: ∀h,o,X,Y. X ⩳[h, o] Y → ∀l. X = §l → Y = §l.
#h #o #X #Y * -X -Y //
[ #s1 #s2 #d #_ #_ #k #H destruct
| #I #V1 #V2 #T1 #T2 #k #H destruct
]
qed-.

lemma tsts_inv_gref1: ∀h,o,Y,l. §l ⩳[h, o] Y → Y = §l.
/2 width=5 by tsts_inv_gref1_aux/ qed-.

fact tsts_inv_pair1_aux: ∀h,o,T1,T2. T1 ⩳[h, o] T2 →
                         ∀I,W1,U1. T1 = ②{I}W1.U1 →
                         ∃∃W2,U2. T2 = ②{I}W2.U2.
#h #o #T1 #T2 * -T1 -T2
[ #s1 #s2 #d #_ #_ #J #W1 #U1 #H destruct
| #i #J #W1 #U1 #H destruct
| #l #J #W1 #U1 #H destruct
| #I #V1 #V2 #T1 #T2 #J #W1 #U1 #H destruct /2 width=3 by ex1_2_intro/
]
qed-.

(* Basic_1: was: iso_gen_head *)
lemma tsts_inv_pair1: ∀h,o,J,W1,U1,T2. ②{J}W1.U1 ⩳[h, o] T2 →
                      ∃∃W2,U2. T2 = ②{J}W2. U2.
/2 width=7 by tsts_inv_pair1_aux/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma tsts_inv_sort1_deg: ∀h,o,Y,s1. ⋆s1 ⩳[h, o] Y → ∀d. deg h o s1 d →
                          ∃∃s2. deg h o s2 d & Y = ⋆s2.
#h #o #Y #s1 #H #d #Hs1 elim (tsts_inv_sort1 … H) -H
#s2 #x #Hx <(deg_mono h o … Hx … Hs1) -s1 -d /2 width=3 by ex2_intro/
qed-.

lemma tsts_inv_sort_deg: ∀h,o,s1,s2. ⋆s1 ⩳[h, o] ⋆s2 →
                         ∀d1,d2. deg h o s1 d1 → deg h o s2 d2 →
                         d1 = d2.
#h #o #s1 #y #H #d1 #d2 #Hs1 #Hy
elim (tsts_inv_sort1_deg … H … Hs1) -s1 #s2 #Hs2 #H destruct
<(deg_mono h o … Hy … Hs2) -s2 -d1 //
qed-.

lemma tsts_inv_pair: ∀h,o,I1,I2,V1,V2,T1,T2. ②{I1}V1.T1 ⩳[h, o] ②{I2}V2.T2 →
                     I1 = I2.
#h #o #I1 #I2 #V1 #V2 #T1 #T2 #H elim (tsts_inv_pair1 … H) -H
#V0 #T0 #H destruct //
qed-.

(* Basic properties *********************************************************)

(* Basic_1: was: iso_refl *)
lemma tsts_refl: ∀h,o. reflexive … (tsts h o).
#h #o * //
* /2 width=1 by tsts_lref, tsts_gref/
#s elim (deg_total h o s) /2 width=3 by tsts_sort/
qed.

lemma tsts_sym: ∀h,o. symmetric … (tsts h o).
#h #o #T1 #T2 * -T1 -T2 /2 width=3 by tsts_sort/
qed-.

lemma tsts_dec: ∀h,o,T1,T2. Decidable (T1 ⩳[h, o] T2).
#h #o * [ * #s1 | #I1 #V1 #T1 ] * [1,3,5,7: * #s2 |*: #I2 #V2 #T2 ]
[ elim (deg_total h o s1) #d1 #H1
  elim (deg_total h o s2) #d2 #H2
  elim (eq_nat_dec d1 d2) #Hd12 destruct /3 width=3 by tsts_sort, or_introl/
  @or_intror #H
  lapply (tsts_inv_sort_deg … H … H1 H2) -H -H1 -H2 /2 width=1 by/
|2,3,13:
  @or_intror #H
  elim (tsts_inv_sort1 … H) -H #x1 #x2 #_ #_ #H destruct
|4,6,14:
  @or_intror #H
  lapply (tsts_inv_lref1 … H) -H #H destruct
|5:
  elim (eq_nat_dec s1 s2) #Hs12 destruct /2 width=1 by or_introl/
  @or_intror #H
  lapply (tsts_inv_lref1 … H) -H #H destruct /2 width=1 by/
|7,8,15:
  @or_intror #H
  lapply (tsts_inv_gref1 … H) -H #H destruct
|9:
  elim (eq_nat_dec s1 s2) #Hs12 destruct /2 width=1 by or_introl/
  @or_intror #H
  lapply (tsts_inv_gref1 … H) -H #H destruct /2 width=1 by/
|10,11,12:
  @or_intror #H
  elim (tsts_inv_pair1 … H) -H #X1 #X2 #H destruct
|16:
  elim (eq_item2_dec I1 I2) #HI12 destruct
  [ /3 width=1 by tsts_pair, or_introl/ ]
  @or_intror #H
  lapply (tsts_inv_pair … H) -H /2 width=1 by/
]
qed-.

(* Basic_2A1: removed theorems 4:
              tsts_inv_atom1 tsts_inv_atom2
*)
