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
include "basic_2/syntax/lenv.ma".

(* DEGREE-BASED EQUIVALENCE ON TERMS ****************************************)

inductive tdeq (h) (o): relation term ≝
| tdeq_sort: ∀s1,s2,d. deg h o s1 d → deg h o s2 d → tdeq h o (⋆s1) (⋆s2)
| tdeq_lref: ∀i. tdeq h o (#i) (#i)
| tdeq_gref: ∀l. tdeq h o (§l) (§l)
| tdeq_pair: ∀I,V1,V2,T1,T2. tdeq h o V1 V2 → tdeq h o T1 T2 → tdeq h o (②{I}V1.T1) (②{I}V2.T2)
.

interpretation
   "degree-based equivalence (terms)"
   'LazyEq h o T1 T2 = (tdeq h o T1 T2).

definition cdeq: ∀h. sd h → relation3 lenv term term ≝
                 λh,o,L. tdeq h o.

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

(* Basic forward lemmas *****************************************************)

lemma tdeq_fwd_atom1: ∀h,o,I,Y. ⓪{I} ≡[h, o] Y → ∃J. Y = ⓪{J}.
#h #o * #x #Y #H [ elim (tdeq_inv_sort1 … H) -H ]
/3 width=4 by tdeq_inv_gref1, tdeq_inv_lref1, ex_intro/
qed-.
