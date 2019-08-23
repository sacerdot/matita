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

include "static_2/notation/relations/approxeq_2.ma".
include "static_2/syntax/term.ma".

(* TAIL SORT-IRRELEVANT EQUIVALENCE ON TERMS ********************************)

inductive tueq: relation term ≝
| tueq_sort: ∀s1,s2. tueq (⋆s1) (⋆s2)
| tueq_lref: ∀i. tueq (#i) (#i)
| tueq_gref: ∀l. tueq (§l) (§l)
| tueq_bind: ∀p,I,V,T1,T2. tueq T1 T2 → tueq (ⓑ{p,I}V.T1) (ⓑ{p,I}V.T2)
| tueq_appl: ∀V,T1,T2. tueq T1 T2 → tueq (ⓐV.T1) (ⓐV.T2)
| tueq_cast: ∀V1,V2,T1,T2. tueq V1 V2 → tueq T1 T2 → tueq (ⓝV1.T1) (ⓝV2.T2)
.

interpretation
   "context-free tail sort-irrelevant equivalence (term)"
   'ApproxEq T1 T2 = (tueq T1 T2).

(* Basic properties *********************************************************)

lemma tueq_refl: reflexive … tueq.
#T elim T -T * [|||| * ] 
/2 width=1 by tueq_sort, tueq_lref, tueq_gref, tueq_bind, tueq_appl, tueq_cast/
qed.

lemma tueq_sym: symmetric … tueq.
#T1 #T2 #H elim H -T1 -T2
/2 width=3 by tueq_sort, tueq_bind, tueq_appl, tueq_cast/
qed-.

(* Left basic inversion lemmas **********************************************)

fact tueq_inv_sort1_aux: ∀X,Y. X ≅ Y → ∀s1. X = ⋆s1 →
                         ∃s2. Y = ⋆s2.
#X #Y * -X -Y
[ #s1 #s2 #s #H destruct /2 width=2 by ex_intro/
| #i #s #H destruct
| #l #s #H destruct
| #p #I #V #T1 #T2 #_ #s #H destruct
| #V #T1 #T2 #_ #s #H destruct
| #V1 #V2 #T1 #T2 #_ #_ #s #H destruct
]
qed-.

lemma tueq_inv_sort1: ∀Y,s1. ⋆s1 ≅ Y →
                      ∃s2. Y = ⋆s2.
/2 width=4 by tueq_inv_sort1_aux/ qed-.

fact tueq_inv_lref1_aux: ∀X,Y. X ≅ Y → ∀i. X = #i → Y = #i.
#X #Y * -X -Y //
[ #s1 #s2 #j #H destruct
| #p #I #V #T1 #T2 #_ #j #H destruct
| #V #T1 #T2 #_ #j #H destruct
| #V1 #V2 #T1 #T2 #_ #_ #j #H destruct
]
qed-.

lemma tueq_inv_lref1: ∀Y,i. #i ≅ Y → Y = #i.
/2 width=5 by tueq_inv_lref1_aux/ qed-.

fact tueq_inv_gref1_aux: ∀X,Y. X ≅ Y → ∀l. X = §l → Y = §l.
#X #Y * -X -Y //
[ #s1 #s2 #k #H destruct
| #p #I #V #T1 #T2 #_ #k #H destruct
| #V #T1 #T2 #_ #k #H destruct
| #V1 #V2 #T1 #T2 #_ #_ #k #H destruct
]
qed-.

lemma tueq_inv_gref1: ∀Y,l. §l ≅ Y → Y = §l.
/2 width=5 by tueq_inv_gref1_aux/ qed-.

fact tueq_inv_bind1_aux: ∀X,Y. X ≅ Y → ∀p,I,V,T1. X = ⓑ{p,I}V.T1 →
                         ∃∃T2. T1 ≅ T2 & Y = ⓑ{p,I}V.T2.
#X #Y * -X -Y
[ #s1 #s2 #q #J #W #U1 #H destruct
| #i #q #J #W #U1 #H destruct
| #l #q #J #W #U1 #H destruct
| #p #I #V #T1 #T2 #HT #q #J #W #U1 #H destruct /2 width=3 by ex2_intro/
| #V #T1 #T2 #_ #q #J #W #U1 #H destruct
| #V1 #V2 #T1 #T2 #_ #_ #q #J #W #U1 #H destruct
]
qed-.

lemma tueq_inv_bind1: ∀p,I,V,T1,Y. ⓑ{p,I}V.T1 ≅ Y →
                      ∃∃T2. T1 ≅ T2 & Y = ⓑ{p,I}V.T2.
/2 width=3 by tueq_inv_bind1_aux/ qed-.

fact tueq_inv_appl1_aux: ∀X,Y. X ≅ Y → ∀V,T1. X = ⓐV.T1 →
                         ∃∃T2. T1 ≅ T2 & Y = ⓐV.T2.
#X #Y * -X -Y
[ #s1 #s2 #W #U1 #H destruct
| #i #W #U1 #H destruct
| #l #W #U1 #H destruct
| #p #I #V #T1 #T2 #_ #W #U1 #H destruct
| #V #T1 #T2 #HT #W #U1 #H destruct /2 width=3 by ex2_intro/
| #V1 #V2 #T1 #T2 #_ #_ #W #U1 #H destruct
]
qed-.

lemma tueq_inv_appl1: ∀V,T1,Y. ⓐV.T1 ≅ Y →
                      ∃∃T2. T1 ≅ T2 & Y = ⓐV.T2.
/2 width=3 by tueq_inv_appl1_aux/ qed-.

fact tueq_inv_cast1_aux: ∀X,Y. X ≅ Y → ∀V1,T1. X = ⓝV1.T1 →
                         ∃∃V2,T2. V1 ≅ V2 & T1 ≅ T2 & Y = ⓝV2.T2.
#X #Y * -X -Y
[ #s1 #s2 #W1 #U1 #H destruct
| #i #W1 #U1 #H destruct
| #l #W1 #U1 #H destruct
| #p #I #V #T1 #T2 #_ #W1 #U1 #H destruct
| #V #T1 #T2 #_ #W1 #U1 #H destruct
| #V1 #V2 #T1 #T2 #HV #HT #W1 #U1 #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

lemma tueq_inv_cast1: ∀V1,T1,Y. ⓝV1.T1 ≅ Y →
                      ∃∃V2,T2. V1 ≅ V2 & T1 ≅ T2 & Y = ⓝV2.T2.
/2 width=3 by tueq_inv_cast1_aux/ qed-.

(* Right basic inversion lemmas *********************************************)

lemma tueq_inv_bind2: ∀p,I,V,T2,X1. X1 ≅ ⓑ{p,I}V.T2 →
                      ∃∃T1. T1 ≅ T2 & X1 = ⓑ{p,I}V.T1.
#p #I #V #T2 #X1 #H
elim (tueq_inv_bind1 p I V T2 X1)
[ #T1 #HT #H destruct ]
/3 width=3 by tueq_sym, ex2_intro/
qed-.
