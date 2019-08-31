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

include "static_2/syntax/toeq.ma".
include "static_2/relocation/lifts_lifts.ma".

(* GENERIC RELOCATION FOR TERMS *********************************************)

(* Properties with sort-irrelevant outer equivalence for terms **************)

lemma toeq_lifts_sn: liftable2_sn toeq.
#T1 #T2 #H elim H -T1 -T2 [||| * ]
[ #s1 #s2 #f #X #H 
  >(lifts_inv_sort1 … H) -H
  /2 width=3 by toeq_sort, ex2_intro/
| #i #f #X #H
  elim (lifts_inv_lref1 … H) -H #j #Hj #H destruct
  /3 width=3 by toeq_lref, lifts_lref, ex2_intro/
| #l #f #X #H
  >(lifts_inv_gref1 … H) -H
  /2 width=3 by toeq_gref, ex2_intro/
| #p #I #V1 #V2 #T1 #T2 #f #X #H
  elim (lifts_inv_bind1 … H) -H #W1 #U1 #_ #_ #H destruct -V1 -T1
  elim (lifts_total V2 f) #W2 #HVW2
  elim (lifts_total T2 (⫯f)) #U2 #HTU2
  /3 width=3 by toeq_pair, lifts_bind, ex2_intro/
| #I #V1 #V2 #T1 #T2 #f #X #H
  elim (lifts_inv_flat1 … H) -H #W1 #U1 #_ #_ #H destruct -V1 -T1
  elim (lifts_total V2 f) #W2 #HVW2
  elim (lifts_total T2 f) #U2 #HTU2
  /3 width=3 by toeq_pair, lifts_flat, ex2_intro/
]
qed-.

lemma toeq_lifts_dx: liftable2_dx toeq.
/3 width=3 by toeq_lifts_sn, liftable2_sn_dx, toeq_sym/ qed-.

lemma toeq_lifts_bi: liftable2_bi toeq.
/3 width=6 by toeq_lifts_sn, liftable2_sn_bi/ qed-.

(* Inversion lemmas with sort-irrelevant outer equivalence for terms ********)

lemma toeq_inv_lifts_bi: deliftable2_bi toeq.
#U1 #U2 #H elim H -U1 -U2 [||| * ]
[ #s1 #s2 #f #X1 #H1 #X2 #H2
  >(lifts_inv_sort2 … H1) -H1 >(lifts_inv_sort2 … H2) -H2
  /1 width=1 by toeq_sort/
| #j #f #X1 #H1 #X2 #H2
  elim (lifts_inv_lref2 … H1) -H1 #i1 #Hj1 #H destruct
  elim (lifts_inv_lref2 … H2) -H2 #i2 #Hj2 #H destruct
  <(at_inj … Hj2 … Hj1) -j -f -i1
  /1 width=1 by toeq_lref/
| #l #f #X1 #H1 #X2 #H2
  >(lifts_inv_gref2 … H1) -H1 >(lifts_inv_gref2 … H2) -H2
  /1 width=1 by toeq_gref/
| #p #I #W1 #W2 #U1 #U2 #f #X1 #H1 #X2 #H2
  elim (lifts_inv_bind2 … H1) -H1 #V1 #T1 #_ #_ #H destruct -W1 -U1
  elim (lifts_inv_bind2 … H2) -H2 #V2 #T2 #_ #_ #H destruct -W2 -U2
  /1 width=1 by toeq_pair/
| #I #W1 #W2 #U1 #U2 #f #X1 #H1 #X2 #H2
  elim (lifts_inv_flat2 … H1) -H1 #V1 #T1 #_ #_ #H destruct -W1 -U1
  elim (lifts_inv_flat2 … H2) -H2 #V2 #T2 #_ #_ #H destruct -W2 -U2
  /1 width=1 by toeq_pair/
]
qed-.
