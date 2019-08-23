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

include "static_2/syntax/theq.ma".
include "static_2/relocation/lifts_lifts.ma".

(* GENERIC RELOCATION FOR TERMS *********************************************)

(* Properties with tail sort-irrelevant head equivalence for terms **********)

lemma theq_lifts_bi: liftable2_bi theq.
#T1 #T2 #H elim H -T1 -T2 [||| * ]
[ #s1 #s2 #f #X1 #H1 #X2 #H2
  >(lifts_inv_sort1 … H1) -H1 >(lifts_inv_sort1 … H2) -H2
  /1 width=1 by theq_sort/
| #i #f #X1 #H1 #X2 #H2
  elim (lifts_inv_lref1 … H1) -H1 #j1 #Hj1 #H destruct
  elim (lifts_inv_lref1 … H2) -H2 #j2 #Hj2 #H destruct
  <(at_mono … Hj2 … Hj1) -i -f -j2
  /1 width=1 by theq_lref/
| #l #f #X1 #H1 #X2 #H2
  >(lifts_inv_gref1 … H1) -H1 >(lifts_inv_gref1 … H2) -H2
  /1 width=1 by theq_gref/
| #p #I #V1 #V2 #T1 #T2 #f #X1 #H1 #X2 #H2
  elim (lifts_inv_bind1 … H1) -H1 #W1 #U1 #_ #_ #H destruct
  elim (lifts_inv_bind1 … H2) -H2 #W2 #U2 #_ #_ #H destruct
  /1 width=1 by theq_pair/
| #I #V1 #V2 #T1 #T2 #f #X1 #H1 #X2 #H2
  elim (lifts_inv_flat1 … H1) -H1 #W1 #U1 #_ #_ #H destruct
  elim (lifts_inv_flat1 … H2) -H2 #W2 #U2 #_ #_ #H destruct
  /1 width=1 by theq_pair/
]
qed-.

(* Inversion lemmas with tail sort-irrelevant head equivalence for terms ****)

lemma theq_inv_lifts_bi: deliftable2_bi theq.
#U1 #U2 #H elim H -U1 -U2 [||| * ]
[ #s1 #s2 #f #X1 #H1 #X2 #H2
  >(lifts_inv_sort2 … H1) -H1 >(lifts_inv_sort2 … H2) -H2
  /1 width=1 by theq_sort/
| #j #f #X1 #H1 #X2 #H2
  elim (lifts_inv_lref2 … H1) -H1 #i1 #Hj1 #H destruct
  elim (lifts_inv_lref2 … H2) -H2 #i2 #Hj2 #H destruct
  <(at_inj … Hj2 … Hj1) -j -f -i1
  /1 width=1 by theq_lref/
| #l #f #X1 #H1 #X2 #H2
  >(lifts_inv_gref2 … H1) -H1 >(lifts_inv_gref2 … H2) -H2
  /1 width=1 by theq_gref/
| #p #I #W1 #W2 #U1 #U2 #f #X1 #H1 #X2 #H2
  elim (lifts_inv_bind2 … H1) -H1 #V1 #T1 #_ #_ #H destruct
  elim (lifts_inv_bind2 … H2) -H2 #V2 #T2 #_ #_ #H destruct
  /1 width=1 by theq_pair/
| #I #W1 #W2 #U1 #U2 #f #X1 #H1 #X2 #H2
  elim (lifts_inv_flat2 … H1) -H1 #V1 #T1 #_ #_ #H destruct
  elim (lifts_inv_flat2 … H2) -H2 #V2 #T2 #_ #_ #H destruct
  /1 width=1 by theq_pair/
]
qed-.
