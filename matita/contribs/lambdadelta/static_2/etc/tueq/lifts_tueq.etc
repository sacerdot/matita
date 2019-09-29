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

include "static_2/syntax/tueq.ma".
include "static_2/relocation/lifts_lifts.ma".

(* GENERIC RELOCATION FOR TERMS *********************************************)

(* Properties with tail sort-irrelevant equivalence for terms ***************)

lemma tueq_lifts_sn: liftable2_sn tueq.
#T1 #T2 #H elim H -T1 -T2
[ #s1 #s2 #f #X #H >(lifts_inv_sort1 … H) -H
  /3 width=3 by lifts_sort, tueq_sort, ex2_intro/
| #i #f #X #H elim (lifts_inv_lref1 … H) -H
  /3 width=3 by lifts_lref, tueq_lref, ex2_intro/
| #l #f #X #H >(lifts_inv_gref1 … H) -H
  /2 width=3 by lifts_gref, tueq_gref, ex2_intro/
| #p #I #V #T1 #T2 #_ #IHT #f #X #H elim (lifts_inv_bind1 … H) -H
  #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (IHT … HTU1) -T1
  /3 width=3 by lifts_bind, tueq_bind, ex2_intro/
| #V #T1 #T2 #_ #IHT #f #X #H elim (lifts_inv_flat1 … H) -H
  #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (IHT … HTU1) -T1
  /3 width=3 by lifts_flat, tueq_appl, ex2_intro/
| #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #f #X #H elim (lifts_inv_flat1 … H) -H
  #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (IHV … HVW1) -V1 elim (IHT … HTU1) -T1
  /3 width=5 by lifts_flat, tueq_cast, ex2_intro/  
]
qed-.

lemma tueq_lifts_dx: liftable2_dx tueq.
/3 width=3 by tueq_lifts_sn, liftable2_sn_dx, tueq_sym/ qed-.

lemma tueq_lifts_bi: liftable2_bi tueq.
/3 width=6 by tueq_lifts_sn, liftable2_sn_bi/ qed-.

(* Inversion lemmas with tail sort-irrelevant equivalence for terms *********)

lemma tueq_inv_lifts_sn: deliftable2_sn tueq.
#U1 #U2 #H elim H -U1 -U2
[ #s1 #s2 #f #X #H >(lifts_inv_sort2 … H) -H
  /3 width=3 by lifts_sort, tueq_sort, ex2_intro/
| #i #f #X #H elim (lifts_inv_lref2 … H) -H
  /3 width=3 by lifts_lref, tueq_lref, ex2_intro/
| #l #f #X #H >(lifts_inv_gref2 … H) -H
  /2 width=3 by lifts_gref, tueq_gref, ex2_intro/
| #p #I #W #U1 #U2 #_ #IHU #f #X #H elim (lifts_inv_bind2 … H) -H
  #V1 #T1 #HVW1 #HTU1 #H destruct
  elim (IHU … HTU1) -U1
  /3 width=3 by lifts_bind, tueq_bind, ex2_intro/
| #W #U1 #U2 #_ #IHU #f #X #H elim (lifts_inv_flat2 … H) -H
  #V1 #T1 #HVW1 #HTU1 #H destruct
  elim (IHU … HTU1) -U1
  /3 width=3 by lifts_flat, tueq_appl, ex2_intro/
| #W1 #W2 #U1 #U2 #_ #_ #IHW #IHU #f #X #H elim (lifts_inv_flat2 … H) -H
  #V1 #T1 #HVW1 #HTU1 #H destruct
  elim (IHW … HVW1) -W1 elim (IHU … HTU1) -U1
  /3 width=5 by lifts_flat, tueq_cast, ex2_intro/
]
qed-.

lemma tueq_inv_lifts_dx: deliftable2_dx tueq.
/3 width=3 by tueq_inv_lifts_sn, deliftable2_sn_dx, tueq_sym/ qed-.

lemma tueq_inv_lifts_bi: deliftable2_bi tueq.
/3 width=6 by tueq_inv_lifts_sn, deliftable2_sn_bi/ qed-.
