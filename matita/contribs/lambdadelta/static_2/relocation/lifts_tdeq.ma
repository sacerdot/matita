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

include "static_2/syntax/tdeq.ma".
include "static_2/relocation/lifts_lifts.ma".

(* GENERIC RELOCATION FOR TERMS *********************************************)

(* Properties with degree-based equivalence for terms ***********************)

lemma tdeq_lifts_sn: ∀h,o. liftable2_sn (tdeq h o).
#h #o #T1 #T2 #H elim H -T1 -T2 [||| * ]
[ #s1 #s2 #d #Hs1 #Hs2 #f #X #H >(lifts_inv_sort1 … H) -H
  /3 width=5 by lifts_sort, tdeq_sort, ex2_intro/
| #i #f #X #H elim (lifts_inv_lref1 … H) -H
  /3 width=3 by lifts_lref, tdeq_lref, ex2_intro/
| #l #f #X #H >(lifts_inv_gref1 … H) -H
  /2 width=3 by lifts_gref, tdeq_gref, ex2_intro/
| #p #I #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #f #X #H elim (lifts_inv_bind1 … H) -H
  #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (IHV … HVW1) -V1 elim (IHT … HTU1) -T1
  /3 width=5 by lifts_bind, tdeq_pair, ex2_intro/
| #I #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #f #X #H elim (lifts_inv_flat1 … H) -H
  #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (IHV … HVW1) -V1 elim (IHT … HTU1) -T1
  /3 width=5 by lifts_flat, tdeq_pair, ex2_intro/
]
qed-.

lemma tdeq_lifts_bi: ∀h,o. liftable2_bi (tdeq h o).
/3 width=6 by tdeq_lifts_sn, liftable2_sn_bi/ qed-.

(* Inversion lemmas with degree-based equivalence for terms *****************)

lemma tdeq_inv_lifts_sn: ∀h,o. deliftable2_sn (tdeq h o).
#h #o #U1 #U2 #H elim H -U1 -U2 [||| * ]
[ #s1 #s2 #d #Hs1 #Hs2 #f #X #H >(lifts_inv_sort2 … H) -H
  /3 width=5 by lifts_sort, tdeq_sort, ex2_intro/
| #i #f #X #H elim (lifts_inv_lref2 … H) -H
  /3 width=3 by lifts_lref, tdeq_lref, ex2_intro/
| #l #f #X #H >(lifts_inv_gref2 … H) -H
  /2 width=3 by lifts_gref, tdeq_gref, ex2_intro/
| #p #I #W1 #W2 #U1 #U2 #_ #_ #IHW #IHU #f #X #H elim (lifts_inv_bind2 … H) -H
  #V1 #T1 #HVW1 #HTU1 #H destruct
  elim (IHW … HVW1) -W1 elim (IHU … HTU1) -U1
  /3 width=5 by lifts_bind, tdeq_pair, ex2_intro/
| #I #W1 #W2 #U1 #U2 #_ #_ #IHW #IHU #f #X #H elim (lifts_inv_flat2 … H) -H
  #V1 #T1 #HVW1 #HTU1 #H destruct
  elim (IHW … HVW1) -W1 elim (IHU … HTU1) -U1
  /3 width=5 by lifts_flat, tdeq_pair, ex2_intro/
]
qed-.

lemma tdeq_inv_lifts_bi: ∀h,o. deliftable2_bi (tdeq h o).
/3 width=6 by tdeq_inv_lifts_sn, deliftable2_sn_bi/ qed-.

lemma tdeq_lifts_inv_pair_sn (h) (o) (I) (f:rtmap):
                             ∀X,T. ⬆*[f]X ≘ T → ∀V. ②{I}V.T ≛[h,o] X → ⊥.
#h #o #I #f #X #T #H elim H -f -X -T
[ #f #s #V #H
  elim (tdeq_inv_pair1 … H) -H #X1 #X2 #_ #_ #H destruct
| #f #i #j #_ #V #H
  elim (tdeq_inv_pair1 … H) -H #X1 #X2 #_ #_ #H destruct
| #f #l #V #H
  elim (tdeq_inv_pair1 … H) -H #X1 #X2 #_ #_ #H destruct
| #f #p #J #X1 #T1 #X2 #T2 #_ #_ #_ #IH2 #V #H
  elim (tdeq_inv_pair1 … H) -H #Z1 #Z2 #_ #HZ2 #H destruct
  /2 width=2 by/
| #f #J #X1 #T1 #X2 #T2 #_ #_ #_ #IH2 #V #H
  elim (tdeq_inv_pair1 … H) -H #Z1 #Z2 #_ #HZ2 #H destruct
  /2 width=2 by/
]
qed-.
