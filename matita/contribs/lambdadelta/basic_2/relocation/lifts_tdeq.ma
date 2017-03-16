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

include "basic_2/syntax/tdeq.ma".
include "basic_2/relocation/lifts.ma".

(* GENERIC RELOCATION FOR TERMS *********************************************)

(* Properties with degree-based equivalence for terms ***********************)

lemma tdeq_lifts: ∀h,o. liftable2 (tdeq h o).
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

(* Inversion lemmas with degree-based equivalence for terms *****************)

lemma tdeq_inv_lifts: ∀h,o. deliftable2_sn (tdeq h o).
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