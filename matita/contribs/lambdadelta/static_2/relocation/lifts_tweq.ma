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

include "static_2/syntax/tweq.ma".
include "static_2/relocation/lifts_lifts.ma".

(* GENERIC RELOCATION FOR TERMS *********************************************)

(* Properties with sort-irrelevant whd equivalence for terms ****************)

lemma tweq_lifts_sn: liftable2_sn tweq.
#T1 #T2 #H elim H -T1 -T2
[ #s1 #s2 #f #X #H >(lifts_inv_sort1 … H) -H
  /3 width=3 by lifts_sort, tweq_sort, ex2_intro/
| #i #f #X #H elim (lifts_inv_lref1 … H) -H
  /3 width=3 by lifts_lref, tweq_lref, ex2_intro/
| #l #f #X #H >(lifts_inv_gref1 … H) -H
  /2 width=3 by lifts_gref, tweq_gref, ex2_intro/
| #p #V1 #V2 #T1 #T2 #_ #IHT #f #X #H
  elim (lifts_inv_bind1 … H) -H #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (lifts_total V2 f) #W2 #HVW2
  elim (true_or_false p) #H destruct
  [ elim (IHT … HTU1) -T1 [| // ] #U2 #HTU2 #HU12
  | elim (lifts_total T2 (⫯f)) #U2 #HTU2
  ]
  /3 width=4 by tweq_abbr_pos, lifts_bind, ex2_intro/
| #p #V1 #V2 #T1 #T2 #f #X #H
  elim (lifts_inv_bind1 … H) -H #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (lifts_total V2 f) #W2 #HVW2
  elim (lifts_total T2 (⫯f)) #U2 #HTU2
  /3 width=3 by lifts_bind, ex2_intro/
| #V1 #V2 #T1 #T2 #_ #IHT #f #X #H
  elim (lifts_inv_flat1 … H) -H #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (lifts_total V2 f) #W2 #HVW2
  elim (IHT … HTU1) -T1 #U2 #HTU2 #HU12
  /3 width=4 by lifts_flat, tweq_appl, ex2_intro/
| #V1 #V2 #T1 #T2 #_ #_ #IHV #IHT #f #X #H
  elim (lifts_inv_flat1 … H) -H #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (IHV … HVW1) -V1 #W2 #HVW2 #HW12
  elim (IHT … HTU1) -T1 #U2 #HTU2 #HU12
  /3 width=5 by lifts_flat, tweq_cast, ex2_intro/
]
qed-.

lemma tweq_lifts_dx: liftable2_dx tweq.
/3 width=3 by tweq_lifts_sn, liftable2_sn_dx, tweq_sym/ qed-.

lemma tweq_lifts_bi: liftable2_bi tweq.
/3 width=6 by tweq_lifts_sn, liftable2_sn_bi/ qed-.

(* Inversion lemmas with sort-irrelevant whd equivalence for terms **********)

lemma tweq_inv_lifts_bi: deliftable2_bi tweq.
#U1 #U2 #H elim H -U1 -U2
[ #s1 #s2 #f #X1 #H1 #X2 #H2
  >(lifts_inv_sort2 … H1) -H1 >(lifts_inv_sort2 … H2) -H2
  /1 width=1 by tweq_sort/
| #j #f #X1 #H1 #X2 #H2
  elim (lifts_inv_lref2 … H1) -H1 #i1 #Hj1 #H destruct
  elim (lifts_inv_lref2 … H2) -H2 #i2 #Hj2 #H destruct
  <(at_inj … Hj2 … Hj1) -j -f -i1
  /1 width=1 by tweq_lref/
| #l #f #X1 #H1 #X2 #H2
  >(lifts_inv_gref2 … H1) -H1 >(lifts_inv_gref2 … H2) -H2
  /1 width=1 by tweq_gref/
| #p #W1 #W2 #U1 #U2 #_ #IH #f #X1 #H1 #X2 #H2
  elim (lifts_inv_bind2 … H1) -H1 #V1 #T1 #_ #HTU1 #H destruct -W1
  elim (lifts_inv_bind2 … H2) -H2 #V2 #T2 #_ #HTU2 #H destruct -W2
  elim (true_or_false p) #H destruct
  [ /3 width=3 by tweq_abbr_pos/
  | /1 width=1 by tweq_abbr_neg/
  ]
| #p #W1 #W2 #U1 #U2 #f #X1 #H1 #X2 #H2
  elim (lifts_inv_bind2 … H1) -H1 #V1 #T1 #_ #_ #H destruct -W1 -U1
  elim (lifts_inv_bind2 … H2) -H2 #V2 #T2 #_ #_ #H destruct -W2 -U2
  /1 width=1 by tweq_abst/
| #W1 #W2 #U1 #U2 #_ #IH #f #X1 #H1 #X2 #H2
  elim (lifts_inv_flat2 … H1) -H1 #V1 #T1 #_ #HTU1 #H destruct -W1
  elim (lifts_inv_flat2 … H2) -H2 #V2 #T2 #_ #HTU2 #H destruct -W2
  /3 width=3 by tweq_appl/
| #W1 #W2 #U1 #U2 #_ #_ #IHW #IHU #f #X1 #H1 #X2 #H2
  elim (lifts_inv_flat2 … H1) -H1 #V1 #T1 #HVW1 #HTU1 #H destruct
  elim (lifts_inv_flat2 … H2) -H2 #V2 #T2 #HVW2 #HTU2 #H destruct
  /3 width=3 by tweq_cast/
]
qed-.

lemma tweq_inv_abbr_pos_x_lifts_y_y (T) (f:rtmap):
      ∀V,U. +ⓓV.U ≅ T → ⇧*[f]T ≘ U → ⊥.
@(f_ind … tw) #n #IH #T #Hn #f #V #U #H1 #H2 destruct
elim (tweq_inv_abbr_pos_sn … H1) -H1 #X1 #X2 #HX2 #H destruct -V
elim (lifts_inv_bind1 … H2) -H2 #Y1 #Y2 #_ #HXY2 #H destruct
/2 width=7 by/
qed-.
