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

include "basic_2/static/rdeq.ma".
include "basic_2/static/aaa.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Properties with degree-based equivalence on referred entries *************)

lemma aaa_tdeq_conf_rdeq: ∀h,o,G,L1,T1,A. ⦃G, L1⦄ ⊢ T1 ⁝ A → ∀T2. T1 ≛[h, o] T2 →
                          ∀L2. L1 ≛[h, o, T1] L2 → ⦃G, L2⦄ ⊢ T2 ⁝ A.
#h #o #G #L1 #T1 #A #H elim H -G -L1 -T1 -A
[ #G #L1 #s1 #X #H1 elim (tdeq_inv_sort1 … H1) -H1 //
| #I #G #L1 #V1 #B #_ #IH #X #H1 >(tdeq_inv_lref1 … H1) -H1
  #Y #H2 elim (rdeq_inv_zero_pair_sn … H2) -H2
  #L2 #V2 #HL12 #HV12 #H destruct /3 width=1 by aaa_zero/
| #I #G #L1 #A #i #_ #IH #X #H1 >(tdeq_inv_lref1 … H1) -H1
  #Y #H2 elim (rdeq_inv_lref_bind_sn … H2) -H2
  #J #L2 #HL12 #H destruct /3 width=1 by aaa_lref/
| #p #G #L1 #V1 #T1 #B #A #_ #_ #IHV #IHT #X #H1 elim (tdeq_inv_pair1 … H1) -H1
  #V2 #T2 #HV12 #HT12 #H #L2 #H2 elim (rdeq_inv_bind … H2) -H2 destruct
  /5 width=2 by aaa_abbr, rdeq_bind_repl_dx, ext2_pair/
| #p #G #L1 #V1 #T1 #B #A #_ #_ #IHV #IHT #X #H1 elim (tdeq_inv_pair1 … H1) -H1
  #V2 #T2 #HV12 #HT12 #H #L2 #H2 elim (rdeq_inv_bind … H2) -H2 destruct
  /5 width=2 by aaa_abst, rdeq_bind_repl_dx, ext2_pair/
| #G #L1 #V1 #T1 #B #A #_ #_ #IHV #IHT #X #H1 elim (tdeq_inv_pair1 … H1) -H1
  #V2 #T2 #HV12 #HT12 #H #L2 #H2 elim (rdeq_inv_flat … H2) -H2 destruct
  /3 width=3 by aaa_appl/
| #G #L1 #V1 #T1 #A #_ #_ #IHV #IHT #X #H1 elim (tdeq_inv_pair1 … H1) -H1
  #V2 #T2 #HV12 #HT12 #H #L2 #H2 elim (rdeq_inv_flat … H2) -H2 destruct
  /3 width=1 by aaa_cast/
]
qed-.
