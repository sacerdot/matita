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

include "basic_2/rt_transition/lfpx_lfdeq.ma".
include "basic_2/rt_computation/lfpxs_fqup.ma".

(* UNCOUNTED PARALLEL RT-COMPUTATION FOR LOCAL ENV.S ON REFERRED ENTRIES ****)

(* Properties with degree-based equivalence on referred entries *************)

(* Basic_2A1: was: lleq_lpxs_trans *)
lemma lfdeq_lfpxs_trans: ∀h,o,G,L2,K2,T. ⦃G, L2⦄ ⊢ ⬈*[h, T] K2 →
                         ∀L1. L1 ≛[h, o, T] L2 →
                         ∃∃K1. ⦃G, L1⦄ ⊢ ⬈*[h, T] K1 & K1 ≛[h, o, T] K2.
#h #o #G #L2 #K2 #T #H @(lfpxs_ind_sn … H) -K2 /2 width=3 by ex2_intro/
#K #K2 #_ #HK2 #IH #L1 #HT elim (IH … HT) -L2
#L #HL1 #HT elim (lfdeq_lfpx_trans … HK2 … HT) -K
/3 width=3 by lfpxs_step_dx, ex2_intro/
qed-.

(* Basic_2A1: was: lpxs_nlleq_inv_step_sn *)
lemma lfpxs_lfdneq_inv_step_sn: ∀h,o,G,L1,L2,T. ⦃G, L1⦄ ⊢ ⬈*[h, T] L2 → (L1 ≛[h, o, T] L2 → ⊥) →
                                ∃∃L,L0. ⦃G, L1⦄ ⊢ ⬈[h, T] L & L1 ≛[h, o, T] L → ⊥ & ⦃G, L⦄ ⊢ ⬈*[h, T] L0 & L0 ≛[h, o, T] L2.
#h #o #G #L1 #L2 #T #H @(lfpxs_ind_dx … H) -L1
[ #H elim H -H //
| #L1 #L #H1 #H2 #IH2 #H12 elim (lfdeq_dec h o L1 L T) #H
  [ -H1 -H2 elim IH2 -IH2 /3 width=3 by lfdeq_trans/ -H12
    #L0 #L3 #H1 #H2 #H3 #H4 lapply (lfdeq_lfdneq_trans … H … H2) -H2
    #H2 elim (lfdeq_lfpx_trans … H1 … H) -L
    #L #H1 #H lapply (lfdneq_lfdeq_div … H … H2) -H2
    #H2 elim (lfdeq_lfpxs_trans … H3 … H) -L0
    /3 width=8 by lfdeq_trans, ex4_2_intro/
  | -H12 -IH2 /3 width=6 by ex4_2_intro/
  ]
]
qed-.
