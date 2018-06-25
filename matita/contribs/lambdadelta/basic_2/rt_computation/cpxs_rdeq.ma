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

include "basic_2/rt_transition/cpx_rdeq.ma".
include "basic_2/rt_computation/cpxs_tdeq.ma".

(* UNBOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Properties with degree-based equivalence for local environments **********)

(* Basic_2A1: was just: lleq_cpxs_trans *) 
lemma rdeq_cpxs_trans: ∀h,o,G,L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ⬈*[h] T1 →
                       ∀L2. L2 ≛[h, o, T0] L0 →
                       ∃∃T. ⦃G, L2⦄ ⊢ T0 ⬈*[h] T & T ≛[h, o] T1.
#h #o #G #L0 #T0 #T1 #H @(cpxs_ind_dx … H) -T0 /2 width=3 by ex2_intro/
#T0 #T #HT0 #_ #IH #L2 #HL2
elim (rdeq_cpx_trans … HL2 … HT0) #U1 #H1 #H2
elim (IH L2) -IH /2 width=4 by cpx_rdeq_conf_dx/ -L0 #U2 #H3 #H4
elim (tdeq_cpxs_trans … H2 … H3) -T #U0 #H2 #H3
/3 width=5 by cpxs_strap2, tdeq_trans, ex2_intro/
qed-.

(* Basic_2A1: was just: cpxs_lleq_conf *) 
lemma cpxs_rdeq_conf: ∀h,o,G,L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ⬈*[h] T1 →
                      ∀L2. L0 ≛[h, o, T0] L2 →
                      ∃∃T. ⦃G, L2⦄ ⊢ T0 ⬈*[h] T & T ≛[h, o] T1.
/3 width=3 by rdeq_cpxs_trans, rdeq_sym/ qed-.

(* Basic_2A1: was just: cpxs_lleq_conf_dx *) 
lemma cpxs_rdeq_conf_dx: ∀h,o,G,L2,T1,T2. ⦃G, L2⦄ ⊢ T1 ⬈*[h] T2 →
                         ∀L1. L1 ≛[h, o, T1] L2 → L1 ≛[h, o, T2] L2.
#h #o #G #L2 #T1 #T2 #H @(cpxs_ind … H) -T2 /3 width=6 by cpx_rdeq_conf_dx/
qed-.

(* Basic_2A1: was just: lleq_conf_sn *) 
lemma cpxs_rdeq_conf_sn: ∀h,o,G,L1,T1,T2. ⦃G, L1⦄ ⊢ T1 ⬈*[h] T2 →
                         ∀L2. L1 ≛[h, o, T1] L2 → L1 ≛[h, o, T2] L2.
/4 width=6 by cpxs_rdeq_conf_dx, rdeq_sym/ qed-.
