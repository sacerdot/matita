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

include "basic_2/rt_transition/lpx_reqx.ma".
include "basic_2/rt_computation/lpxs_lpx.ma".

(* UNBOUND PARALLEL RT-COMPUTATION FOR FULL LOCAL ENVIRONMENTS **************)

(* Properties with sort-irrelevant equivalence on referred entries **********)

(* Basic_2A1: uses: lleq_lpxs_trans *)
lemma reqx_lpxs_trans (h) (G) (T:term):
                      ∀L2,K2. ⦃G,L2⦄ ⊢ ⬈*[h] K2 →
                      ∀L1. L1 ≛[T] L2 →
                      ∃∃K1. ⦃G,L1⦄ ⊢ ⬈*[h] K1 & K1 ≛[T] K2.
#h #G #T #L2 #K2 #H @(lpxs_ind_sn … H) -L2 /2 width=3 by ex2_intro/
#L #L2 #HL2 #_ #IH #L1 #HT
elim (reqx_lpx_trans … HL2 … HT) -L #L #HL1 #HT
elim (IH … HT) -L2 #K #HLK #HT
/3 width=3 by lpxs_step_sn, ex2_intro/
qed-.

(* Basic_2A1: uses: lpxs_nlleq_inv_step_sn *)
lemma lpxs_rneqx_inv_step_sn (h) (G) (T:term):
                             ∀L1,L2. ⦃G,L1⦄ ⊢ ⬈*[h] L2 → (L1 ≛[T] L2 → ⊥) →
                             ∃∃L,L0. ⦃G,L1⦄ ⊢ ⬈[h] L & L1 ≛[T] L → ⊥ &
                                     ⦃G,L⦄ ⊢ ⬈*[h] L0 & L0 ≛[T] L2.
#h #G #T #L1 #L2 #H @(lpxs_ind_sn … H) -L1
[ #H elim H -H //
| #L1 #L #H1 #H2 #IH2 #H12 elim (reqx_dec L1 L T) #H
  [ -H1 -H2 elim IH2 -IH2 /3 width=3 by reqx_trans/ -H12
    #L0 #L3 #H1 #H2 #H3 #H4 lapply (reqx_rneqx_trans … H … H2) -H2
    #H2 elim (reqx_lpx_trans … H1 … H) -L
    #L #H1 #H lapply (rneqx_reqx_div … H … H2) -H2
    #H2 elim (reqx_lpxs_trans … H3 … H) -L0
    /3 width=8 by reqx_trans, ex4_2_intro/
  | -H12 -IH2 /3 width=6 by ex4_2_intro/
  ]
]
qed-.
