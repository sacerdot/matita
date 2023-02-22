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

include "basic_2/static/ffdeq.ma".
include "basic_2/rt_computation/lfpxs_lfdeq.ma".

(* UNBOUND PARALLEL RT-COMPUTATION FOR LOCAL ENV.S ON REFERRED ENTRIES ******)

(* Properties with degree-based equivalence on closures *********************)

lemma ffdeq_lfpxs_trans: ∀h,o,G1,G2,L1,L0,T1,T2. ⦃G1, L1, T1⦄ ≛[h, o] ⦃G2, L0, T2⦄ →
                         ∀L2. ⦃G2, L0⦄ ⊢⬈*[h, T2] L2 →
                         ∃∃L. ⦃G1, L1⦄ ⊢⬈*[h, T1] L & ⦃G1, L, T1⦄ ≛[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G2 #L1 #L0 #T1 #T2 #H1 #L2 #HL02
elim (ffdeq_inv_gen_dx … H1) -H1 #HG #HL10 #HT12 destruct
elim (lfdeq_lfpxs_trans … HL02 … HL10) -L0 #L0 #HL10 #HL02
lapply (tdeq_lfpxs_trans … HT12 … HL10) -HL10 #HL10
/3 width=3 by ffdeq_intro_dx, ex2_intro/
qed-.
