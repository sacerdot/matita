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

include "basic_2/static/ffdeq_lfeq.ma".
include "basic_2/rt_computation/lfpxs_lpxs.ma".
include "basic_2/rt_computation/fpbs_lfpxs.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Properties with unbound parallel rt-computation on local environments ****)

(* Basic_2A1: uses: fpbs_intro_alt *) 
lemma fpbs_intro_star: ∀h,o,G1,L1,T1,T. ⦃G1, L1⦄ ⊢ T1 ⬈*[h] T →
                       ∀G,L,T0. ⦃G1, L1, T⦄ ⊐* ⦃G, L, T0⦄ →
                       ∀L0. ⦃G, L⦄ ⊢ ⬈*[h] L0 →
                       ∀G2,L2,T2. ⦃G, L0, T0⦄ ≛[h, o] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄ .
/3 width=9 by fpbs_intro_fstar, lfpxs_lpxs/ qed.

(* Eliminators with unbound parallel rt-computation on local environments ***)

(* Basic_2A1: uses: fpbs_inv_alt *)
lemma fpbs_inv_star: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄ →
                     ∃∃G,L,L0,T,T0. ⦃G1, L1⦄ ⊢ T1 ⬈*[h] T & ⦃G1, L1, T⦄ ⊐* ⦃G, L, T0⦄
                                  & ⦃G, L⦄ ⊢ ⬈*[h] L0 & ⦃G, L0, T0⦄ ≛[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H
elim (fpbs_inv_fstar … H) -H #G #L #L0 #T #T0 #HT1 #H10 #HL0 #H02
elim (lfpxs_inv_lpxs_lfeq … HL0) -HL0 #L3 #HL3 #HL30
/3 width=11 by lfeq_lfdeq_trans, ex4_5_intro/
qed-.
