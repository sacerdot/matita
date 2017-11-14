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

include "basic_2/computation/lpxs_lleq.ma".
include "basic_2/computation/fpbs_lift.ma".
include "basic_2/computation/fpbg_fleq.ma".

(* "QRST" PROPER PARALLEL COMPUTATION FOR CLOSURES **************************)

(* Properties on "qrst" parallel reduction on closures **********************)

lemma fpb_fpbg_trans: ∀h,o,G1,G,G2,L1,L,L2,T1,T,T2.
                      ⦃G1, L1, T1⦄ ≻[h, o] ⦃G, L, T⦄ → ⦃G, L, T⦄ >≛[h, o] ⦃G2, L2, T2⦄ →
                      ⦃G1, L1, T1⦄ >≛[h, o] ⦃G2, L2, T2⦄.
/3 width=5 by fpbg_fwd_fpbs, ex2_3_intro/ qed-.

lemma fpbq_fpbg_trans: ∀h,o,G1,G,G2,L1,L,L2,T1,T,T2.
                       ⦃G1, L1, T1⦄ ≽[h, o] ⦃G, L, T⦄ → ⦃G, L, T⦄ >≛[h, o] ⦃G2, L2, T2⦄ →
                       ⦃G1, L1, T1⦄ >≛[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H2 @(fpbq_ind_alt … H1) -H1
/2 width=5 by fleq_fpbg_trans, fpb_fpbg_trans/
qed-.

(* Properties on "qrst" parallel compuutation on closures *******************)

lemma fpbs_fpbg_trans: ∀h,o,G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G, L, T⦄ →
                       ∀G2,L2,T2. ⦃G, L, T⦄ >≛[h, o] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >≛[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G #L1 #L #T1 #T #H @(fpbs_ind … H) -G -L -T /3 width=5 by fpbq_fpbg_trans/
qed-.

(* Note: this is used in the closure proof *)
lemma fpbg_fpbs_trans: ∀h,o,G,G2,L,L2,T,T2. ⦃G, L, T⦄ ≥[h, o] ⦃G2, L2, T2⦄ →
                       ∀G1,L1,T1. ⦃G1, L1, T1⦄ >≛[h, o] ⦃G, L, T⦄ → ⦃G1, L1, T1⦄ >≛[h, o] ⦃G2, L2, T2⦄.
#h #o #G #G2 #L #L2 #T #T2 #H @(fpbs_ind_dx … H) -G -L -T /3 width=5 by fpbg_fpbq_trans/
qed-.

(* Note: this is used in the closure proof *)
lemma fqup_fpbg: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >≛[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H elim (fqup_inv_step_sn … H) -H
/3 width=5 by fqus_fpbs, fpb_fqu, ex2_3_intro/
qed.

lemma cpxs_fpbg: ∀h,o,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[h, o] T2 →
                 (T1 = T2 → ⊥) → ⦃G, L, T1⦄ >≛[h, o] ⦃G, L, T2⦄.
#h #o #G #L #T1 #T2 #H #H0 elim (cpxs_neq_inv_step_sn … H … H0) -H -H0
/4 width=5 by cpxs_fpbs, fpb_cpx, ex2_3_intro/
qed.

lemma lstas_fpbg: ∀h,o,G,L,T1,T2,d2. ⦃G, L⦄ ⊢ T1 •*[h, d2] T2 → (T1 = T2 → ⊥) →
                  ∀d1. d2 ≤ d1 → ⦃G, L⦄ ⊢ T1 ▪[h, o] d1 → ⦃G, L, T1⦄ >≛[h, o] ⦃G, L, T2⦄.
/3 width=5 by lstas_cpxs, cpxs_fpbg/ qed.

lemma lpxs_fpbg: ∀h,o,G,L1,L2,T. ⦃G, L1⦄ ⊢ ➡*[h, o] L2 →
                 (L1 ≡[T, 0] L2 → ⊥) → ⦃G, L1, T⦄ >≛[h, o] ⦃G, L2, T⦄.
#h #o #G #L1 #L2 #T #H #H0 elim (lpxs_nlleq_inv_step_sn … H … H0) -H -H0
/4 width=5 by fpb_lpx, lpxs_lleq_fpbs, ex2_3_intro/
qed.
