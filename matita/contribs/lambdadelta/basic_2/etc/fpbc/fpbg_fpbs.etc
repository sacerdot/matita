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

lemma fpbg_fpb_trans: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2.
                      ⦃G1, L1, T1⦄ >≡[h, g] ⦃G, L, T⦄ → ⦃G, L, T⦄ ≽[h, g] ⦃G2, L2, T2⦄ →
                      ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H2 elim (fpb_fpbu … H2) -H2
/3 width=5 by fpbg_fleq_trans, fpbg_strap1, fpbu_fpbc/
qed-.

lemma fpb_fpbg_trans: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2.
                      ⦃G1, L1, T1⦄ ≽[h, g] ⦃G, L, T⦄ → ⦃G, L, T⦄ >≡[h, g] ⦃G2, L2, T2⦄ →
                      ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 elim (fpb_fpbu … H1) -H1
/3 width=5 by fleq_fpbg_trans, fpbg_strap2, fpbu_fpbc/
qed-.

(* Properties on "qrst" parallel compuutation on closures *******************)

lemma fpbs_fpbg_trans: ∀h,g,G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G, L, T⦄ →
                       ∀G2,L2,T2. ⦃G, L, T⦄ >≡[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #L1 #L #T1 #T #H @(fpbs_ind … H) -G -L -T /3 width=5 by fpb_fpbg_trans/
qed-.

(* Note: this is used in the closure proof *)
lemma fpbg_fpbs_trans: ∀h,g,G,G2,L,L2,T,T2. ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄ →
                       ∀G1,L1,T1. ⦃G1, L1, T1⦄ >≡[h, g] ⦃G, L, T⦄ → ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄.
#h #g #G #G2 #L #L2 #T #T2 #H @(fpbs_ind_dx … H) -G -L -T /3 width=5 by fpbg_fpb_trans/
qed-.

lemma fpbu_fpbs_fpbg: ∀h,g,G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ≻[h, g] ⦃G, L, T⦄ → 
                      ∀G2,L2,T2. ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄.
/3 width=5 by fpbg_fpbs_trans, fpbu_fpbg/ qed.

(* Note: this is used in the closure proof *)
lemma fqup_fpbg: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim (fqup_inv_step_sn … H) -H
/3 width=5 by fqus_fpbs, fpbu_fqu, fpbu_fpbs_fpbg/
qed.

lemma cpxs_fpbg: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 →
                 (T1 = T2 → ⊥) → ⦃G, L, T1⦄ >≡[h, g] ⦃G, L, T2⦄.
#h #g #G #L #T1 #T2 #H #H0 elim (cpxs_neq_inv_step_sn … H … H0) -H -H0
/4 width=5 by cpxs_fpbs, fpbu_cpx, fpbu_fpbs_fpbg/
qed.

lemma lstas_fpbg: ∀h,g,G,L,T1,T2,l2. ⦃G, L⦄ ⊢ T1 •*[h, l2] T2 → (T1 = T2 → ⊥) →
                  ∀l1. l2 ≤ l1 → ⦃G, L⦄ ⊢ T1 ▪[h, g] l1 → ⦃G, L, T1⦄ >≡[h, g] ⦃G, L, T2⦄.
/3 width=5 by lstas_cpxs, cpxs_fpbg/ qed.

lemma lpxs_fpbg: ∀h,g,G,L1,L2,T. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 →
                 (L1 ≡[T, 0] L2 → ⊥) → ⦃G, L1, T⦄ >≡[h, g] ⦃G, L2, T⦄.
#h #g #G #L1 #L2 #T #H #H0 elim (lpxs_nlleq_inv_step_sn … H … H0) -H -H0
/4 width=5 by fpbu_fpbs_fpbg, fpbu_lpx, lpxs_lleq_fpbs/
qed.

lemma fpbs_fpbg: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄ →
                 ⦃G1, L1, T1⦄ ≡[0] ⦃G2, L2, T2⦄ ∨
                 ⦃G1, L1, T1⦄ >≡[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fpbs_ind … H) -G2 -L2 -T2
[ /2 width=1 by or_introl/
| #G #G2 #L #L2 #T #T2 #_ #H2 * #H1 elim (fpb_fpbu … H2) -H2 #H2
  [ /3 width=5 by fleq_trans, or_introl/
  | /5 width=5 by fpbc_fpbg, fleq_fpbc_trans, fpbu_fpbc, or_intror/
  | /3 width=5 by fpbg_fleq_trans, or_intror/
  | /4 width=5 by fpbg_strap1, fpbu_fpbc, or_intror/
  ]
]
qed-.
