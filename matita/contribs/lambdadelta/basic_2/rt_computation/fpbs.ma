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

include "basic_2/notation/relations/btpredstar_8.ma".
include "basic_2/multiple/fqus.ma".
include "basic_2/reduction/fpbq.ma".
include "basic_2/computation/cpxs.ma".
include "basic_2/computation/lpxs.ma".

(* "QRST" PARALLEL COMPUTATION FOR CLOSURES *********************************)

definition fpbs: ∀h. sd h → tri_relation genv lenv term ≝
                 λh,o. tri_TC … (fpbq h o).

interpretation "'qrst' parallel computation (closure)"
   'BTPRedStar h o G1 L1 T1 G2 L2 T2 = (fpbs h o G1 L1 T1 G2 L2 T2).

(* Basic eliminators ********************************************************)

lemma fpbs_ind: ∀h,o,G1,L1,T1. ∀R:relation3 genv lenv term. R G1 L1 T1 →
                (∀G,G2,L,L2,T,T2. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G, L, T⦄ → ⦃G, L, T⦄ ≽[h, o] ⦃G2, L2, T2⦄ → R G L T → R G2 L2 T2) →
                ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄ → R G2 L2 T2.
/3 width=8 by tri_TC_star_ind/ qed-.

lemma fpbs_ind_dx: ∀h,o,G2,L2,T2. ∀R:relation3 genv lenv term. R G2 L2 T2 →
                   (∀G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ≽[h, o] ⦃G, L, T⦄ → ⦃G, L, T⦄ ≥[h, o] ⦃G2, L2, T2⦄ → R G L T → R G1 L1 T1) →
                   ∀G1,L1,T1. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄ → R G1 L1 T1.
/3 width=8 by tri_TC_star_ind_dx/ qed-.

(* Basic properties *********************************************************)

lemma fpbs_refl: ∀h,o. tri_reflexive … (fpbs h o).
/2 width=1 by tri_inj/ qed.

lemma fpbq_fpbs: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≽[h, o] ⦃G2, L2, T2⦄ →
                 ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/2 width=1 by tri_inj/ qed.

lemma fpbs_strap1: ∀h,o,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ ≽[h, o] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/2 width=5 by tri_step/ qed-.

lemma fpbs_strap2: ∀h,o,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ≽[h, o] ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ ≥[h, o] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/2 width=5 by tri_TC_strap/ qed-.

lemma fqup_fpbs: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                 ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2 
/4 width=5 by fqu_fquq, fpbq_fquq, tri_step/
qed.

lemma fqus_fpbs: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                 ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqus_ind … H) -G2 -L2 -T2 
/3 width=5 by fpbq_fquq, tri_step/
qed.

lemma cpxs_fpbs: ∀h,o,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[h, o] T2 → ⦃G, L, T1⦄ ≥[h, o] ⦃G, L, T2⦄.
#h #o #G #L #T1 #T2 #H @(cpxs_ind … H) -T2
/3 width=5 by fpbq_cpx, fpbs_strap1/
qed.

lemma lpxs_fpbs: ∀h,o,G,L1,L2,T. ⦃G, L1⦄ ⊢ ➡*[h, o] L2 → ⦃G, L1, T⦄ ≥[h, o] ⦃G, L2, T⦄.
#h #o #G #L1 #L2 #T #H @(lpxs_ind … H) -L2
/3 width=5 by fpbq_lpx, fpbs_strap1/
qed.

lemma lleq_fpbs: ∀h,o,G,L1,L2,T. L1 ≡[T, 0] L2 → ⦃G, L1, T⦄ ≥[h, o] ⦃G, L2, T⦄.
/3 width=1 by fpbq_fpbs, fpbq_lleq/ qed.

lemma cprs_fpbs: ∀h,o,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡* T2 → ⦃G, L, T1⦄ ≥[h, o] ⦃G, L, T2⦄.
/3 width=1 by cprs_cpxs, cpxs_fpbs/ qed.

lemma lprs_fpbs: ∀h,o,G,L1,L2,T. ⦃G, L1⦄ ⊢ ➡* L2 → ⦃G, L1, T⦄ ≥[h, o] ⦃G, L2, T⦄.
/3 width=1 by lprs_lpxs, lpxs_fpbs/ qed.

lemma fpbs_fqus_trans: ∀h,o,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G, L, T⦄ →
                       ⦃G, L, T⦄ ⊐* ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H @(fqus_ind … H) -G2 -L2 -T2
/3 width=5 by fpbs_strap1, fpbq_fquq/
qed-.

lemma fpbs_fqup_trans: ∀h,o,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G, L, T⦄ →
                       ⦃G, L, T⦄ ⊐+ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/3 width=5 by fpbs_fqus_trans, fqup_fqus/ qed-.

lemma fpbs_cpxs_trans: ∀h,o,G1,G,L1,L,T1,T,T2. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G, L, T⦄ →
                       ⦃G, L⦄ ⊢ T ➡*[h, o] T2 → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G, L, T2⦄.
#h #o #G1 #G #L1 #L #T1 #T #T2 #H1 #H @(cpxs_ind … H) -T2
/3 width=5 by fpbs_strap1, fpbq_cpx/
qed-.

lemma fpbs_lpxs_trans: ∀h,o,G1,G,L1,L,L2,T1,T. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G, L, T⦄ →
                       ⦃G, L⦄ ⊢ ➡*[h, o] L2 → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G, L2, T⦄.
#h #o #G1 #G #L1 #L #L2 #T1 #T #H1 #H @(lpxs_ind … H) -L2
/3 width=5 by fpbs_strap1, fpbq_lpx/
qed-.

lemma fpbs_lleq_trans: ∀h,o,G1,G,L1,L,L2,T1,T. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G, L, T⦄ →
                       L ≡[T, 0] L2 → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G, L2, T⦄.
/3 width=5 by fpbs_strap1, fpbq_lleq/ qed-.

lemma fqus_fpbs_trans: ∀h,o,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G, L, T⦄ ≥[h, o] ⦃G2, L2, T2⦄ →
                       ⦃G1, L1, T1⦄ ⊐* ⦃G, L, T⦄ → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H @(fqus_ind_dx … H) -G1 -L1 -T1
/3 width=5 by fpbs_strap2, fpbq_fquq/
qed-.

lemma cpxs_fpbs_trans: ∀h,o,G1,G2,L1,L2,T1,T,T2. ⦃G1, L1, T⦄ ≥[h, o] ⦃G2, L2, T2⦄ →
                       ⦃G1, L1⦄ ⊢ T1 ➡*[h, o] T → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G2 #L1 #L2 #T1 #T #T2 #H1 #H @(cpxs_ind_dx … H) -T1
/3 width=5 by fpbs_strap2, fpbq_cpx/
qed-.

lemma lpxs_fpbs_trans: ∀h,o,G1,G2,L1,L,L2,T1,T2. ⦃G1, L, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄ →
                       ⦃G1, L1⦄ ⊢ ➡*[h, o] L → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
#h #o #G1 #G2 #L1 #L #L2 #T1 #T2 #H1 #H @(lpxs_ind_dx … H) -L1
/3 width=5 by fpbs_strap2, fpbq_lpx/
qed-.

lemma lleq_fpbs_trans: ∀h,o,G1,G2,L1,L,L2,T1,T2. ⦃G1, L, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄ →
                       L1 ≡[T1, 0] L → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/3 width=5 by fpbs_strap2, fpbq_lleq/ qed-.

lemma cpxs_fqus_fpbs: ∀h,o,G1,G2,L1,L2,T1,T,T2. ⦃G1, L1⦄ ⊢ T1 ➡*[h, o] T →
                      ⦃G1, L1, T⦄ ⊐* ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/3 width=5 by fpbs_fqus_trans, cpxs_fpbs/ qed.

lemma cpxs_fqup_fpbs: ∀h,o,G1,G2,L1,L2,T1,T,T2. ⦃G1, L1⦄ ⊢ T1 ➡*[h, o] T →
                      ⦃G1, L1, T⦄ ⊐+ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/3 width=5 by fpbs_fqup_trans, cpxs_fpbs/ qed.

lemma fqus_lpxs_fpbs: ∀h,o,G1,G2,L1,L,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L, T2⦄ →
                      ⦃G2, L⦄ ⊢ ➡*[h, o] L2 → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/3 width=3 by fpbs_lpxs_trans, fqus_fpbs/ qed.

lemma cpxs_fqus_lpxs_fpbs: ∀h,o,G1,G2,L1,L,L2,T1,T,T2. ⦃G1, L1⦄ ⊢ T1 ➡*[h, o] T →
                           ⦃G1, L1, T⦄ ⊐* ⦃G2, L, T2⦄ → ⦃G2, L⦄ ⊢ ➡*[h, o] L2 → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/3 width=5 by cpxs_fqus_fpbs, fpbs_lpxs_trans/ qed.

lemma lpxs_lleq_fpbs: ∀h,o,G,L1,L,L2,T. ⦃G, L1⦄ ⊢ ➡*[h, o] L →
                      L ≡[T, 0] L2 → ⦃G, L1, T⦄ ≥[h, o] ⦃G, L2, T⦄.
/3 width=3 by lpxs_fpbs_trans, lleq_fpbs/ qed.

(* Note: this is used in the closure proof *)
lemma cpr_lpr_fpbs: ∀h,o,G,L1,L2,T1,T2. ⦃G, L1⦄ ⊢ T1 ➡ T2 → ⦃G, L1⦄ ⊢ ➡ L2 →
                    ⦃G, L1, T1⦄ ≥[h, o] ⦃G, L2, T2⦄.
/4 width=5 by fpbs_strap1, fpbq_fpbs, lpr_fpbq, cpr_fpbq/
qed.
