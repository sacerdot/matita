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
include "basic_2/substitution/fqus.ma".
include "basic_2/reduction/fpb.ma".
include "basic_2/computation/cpxs.ma".
include "basic_2/computation/lpxs.ma".

(* "BIG TREE" PARALLEL COMPUTATION FOR CLOSURES *****************************)

definition fpbs: ∀h. sd h → tri_relation genv lenv term ≝
                 λh,g. tri_TC … (fpb h g).

interpretation "'big tree' parallel computation (closure)"
   'BTPRedStar h g G1 L1 T1 G2 L2 T2 = (fpbs h g G1 L1 T1 G2 L2 T2).

(* Basic eliminators ********************************************************)

lemma fpbs_ind: ∀h,g,G1,L1,T1. ∀R:relation3 genv lenv term. R G1 L1 T1 →
                (∀G,G2,L,L2,T,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G, L, T⦄ → ⦃G, L, T⦄ ≽[h, g] ⦃G2, L2, T2⦄ → R G L T → R G2 L2 T2) →
                ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2.
/3 width=8 by tri_TC_star_ind/ qed-.

lemma fpbs_ind_dx: ∀h,g,G2,L2,T2. ∀R:relation3 genv lenv term. R G2 L2 T2 →
                   (∀G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G, L, T⦄ → ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄ → R G L T → R G1 L1 T1) →
                   ∀G1,L1,T1. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄ → R G1 L1 T1.
/3 width=8 by tri_TC_star_ind_dx/ qed-.

(* Basic properties *********************************************************)

lemma fpbs_refl: ∀h,g. tri_reflexive … (fpbs h g).
/2 width=1 by tri_inj/ qed.

lemma fpb_fpbs: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄ →
                ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
/2 width=1 by tri_inj/ qed.

lemma fpbs_strap1: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ ≽[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
/2 width=5 by tri_step/ qed-.

lemma fpbs_strap2: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
/2 width=5 by tri_TC_strap/ qed-.

lemma fqus_fpbs: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃* ⦃G2, L2, T2⦄ →
                 ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqus_ind … L2 T2 H) -G2 -L2 -T2 
/3 width=5 by fpb_fquq, tri_step/
qed.

lemma cpxs_fpbs: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 → ⦃G, L, T1⦄ ≥[h, g] ⦃G, L, T2⦄.
#h #g #G #L #T1 #T2 #H @(cpxs_ind … H) -T2 
/3 width=5 by fpb_cpx, fpbs_strap1/
qed.

lemma lpxs_fpbs: ∀h,g,G,L1,L2,T. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → ⦃G, L1, T⦄ ≥[h, g] ⦃G, L2, T⦄.
#h #g #G #L1 #L2 #T #H @(lpxs_ind … H) -L2
/3 width=5 by fpb_lpx, fpbs_strap1/
qed.

lemma cprs_fpbs: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡* T2 → ⦃G, L, T1⦄ ≥[h, g] ⦃G, L, T2⦄.
/3 width=1 by cprs_cpxs, cpxs_fpbs/ qed.

lemma lprs_fpbs: ∀h,g,G,L1,L2,T. ⦃G, L1⦄ ⊢ ➡* L2 → ⦃G, L1, T⦄ ≥[h, g] ⦃G, L2, T⦄.
/3 width=1 by lprs_lpxs, lpxs_fpbs/ qed.

lemma cpr_lpr_fpbs: ∀h,g,G,L1,L2,T1,T2. ⦃G, L1⦄ ⊢ T1 ➡ T2 → ⦃G, L1⦄ ⊢ ➡ L2 →
                    ⦃G, L1, T1⦄ ≥[h, g] ⦃G, L2, T2⦄.
/4 width=5 by fpbs_strap1, lpr_fpb, cpr_fpb/ qed.
