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
include "basic_2/substitution/fsupp.ma".
include "basic_2/computation/lprs.ma".
include "basic_2/dynamic/ypr.ma".

(* "BIG TREE" PARALLEL COMPUTATION FOR CLOSURES *****************************)

definition yprs: ∀h. sd h → tri_relation genv lenv term ≝
                 λh,g. tri_TC … (ypr h g).

interpretation "'big tree' parallel computation (closure)"
   'BTPRedStar h g G1 L1 T1 G2 L2 T2 = (yprs h g G1 L1 T1 G2 L2 T2).

(* Basic eliminators ********************************************************)

lemma yprs_ind: ∀h,g,G1,L1,T1. ∀R:relation3 genv lenv term. R G1 L1 T1 →
                (∀L,G2,G,L2,T,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G, L, T⦄ → ⦃G, L, T⦄ ≽[h, g] ⦃G2, L2, T2⦄ → R G L T → R G2 L2 T2) →
                ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄ → R G2 L2 T2.
/3 width=8 by tri_TC_star_ind/ qed-.

lemma yprs_ind_dx: ∀h,g,G2,L2,T2. ∀R:relation3 genv lenv term. R G2 L2 T2 →
                   (∀G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G, L, T⦄ → ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄ → R G L T → R G1 L1 T1) →
                   ∀G1,L1,T1. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄ → R G1 L1 T1.
/3 width=8 by tri_TC_star_ind_dx/ qed-.

(* Basic properties *********************************************************)

lemma yprs_refl: ∀h,g. tri_reflexive … (yprs h g).
/2 width=1/ qed.

lemma ypr_yprs: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G2, L2, T2⦄ →
                ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
/2 width=1/ qed.

lemma yprs_strap1: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ≥[h, g] ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ ≽[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
/2 width=5/ qed-.

lemma yprs_strap2: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ≽[h, g] ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ ≥[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
/2 width=5/ qed-.

(* Note: this is a general property of bi_TC *)
lemma fsupp_yprs: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃+ ⦃G2, L2, T2⦄ →
                  ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fsupp_ind … L2 T2 H) -G2 -L2 -T2 /3 width=1/ /3 width=5/
qed.

lemma cprs_yprs: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡* T2 → ⦃G, L, T1⦄ ≥[h, g] ⦃G, L, T2⦄.
#h #g #G #L #T1 #T2 #H @(cprs_ind … H) -T2 // /3 width=5 by ypr_cpr, yprs_strap1/
qed.

lemma lprs_yprs: ∀h,g,G,L1,L2,T. ⦃G, L1⦄ ⊢ ➡* L2 → ⦃G, L1, T⦄ ≥[h, g] ⦃G, L2, T⦄.
#h #g #G #L1 #L2 #T #H @(lprs_ind … H) -L2 // /3 width=5 by ypr_lpr, yprs_strap1/
qed.

lemma lsubsv_yprs: ∀h,g,G,L1,L2,T. G ⊢ L2 ¡⊑[h, g] L1 → ⦃G, L1, T⦄ ≥[h, g] ⦃G, L2, T⦄.
/3 width=1/ qed.

lemma cpr_lpr_yprs: ∀h,g,G,L1,L2,T1,T2. ⦃G, L1⦄ ⊢ T1 ➡ T2 → ⦃G, L1⦄ ⊢ ➡ L2 →
                    ⦃G, L1, T1⦄ ≥[h, g] ⦃G, L2, T2⦄.
/4 width=5 by yprs_strap1, ypr_lpr, ypr_cpr/ qed.

lemma ssta_yprs: ∀h,g,G,L,T,U,l.
                 ⦃G, L⦄ ⊢ T ▪[h, g] l+1 → ⦃G, L⦄ ⊢ T •[h, g] U →
                 ⦃G, L, T⦄ ≥[h, g] ⦃G, L, U⦄.
/3 width=2 by ypr_yprs, ypr_ssta/ qed.
