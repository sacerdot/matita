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

include "basic_2/substitution/fsupp.ma".
include "basic_2/computation/lprs.ma".
include "basic_2/dynamic/ypr.ma".

(* "BIG TREE" PARALLEL COMPUTATION FOR CLOSURES *****************************)

definition yprs: ∀h. sd h → bi_relation lenv term ≝
                 λh,g. bi_TC … (ypr h g).

interpretation "'big tree' parallel computation (closure)"
   'BTPRedStar h g L1 T1 L2 T2 = (yprs h g L1 T1 L2 T2).

(* Basic eliminators ********************************************************)

lemma yprs_ind: ∀h,g,L1,T1. ∀R:relation2 lenv term. R L1 T1 →
                (∀L,L2,T,T2. h ⊢ ⦃L1, T1⦄ ≥[g] ⦃L, T⦄ → h ⊢ ⦃L, T⦄ ≽[g] ⦃L2, T2⦄ → R L T → R L2 T2) →
                ∀L2,T2. h ⊢ ⦃L1, T1⦄ ≥[g] ⦃L2, T2⦄ → R L2 T2.
/3 width=7 by bi_TC_star_ind/ qed-.

lemma yprs_ind_dx: ∀h,g,L2,T2. ∀R:relation2 lenv term. R L2 T2 →
                   (∀L1,L,T1,T. h ⊢ ⦃L1, T1⦄ ≽[g] ⦃L, T⦄ → h ⊢ ⦃L, T⦄ ≥[g] ⦃L2, T2⦄ → R L T → R L1 T1) →
                   ∀L1,T1. h ⊢ ⦃L1, T1⦄ ≥[g] ⦃L2, T2⦄ → R L1 T1.
/3 width=7 by bi_TC_star_ind_dx/ qed-.

(* Basic properties *********************************************************)

lemma yprs_refl: ∀h,g. bi_reflexive … (yprs h g).
/2 width=1/ qed.

lemma ypr_yprs: ∀h,g,L1,L2,T1,T2. h ⊢ ⦃L1, T1⦄ ≽[g] ⦃L2, T2⦄ →
                h ⊢ ⦃L1, T1⦄ ≥[g] ⦃L2, T2⦄.
/2 width=1/ qed.

lemma yprs_strap1: ∀h,g,L1,L,L2,T1,T,T2. h ⊢ ⦃L1, T1⦄ ≥[g] ⦃L, T⦄ →
                   h ⊢ ⦃L, T⦄ ≽[g] ⦃L2, T2⦄ → h ⊢ ⦃L1, T1⦄ ≥[g] ⦃L2, T2⦄.
/2 width=4/ qed-.

lemma yprs_strap2: ∀h,g,L1,L,L2,T1,T,T2. h ⊢ ⦃L1, T1⦄ ≽[g] ⦃L, T⦄ →
                   h ⊢ ⦃L, T⦄ ≥[g] ⦃L2, T2⦄ → h ⊢ ⦃L1, T1⦄ ≥[g] ⦃L2, T2⦄.
/2 width=4/ qed-.

(* Note: this is a general property of bi_TC *)
lemma fsupp_yprs: ∀h,g,L1,L2,T1,T2. ⦃L1, T1⦄ ⊃+ ⦃L2, T2⦄ →
                  h ⊢ ⦃L1, T1⦄ ≥[g] ⦃L2, T2⦄.
#h #g #L1 #L2 #T1 #T2 #H @(fsupp_ind … L2 T2 H) -L2 -T2 /3 width=1/ /3 width=4/
qed.

lemma cprs_yprs: ∀h,g,L,T1,T2. L ⊢ T1 ➡* T2 → h ⊢ ⦃L, T1⦄ ≥[g] ⦃L, T2⦄.
#h #g #L #T1 #T2 #H @(cprs_ind … H) -T2 // /3 width=4 by ypr_cpr, yprs_strap1/
qed.

lemma lprs_yprs: ∀h,g,L1,L2,T. L1 ⊢ ➡* L2 → h ⊢ ⦃L1, T⦄ ≥[g] ⦃L2, T⦄.
#h #g #L1 #L2 #T #H @(lprs_ind … H) -L2 // /3 width=4 by ypr_lpr, yprs_strap1/
qed.

lemma sstas_yprs: ∀h,g,L,T1,T2. ⦃h, L⦄ ⊢ T1 •*[g] T2 →
                  h ⊢ ⦃L, T1⦄ ≥[g] ⦃L, T2⦄.
#h #g #L #T1 #T2 #H @(sstas_ind … H) -T2 // /3 width=4 by ypr_ssta, yprs_strap1/
qed.

lemma lsubsv_yprs: ∀h,g,L1,L2,T. h ⊢ L2 ¡⊑[g] L1 → h ⊢ ⦃L1, T⦄ ≥[g] ⦃L2, T⦄.
/3 width=1/ qed.

lemma cprs_lpr_yprs: ∀h,g,L1,L2,T1,T2. L1 ⊢ T1 ➡* T2 → L1 ⊢ ➡ L2 →
                     h ⊢ ⦃L1, T1⦄ ≥[g] ⦃L2, T2⦄.
/3 width=4 by yprs_strap1, ypr_lpr, cprs_yprs/
qed.
