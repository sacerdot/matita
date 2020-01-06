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

include "ground_2/xoa/ex_2_3.ma".
include "basic_2/notation/relations/predsubtystarproper_7.ma".
include "basic_2/rt_transition/fpb.ma".
include "basic_2/rt_computation/fpbs.ma".

(* PROPER PARALLEL RST-COMPUTATION FOR CLOSURES *****************************)

definition fpbg: ∀h. tri_relation genv lenv term ≝
                 λh,G1,L1,T1,G2,L2,T2.
                 ∃∃G,L,T. ⦃G1,L1,T1⦄ ≻[h] ⦃G,L,T⦄ & ⦃G,L,T⦄ ≥[h] ⦃G2,L2,T2⦄.

interpretation "proper parallel rst-computation (closure)"
   'PRedSubTyStarProper h G1 L1 T1 G2 L2 T2 = (fpbg h G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fpb_fpbg: ∀h,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ≻[h] ⦃G2,L2,T2⦄ →
                ⦃G1,L1,T1⦄ >[h] ⦃G2,L2,T2⦄.
/2 width=5 by ex2_3_intro/ qed.

lemma fpbg_fpbq_trans: ∀h,G1,G,G2,L1,L,L2,T1,T,T2.
                       ⦃G1,L1,T1⦄ >[h] ⦃G,L,T⦄ → ⦃G,L,T⦄ ≽[h] ⦃G2,L2,T2⦄ →
                       ⦃G1,L1,T1⦄ >[h] ⦃G2,L2,T2⦄.
#h #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 *
/3 width=9 by fpbs_strap1, ex2_3_intro/
qed-.

lemma fpbg_fqu_trans (h): ∀G1,G,G2,L1,L,L2,T1,T,T2.
                          ⦃G1,L1,T1⦄ >[h] ⦃G,L,T⦄ → ⦃G,L,T⦄ ⬂ ⦃G2,L2,T2⦄ →
                          ⦃G1,L1,T1⦄ >[h] ⦃G2,L2,T2⦄.
#h #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H2
/4 width=5 by fpbg_fpbq_trans, fpbq_fquq, fqu_fquq/
qed-.

(* Note: this is used in the closure proof *)
lemma fpbg_fpbs_trans: ∀h,G,G2,L,L2,T,T2. ⦃G,L,T⦄ ≥[h] ⦃G2,L2,T2⦄ →
                       ∀G1,L1,T1. ⦃G1,L1,T1⦄ >[h] ⦃G,L,T⦄ → ⦃G1,L1,T1⦄ >[h] ⦃G2,L2,T2⦄.
#h #G #G2 #L #L2 #T #T2 #H @(fpbs_ind_dx … H) -G -L -T /3 width=5 by fpbg_fpbq_trans/
qed-.

(* Basic_2A1: uses: fpbg_fleq_trans *)
lemma fpbg_feqx_trans: ∀h,G1,G,L1,L,T1,T. ⦃G1,L1,T1⦄ >[h] ⦃G,L,T⦄ →
                       ∀G2,L2,T2. ⦃G,L,T⦄ ≛ ⦃G2,L2,T2⦄ → ⦃G1,L1,T1⦄ >[h] ⦃G2,L2,T2⦄.
/3 width=5 by fpbg_fpbq_trans, fpbq_feqx/ qed-.

(* Properties with t-bound rt-transition for terms **************************)

lemma cpm_tneqx_cpm_fpbg (h) (G) (L):
                         ∀n1,T1,T. ⦃G,L⦄ ⊢ T1 ➡[n1,h] T → (T1 ≛ T → ⊥) →
                         ∀n2,T2. ⦃G,L⦄ ⊢ T ➡[n2,h] T2 → ⦃G,L,T1⦄ >[h] ⦃G,L,T2⦄.
/4 width=5 by fpbq_fpbs, cpm_fpbq, cpm_fpb, ex2_3_intro/ qed.
