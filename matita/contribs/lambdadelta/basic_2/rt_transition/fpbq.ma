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

include "basic_2/notation/relations/predsubty_8.ma".
include "basic_2/static/ffdeq.ma".
include "basic_2/s_transition/fquq.ma".
include "basic_2/rt_transition/lfpr_lfpx.ma".

(* PARALLEL RST-TRANSITION FOR CLOSURES *************************************)

(* Basic_2A1: includes: fpbq_lleq *)
inductive fpbq (h) (o) (G1) (L1) (T1): relation3 genv lenv term ≝
| fpbq_fquq : ∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ → fpbq h o G1 L1 T1 G2 L2 T2
| fpbq_cpx  : ∀T2. ⦃G1, L1⦄ ⊢ T1 ⬈[h] T2 → fpbq h o G1 L1 T1 G1 L1 T2
| fpbq_lfpx : ∀L2. ⦃G1, L1⦄ ⊢ ⬈[h, T1] L2 → fpbq h o G1 L1 T1 G1 L2 T1
| ffpq_lfdeq: ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≛[h, o] ⦃G2, L2, T2⦄ → fpbq h o G1 L1 T1 G2 L2 T2
.

interpretation
   "parallel rst-transition (closure)"
   'PRedSubTy h o G1 L1 T1 G2 L2 T2 = (fpbq h o G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

lemma fpbq_refl: ∀h,o. tri_reflexive … (fpbq h o).
/2 width=1 by fpbq_cpx/ qed.

(* Basic_2A1: includes: cpr_fpbq *)
lemma cpm_fpbq: ∀n,h,o,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[n, h] T2 → ⦃G, L, T1⦄ ≽[h, o] ⦃G, L, T2⦄. 
/3 width=2 by fpbq_cpx, cpm_fwd_cpx/ qed.

lemma lfpr_fpbq: ∀h,o,G,L1,L2,T. ⦃G, L1⦄ ⊢ ➡[h, T] L2 → ⦃G, L1, T⦄ ≽[h, o] ⦃G, L2, T⦄.
/3 width=1 by fpbq_lfpx, lfpr_fwd_lfpx/ qed.

(* Basic_2A1: removed theorems 2:
              fpbq_fpbqa fpbqa_inv_fpbq
*)
