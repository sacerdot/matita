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

include "basic_2/notation/relations/predsubtyproper_7.ma".
include "static_2/s_transition/fqu.ma".
include "static_2/static/rdeq.ma".
include "basic_2/rt_transition/lpr_lpx.ma".

(* PROPER PARALLEL RST-TRANSITION FOR CLOSURES ******************************)

inductive fpb (h) (G1) (L1) (T1): relation3 genv lenv term ≝
| fpb_fqu: ∀G2,L2,T2. ⦃G1,L1,T1⦄ ⬂ ⦃G2,L2,T2⦄ → fpb h G1 L1 T1 G2 L2 T2
| fpb_cpx: ∀T2. ⦃G1,L1⦄ ⊢ T1 ⬈[h] T2 → (T1 ≛ T2 → ⊥) → fpb h G1 L1 T1 G1 L1 T2
| fpb_lpx: ∀L2. ⦃G1,L1⦄ ⊢ ⬈[h] L2 → (L1 ≛[T1] L2 → ⊥) → fpb h G1 L1 T1 G1 L2 T1
.

interpretation
   "proper parallel rst-transition (closure)"
   'PRedSubTyProper h G1 L1 T1 G2 L2 T2 = (fpb h G1 L1 T1 G2 L2 T2).

(* Basic properties *********************************************************)

(* Basic_2A1: includes: cpr_fpb *)
lemma cpm_fpb (n) (h) (G) (L): ∀T1,T2. ⦃G,L⦄ ⊢ T1 ➡[n,h] T2 → (T1 ≛ T2 → ⊥) →
                                   ⦃G,L,T1⦄ ≻[h] ⦃G,L,T2⦄.
/3 width=2 by fpb_cpx, cpm_fwd_cpx/ qed.

lemma lpr_fpb (h) (G) (T): ∀L1,L2. ⦃G,L1⦄ ⊢ ➡[h] L2 → (L1 ≛[T] L2 → ⊥) →
                           ⦃G,L1,T⦄ ≻[h] ⦃G,L2,T⦄.
/3 width=1 by fpb_lpx, lpr_fwd_lpx/ qed.
