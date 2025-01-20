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

include "delayed_updating/reduction/dbf_step.ma".
include "delayed_updating/reduction/prototerm_dbf_residuals.ma".
include "delayed_updating/notation/relations/solidi_black_rightarrow_dbf_3.ma".

(* COMPLETE DEVELOPMENT FOR DELAYED BALANCED FOCUSED REDUCTION **************)

(* Note: the steps of a development can be performed in parallel *)
(* Note: so a complete development corresponds to a parallel reduction *)
inductive dbfd: 𝒫❨ℙ❩ → relation2 (𝕋) (𝕋) ≝
| dbfd_refl (u) (t1) (t2):
            u ⊆ Ⓕ → t1 ⇔ t2 → dbfd u t1 t2
| dbfd_step (u) (r) (t0) (t1) (t2):
            r ϵ u → t1 ➡𝐝𝐛𝐟[r] t0 →
            dbfd (u /𝐝𝐛𝐟{t1} r) t0 t2 → dbfd u t1 t2
.


interpretation
  "complete development (balanced focused reduction with delayed updating)"
  'SolidiBlackRightArrowDBF t1 u t2 = (dbfd u t1 t2).

(* Basic constructions ******************************************************)

lemma dbfd_self (t0) (t) (r):
      t0 ⫽➡𝐝𝐛𝐟[❴r❵ /𝐝𝐛𝐟{t} r] t0.
#t0 #t #r @dbfd_refl //
qed.

lemma dbfs_dbfd (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t2 → t1 ⫽➡𝐝𝐛𝐟[❴r❵] t2.
/2 width=5 by dbfd_step/
qed.
