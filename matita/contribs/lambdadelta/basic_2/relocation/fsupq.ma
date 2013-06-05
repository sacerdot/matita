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

include "basic_2/relocation/fsup.ma".

(* OPTIONAL SUPCLOSURE ******************************************************)

definition fsupq: bi_relation lenv term ≝ bi_RC … fsup.

interpretation
   "optional structural successor (closure)"
   'SupTermOpt L1 T1 L2 T2 = (fsup L1 T1 L2 T2).

(* Basic properties *********************************************************)

lemma fsupq_refl: bi_reflexive … fsupq.
/2 width=1/ qed.

lemma fsup_fsupq: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⊃ ⦃L2, T2⦄ → ⦃L1, T1⦄ ⊃⸮ ⦃L2, T2⦄.
/2 width=1/ qed.

