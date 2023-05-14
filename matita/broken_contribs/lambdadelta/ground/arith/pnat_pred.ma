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

include "ground/notation/functions/downspoon_1.ma".
include "ground/arith/pnat_split.ma".

(* PREDECESSOR FOR POSITIVE INTEGERS ****************************************)

definition ppred (p): ℤ⁺ ≝
           psplit … (𝟏) (λp.p) p.

interpretation
  "predecessor (positive integers)"
  'DownSpoon p = (ppred p).

(* Basic constructions ******************************************************)

lemma ppred_unit: 𝟏 = ⫰𝟏.
// qed.

lemma ppred_succ (p): p = ⫰↑p.
// qed.

(* Basic inversions *********************************************************)

lemma ppred_inv_refl (p): p = ⫰p → 𝟏 = p.
#p elim p -p //
#p #IH #H /2 width=1 by/
qed-.

lemma pnat_split_unit_pos (p): ∨∨ 𝟏 = p | p = ↑⫰p.
#p elim p -p
/2 width=1 by or_introl, or_intror/
qed-.
