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

include "apps_2/models/model_props.ma".

(* EVALUATION EQUIVALENCE  **************************************************)

definition veq (M): relation (evaluation M) ≝
                    λv1,v2. ∀d. v1 d ≗ v2 d.

interpretation "evaluation equivalence (model)"
   'RingEq M v1 v2 = (veq M v1 v2).

(* Basic properties *********************************************************)

lemma veq_refl (M): is_model M →
                    reflexive … (veq M).
/2 width=1 by mq/ qed.
(*
lemma veq_sym: ∀M. symmetric … (veq M).
// qed-.

theorem veq_trans: ∀M. transitive … (veq M).
// qed-.
*)