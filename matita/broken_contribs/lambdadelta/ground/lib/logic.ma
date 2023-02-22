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

include "basics/logic.ma".
include "ground/notation/xoa/false_0.ma".
include "ground/notation/xoa/true_0.ma".
include "ground/notation/xoa/or_2.ma".
include "ground/notation/xoa/and_2.ma".

interpretation
  "false (logic)"
  'false = False.

interpretation
  "true (logic)"
  'true = True.

(* LOGIC ********************************************************************)

definition negation (A:Prop): Prop ≝
           A → ⊥.

(* Constructions with land **************************************************)

lemma commutative_and (A) (B):
      A ∧ B → B ∧ A.
#A #B * /2 width=1 by conj/
qed-.
