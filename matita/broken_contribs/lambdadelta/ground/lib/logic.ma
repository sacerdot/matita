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
include "ground/notation/functions/commercialat_3.ma".
include "ground/notation/relations/not_eq_3.ma".

(* LOGIC ********************************************************************)

definition apply_dx (A:Type[0]) (B:Type[0]) (f:A→B) ≝
           f.

interpretation
  "right associative application"
  'CommercialAt A B f a = (apply_dx A B f a).

interpretation
  "false (logic)"
  'false = (False).

interpretation
  "true (logic)"
  'true = (True).

definition negation (A:Prop): Prop ≝
           A → ⊥.

interpretation
  "negated leibnitz's equality (logic)"
  'NotEq S a b = (negation (eq S a b)).

(* Basic constructions with apply_dx ****************************************)

lemma apply_dx_unfold (A) (B:Type[0]) (f:A→B):
      ∀a. f a = (f @ a).
//
qed.

(* Main constructions with eq ***********************************************)

theorem canc_sx_eq (A) (x) (y) (z:A):
        y = x → y = z → x = z.
// qed-.

theorem canc_dx_eq (A) (x) (y) (z:A):
        x = y → z = y → x = z.
// qed-.

theorem repl_eq (A) (x1) (x2) (y1) (y2:A):
        x1 = y1 → x2 = y2 → x1 = x2 → y1 = y2.
// qed-.

(* Constructions with land **************************************************)

lemma commutative_and (A) (B):
      A ∧ B → B ∧ A.
#A #B * /2 width=1 by conj/
qed-.
