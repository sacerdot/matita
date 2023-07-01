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

include "ground/arith/int.ma".
include "ground/lib/exteq.ma".
include "ground/lib/functions.ma".
include "ground/notation/relations/doteq_2.ma".
include "ground/notation/functions/atsharp_2.ma".

(* TOTAL RELOCATION MAPS WITH INTEGERS **************************************)

record tzr_map: Type[0] ≝
{ tzr_staff    : ℤ → ℤ
; tzr_injective: injective_2_fwd … (eq …) (eq …) tzr_staff
}.

(* Note: this is tzr_dapp *)
interpretation
  "depth application (total relocation maps with integers)"
  'AtSharp f z = (tzr_staff f z).

definition tzr_eq: relation2 tzr_map tzr_map ≝
           λf1,f2. tzr_staff f1 ⊜ tzr_staff f2.

interpretation
  "extensional equivalence (total relocation maps with integers)"
  'DotEq f1 f2 = (tzr_eq f1 f2).

(* Basic constructions ******************************************************)

lemma tzr_eq_refl:
      reflexive … tzr_eq.
// qed.

lemma tzr_eq_repl:
      replace_2 … tzr_eq tzr_eq tzr_eq.
// qed-.

lemma tzr_eq_sym:
      symmetric … tzr_eq.
/2 width=1 by tzr_eq_repl/
qed-.

lemma tzr_eq_trans:
      Transitive … tzr_eq.
/2 width=1 by tzr_eq_repl/
qed-.

lemma tzr_eq_canc_sn:
      left_cancellable … tzr_eq.
/2 width=1 by tzr_eq_repl/
qed-.

lemma tzr_eq_canc_dx:
      right_cancellable … tzr_eq.
/2 width=1 by tzr_eq_repl/
qed-.

lemma tzr_eq_replace_sym (Q):
      replace_1_back … tzr_eq Q → replace_1_fwd … tzr_eq Q.
/3 width=3 by tzr_eq_sym/
qed-.

(* Basic inversions *********************************************************)

lemma tzr_dapp_eq_repl (z):
      compatible_2_fwd … tzr_eq (eq …) (λf.f＠⧣❨z❩).
// qed-.
