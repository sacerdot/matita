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

record trz_map: Type[0] ≝
{ trz_staff    : ℤ → ℤ
; trz_injective: injective_2_fwd … (eq …) (eq …) trz_staff
}.

(* Note: this is trz_dapp *)
interpretation
  "depth application (total relocation maps with integers)"
  'AtSharp f z = (trz_staff f z).

definition trz_eq: relation2 trz_map trz_map ≝
           λf1,f2. trz_staff f1 ⊜ trz_staff f2.

interpretation
  "extensional equivalence (total relocation maps with integers)"
  'DotEq f1 f2 = (trz_eq f1 f2).

(* Basic constructions ******************************************************)

lemma trz_eq_refl:
      reflexive … trz_eq.
// qed.

lemma trz_eq_repl:
      replace_2 … trz_eq trz_eq trz_eq.
// qed-.

lemma trz_eq_sym:
      symmetric … trz_eq.
/2 width=1 by trz_eq_repl/
qed-.

lemma trz_eq_trans:
      Transitive … trz_eq.
/2 width=1 by trz_eq_repl/
qed-.

lemma trz_eq_canc_sn:
      left_cancellable … trz_eq.
/2 width=1 by trz_eq_repl/
qed-.

lemma trz_eq_canc_dx:
      right_cancellable … trz_eq.
/2 width=1 by trz_eq_repl/
qed-.

lemma trz_eq_replace_sym (Q):
      replace_1_back … trz_eq Q → replace_1_fwd … trz_eq Q.
/3 width=3 by trz_eq_sym/
qed-.

(* Basic inversions *********************************************************)

lemma trz_dapp_eq_repl (z):
      compatible_2_fwd … trz_eq (eq …) (λf.f＠⧣❨z❩).
// qed-.
