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

include "explicit_updating/syntax/term_eq.ma".
include "explicit_updating/syntax/substitution.ma".

(* EXTENSIONAL EQUIVALENCE FOR SUBSTITUTION *********************************)

definition subst_eq: relation2 … ≝
           λS1,S2. ∀p. S1＠⧣❨p❩ ≐ S2＠⧣❨p❩.

interpretation
  "extensional equivalence (substitution)"
  'DotEq S1 S2 = (subst_eq S1 S2).

(* Basic constructions ******************************************************)

lemma subst_eq_refl:
      reflexive … subst_eq.
//
qed.

lemma subst_eq_sym:
      symmetric … subst_eq.
/2 width=1 by term_eq_sym/
qed-.

(* Main constructions *******************************************************)

theorem subst_eq_trans:
        Transitive … subst_eq.
/2 width=3 by term_eq_trans/
qed-.

theorem subst_eq_canc_sx:
        left_cancellable … subst_eq.
/2 width=3 by term_eq_canc_sx/
qed-.

theorem subst_eq_canc_dx:
        right_cancellable … subst_eq.
/2 width=3 by term_eq_canc_dx/
qed-.

theorem subst_eq_repl:
        replace_2 … subst_eq subst_eq subst_eq.
/2 width=5 by term_eq_repl/
qed.

(* Constructions with subst_dapp ********************************************)

lemma subst_dapp_eq_repl:
      compatible_3 … subst_eq (eq …) term_eq subst_dapp.
//
qed.
