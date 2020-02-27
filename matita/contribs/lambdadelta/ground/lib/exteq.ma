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

include "ground/notation/relations/doteq_4.ma".
include "ground/lib/relations.ma".

(* EXTENSIONAL EQUIVALENCE **************************************************)

definition exteq (A,B:Type[0]): relation (A → B) ≝
                                λf1,f2. ∀a. f1 a = f2 a.

interpretation "extensional equivalence"
   'DotEq A B f1 f2 = (exteq A B f1 f2).

(* Basic_properties *********************************************************)

lemma exteq_refl (A) (B): reflexive … (exteq A B).
// qed.

lemma exteq_repl (A) (B): replace_2 … (exteq A B) (exteq A B) (exteq A B).
// qed-.

lemma exteq_sym (A) (B): symmetric … (exteq A B).
/2 width=1 by exteq_repl/ qed-.

lemma exteq_trans (A) (B): Transitive … (exteq A B).
/2 width=1 by exteq_repl/ qed-.

