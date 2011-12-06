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

include "Basic_2/grammar/aarity.ma".
include "Basic_2/grammar/lenv.ma".

(* ABSTRACT CANDIDATES OF REDUCIBILITY **************************************)

(* the abstract candidate of reducibility associated to an atomic arity *)
let rec acr (R:lenv→predicate term) (A:aarity) (L:lenv) on A: predicate term ≝
λT. match A with
[ AAtom     ⇒ R L T
| APair B A ⇒ ∀V. acr R B L V → acr R A L (𝕔{Appl} V. T)
].

interpretation
   "candidate of reducibility (abstract)"
   'InEInt R L T A = (acr R A L T).
