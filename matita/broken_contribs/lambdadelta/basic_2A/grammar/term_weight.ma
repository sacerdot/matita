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

include "basic_2A/notation/functions/weight_1.ma".
include "basic_2A/grammar/term.ma".

(* WEIGHT OF A TERM *********************************************************)

let rec tw T ≝ match T with
[ TAtom _     ⇒ 1
| TPair _ V T ⇒ tw V + tw T + 1
].

interpretation "weight (term)" 'Weight T = (tw T).

(* Basic properties *********************************************************)

lemma tw_pos: ∀T. 1 ≤ ♯{T}.
#T elim T -T //
qed.
