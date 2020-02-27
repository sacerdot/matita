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

include "ground_2/notation/functions/complement_1.ma".
include "ground_2/relocation/trace.ma".

(* RELOCATION TRACE *********************************************************)

let rec snot (t:trace) on t ≝ match t with
[ nil      ⇒ ◊
| cons b t ⇒ (¬ b) @ snot t
].

interpretation
   "complement (trace)"
   'Complement t = (snot t).

(* Basic properties *********************************************************)

lemma snot_empty: ∁ (◊) = ◊.
// qed.

lemma snot_inh: ∀t,b. ∁ (b@t) = (¬ b) @ ∁ t.
// qed.

lemma snot_true: ∀t. ∁ (Ⓣ @ t) = Ⓕ @ ∁ t.
// qed.

lemma snot_false: ∀t. ∁ (Ⓕ @ t) = Ⓣ @ ∁ t.
// qed.

lemma snot_length: ∀t. |∁ t| = |t|.
#t elim t -t normalize //
qed.

lemma snot_colength: ∀t. ∥∁ t∥ = |t| - ∥t∥.
#t elim t -t //
* /2 width=1 by minus_Sn_m/
qed.
