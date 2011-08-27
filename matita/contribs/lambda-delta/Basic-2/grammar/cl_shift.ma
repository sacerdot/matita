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

include "Basic-2/grammar/cl_weight.ma".

(* SHIFT OF A CLOSURE *******************************************************)

let rec shift L T on L ≝ match L with
[ LSort       ⇒ T
| LPair L I V ⇒ shift L (𝕓{I} V. T)
].

interpretation "shift (closure)" 'Append L T = (shift L T).

(* Basic properties *********************************************************)

lemma tw_shift: ∀L,T. #[L, T] ≤ #[L @ T].
#L elim L //
#K #I #V #IHL #T
@transitive_le [3: @IHL |2: /2/ | skip ]
qed.

           
