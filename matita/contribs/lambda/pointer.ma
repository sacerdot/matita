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

include "preamble.ma".

(* POINTER ******************************************************************)

(* Policy: pointer step metavariables: c *)
(* Note: this is a step of a path in the tree representation of a term:
         rc (rectus)  : proceed on the argument of an abstraction
         sn (sinister): proceed on the left argument of an application
         dx (dexter)  : proceed on the right argument of an application
*)
inductive ptr_step: Type[0] ≝
| rc: ptr_step
| sn: ptr_step
| dx: ptr_step
.

definition is_dx: predicate ptr_step ≝ λc. dx = c.

(* Policy: pointer metavariables: p, q *)
(* Note: this is a path in the tree representation of a term, heading to a redex *)
definition ptr: Type[0] ≝ list ptr_step.

(* Note: a redex is "in the head" when is not under an abstraction nor in the lefr argument of an application *)
definition in_head: predicate ptr ≝ All … is_dx.

lemma in_head_ind: ∀R:predicate ptr. R (◊) →
                   (∀p. in_head p → R p → R (dx::p)) →
                   ∀p. in_head p → R p.
#R #H #IH #p elim p -p // -H *
#p #IHp * #H1 #H2 destruct /3 width=1/
qed-.
