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

include "term.ma".

(* REDEX POINTER ************************************************************)

(* Policy: boolean metavariables: a, b
           pointer metavariables: p, q
*)
(* Note: this is a path in the tree representation of a term
         in which abstraction nodes are omitted;
         on application nodes, "false" means "proceed left"
         and "true" means "proceed right"
*)
definition rpointer: Type[0] ≝ list bool.

(* Note: precedence relation on redex pointers: p ≺ q
         to serve as base for the order relations: p < q and p ≤ q *)
inductive rpprec: relation rpointer ≝
| rpprec_nil : ∀b,q.   rpprec ([]) (b::q)
| rppprc_cons: ∀p,q.   rpprec (false::p) (true::q)
| rpprec_comp: ∀b,p,q. rpprec p q → rpprec (b::p) (b::q)
.

interpretation "'precedes' on redex pointers"
   'prec p q = (rpprec p q).

(* Note: this should go to core_notation *)
notation "hvbox(a break ≺ b)"
   non associative with precedence 45
   for @{ 'prec $a $b }.

(* Note: this is p < q *)
interpretation "'less than' on redex pointers"
   'lt p q = (TC rpointer rpprec p q).

(* Note: this is p ≤ q, that *really* is p < q ∨ p = q *)
interpretation "'less or equal to' on redex pointers"
   'leq x y = (RC rpointer (TC rpointer rpprec) x y).
