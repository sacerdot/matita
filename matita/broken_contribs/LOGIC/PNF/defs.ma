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



(* NORMAL FORM PREDICATE FOR PROOFS IN CONTEXT
   For cut elimination
*)

include "PEq/defs.ma".
include "PRed/defs.ma".

inductive PNF (P:Context) (p:Proof): Prop \def
   | pnf: (\forall q,Q,S. [P, p, S] => [Q, q, S] \to [P, p] = [Q, q]) \to 
          PNF P p
.
