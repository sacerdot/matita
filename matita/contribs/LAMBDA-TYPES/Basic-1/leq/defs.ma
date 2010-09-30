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

(* This file was automatically generated: do not edit *********************)

include "Basic-1/aplus/defs.ma".

inductive leq (g: G): A \to (A \to Prop) \def
| leq_sort: \forall (h1: nat).(\forall (h2: nat).(\forall (n1: nat).(\forall 
(n2: nat).(\forall (k: nat).((eq A (aplus g (ASort h1 n1) k) (aplus g (ASort 
h2 n2) k)) \to (leq g (ASort h1 n1) (ASort h2 n2)))))))
| leq_head: \forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (\forall (a3: 
A).(\forall (a4: A).((leq g a3 a4) \to (leq g (AHead a1 a3) (AHead a2 
a4))))))).

