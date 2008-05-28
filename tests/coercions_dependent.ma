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



include "nat/nat.ma".
include "list/list.ma".
include "decidable_kit/list_aux.ma".
(* tests from "Dependent Coersion" by Luo and Soloviev *)

inductive vec (A : Type) : nat -> Type :=
 | vnil : vec A O
 | vcons : ∀a:A.∀n:nat.vec A n -> vec A (S n).
 
axiom c : ∀A,B.∀l:list A.vec B (length A l).

axiom veclen : ∀A,n.vec A n -> nat.

coercion cic:/matita/tests/coercions_dependent/c.con.

alias num (instance 0) = "natural number".
definition xxx := veclen nat ? [3; 4; 7].
