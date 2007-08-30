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

set "baseuri" "cic:/matita/test/".

include "logic/equality.ma".
include "nat/nat.ma".

axiom A : nat -> Type.
axiom B : nat -> Type.
axiom A1: nat -> Type.
axiom B1: nat -> Type.
axiom b : ∀n.B n.
axiom c : ∀n,m. A1 n -> A m.
axiom d : ∀n,m. B n -> B1 m.
axiom f : ∀n,m. A n -> B m.

coercion cic:/matita/test/c.con.
coercion cic:/matita/test/d.con.

definition foo :=  λn,n1,m,m1.(λx.d m m1 (f n m (c n1 n x)) : A1 n1 -> B1 m1).
definition foo1_1 := λn,n1,m,m1.(f n m : A1 n1 -> B1 m1).

definition g := λn,m.λx:A n.b m.
definition foo2 := λn,n1,m,m1.(g n m : A1 n1 -> B1 m1).
definition foo3 := λn1,n,m,m1.(g n m : A1 n1 -> B1 m1).
definition foo4 := λn1,n,m1,m.(g n m : A1 n1 -> B1 m1).

