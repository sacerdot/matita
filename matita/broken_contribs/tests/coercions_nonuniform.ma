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



axiom A : Type.
axiom B : A -> Type.
axiom f : A -> A.
axiom f1 : A -> A.

axiom k : ∀a:A.B (f a).

coercion cic:/matita/tests/coercions_nonuniform/k.con.

axiom C : Type.

(* axiom c1 : ∀a:A. B (f a) -> C. *) (* COQ NO: non uniform *)
(* axiom c1 : ∀a:A. B (f1 a) -> C. *) (* non si compongono, ma almeno ho le 2 non composte le ho e le posso usare *)
(* axiom c1 : ∀f.∀a:A.B (f a) -> C. *) (* COQ NO: non uniform *)

(* COQ NO: non uniform *)
axiom c2 : ∀a.B (f a) -> B (f1 a).
axiom c1 : ∀a:A. B (f1 a) -> C.

coercion cic:/matita/tests/coercions_nonuniform/c1.con.
coercion cic:/matita/tests/coercions_nonuniform/c2.con.

axiom g : C -> C.

definition test := λa:A.g a.

(*
Coq < Coercion c1 : B >-> C.                
User error: c1 does not respect the inheritance uniform condition
*)
