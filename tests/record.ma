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



record empty : Type \def {}.

inductive True : Prop \def I: True.

record pippo : Type \def 
{
a: Set ;
b: a \to Prop;
c: \forall x:a.(b x) \to a \to Type 
}.

record pluto (A, B:Set) : Type \def {
d: A \to B \to Prop;
e: \forall y:A.\forall z:B. (d y z) \to A \to B;
mario: \forall y:A.\forall z:B. \forall h:(d y z). \forall i : B \to Prop.
   i (e y z h y)
}.

record paperino: Prop \def {
  paolo : Type;
  pippo : paolo \to paolo;
  piero : True
}.

(* the following test used to show the following bug: the left
   parameter A in the type of t was not unified with the left
   parameter A in the type of the constructor of the record *)
record t (A:Type) : Type := { f : A }.