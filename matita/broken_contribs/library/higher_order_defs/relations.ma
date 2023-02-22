(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "logic/connectives.ma".

definition relation : Type \to Type
\def \lambda A:Type.A \to A \to Prop. 

definition reflexive: \forall A:Type.\forall R :relation A.Prop
\def 
\lambda A.\lambda R.\forall x:A.R x x.

definition symmetric: \forall A:Type.\forall R: relation A.Prop
\def 
\lambda A.\lambda R.\forall x,y:A.R x y \to R y x.

definition transitive: \forall A:Type.\forall R:relation A.Prop
\def 
\lambda A.\lambda R.\forall x,y,z:A.R x y \to R y z \to R x z.

definition irreflexive: \forall A:Type.\forall R:relation A.Prop
\def 
\lambda A.\lambda R.\forall x:A.\lnot (R x x).

definition cotransitive: \forall A:Type.\forall R:relation A.Prop
\def
\lambda A.\lambda R.\forall x,y:A.R x y \to \forall z:A. R x z \lor R z y.

definition tight_apart: \forall A:Type.\forall eq,ap:relation A.Prop
\def 
\lambda A.\lambda eq,ap.\forall x,y:A. (\not (ap x y) \to eq x y) \land
(eq x y \to \not (ap x y)).

definition antisymmetric: \forall A:Type.\forall R:relation A.Prop
\def 
\lambda A.\lambda R.\forall x,y:A. R x y \to \not (R y x).


