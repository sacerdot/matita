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

set "baseuri" "cic:/matita/higher_order_defs/relations/".

include "logic/connectives.ma".

definition reflexive: \forall A:Type.\forall R:A \to A \to Prop.Prop
\def 
\lambda A.\lambda R.\forall x:A.R x x.

definition symmetric: \forall A:Type.\forall R:A \to A \to Prop.Prop
\def 
\lambda A.\lambda R.\forall x,y:A.R x y \to R y x.

definition transitive: \forall A:Type.\forall R:A \to A \to Prop.Prop
\def 
\lambda A.\lambda R.\forall x,y,z:A.R x y \to R y z \to R x z.

definition irreflexive: \forall A:Type.\forall R:A \to A \to Prop.Prop
\def 
\lambda A.\lambda R.\forall x:A.\lnot (R x x).
