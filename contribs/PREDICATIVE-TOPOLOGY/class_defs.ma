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

(* Project started Wed Oct 12, 2005 ***************************************)

set "baseuri" "cic:/matita/PREDICATIVE-TOPOLOGY/class_defs".

include "../../library/logic/connectives.ma".

(* ACZEL CATEGORIES:
   - We use typoids with a compatible membership relation
   - The category is intended to be the domain of the membership relation
   - The membership relation is necessary because we need to regard the
     domain of a propositional function (ie a predicative subset) as a
     quantification domain and therefore as a category, but there is no
     type in CIC representing the domain of a propositional function
   - We set up a single equality predicate, parametric on the category,
     defined as the reflexive, symmetic, transitive and compatible closure
     of the cle1 predicate given inside the category. Then we prove the 
     properties of the equality that usually are axiomatized inside the 
     category structure. This makes categories easier to use
*) 

definition true_f \def \lambda (X:Type). \lambda (_:X). True.

definition false_f \def \lambda (X:Type). \lambda (_:X). False.

record Class: Type \def {
   class:> Type;
   cin: class \to Prop;
   cle1: class \to class \to Prop
}.

inductive cle (C:Class) (c1:C): C \to Prop \def
   | cle_refl: cin ? c1 \to cle ? c1 c1
   | ceq_sing: \forall c2,c3. 
               cle ? c1 c2 \to cin ? c3 \to cle1 ? c2 c3 \to cle ? c1 c3.

inductive ceq (C:Class) (c1:C) (c2:C): Prop \def
   | ceq_intro: cle ? c1 c2 \to cle ? c2 c1 \to ceq ? c1 c2.
