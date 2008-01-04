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

(* STATO: COMPILA *)

(* Project started Wed Oct 12, 2005 ***************************************)

set "baseuri" "cic:/matita/PREDICATIVE-TOPOLOGY/class_defs".

include "logic/connectives.ma".

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
   ceq: class \to class \to Prop;
   cin_repl: \forall c1,c2. cin c1 \to ceq c1 c2 \to cin c2;
   ceq_repl: \forall c1,c2,d1,d2. cin c1 \to
      ceq c1 c2 \to ceq c1 d1 \to ceq c2 d2 \to ceq d1 d2;
   ceq_refl: \forall c. cin c \to ceq c c
}.

(* external universal quantification *)
inductive call (C:Class) (P:C \to Prop) : Prop \def
   | call_intro: (\forall c. cin ? c \to P c) \to call C P.

inductive call2 (C1,C2:Class) (P:C1 \to C2 \to Prop) : Prop \def
   | call2_intro: 
      (\forall c1,c2. cin ? c1 \to cin ? c2 \to P c1 c2) \to call2 C1 C2 P.

(* notations **************************************************************)

(*CSC: the URI must disappear: there is a bug now *)
interpretation "external for all" 'xforall \eta.x =
  (cic:/matita/PREDICATIVE-TOPOLOGY/class_defs/call.ind#xpointer(1/1) _ x).

notation > "hvbox(\xforall ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'xforall ${default
  @{\lambda ${ident i} : $ty. $p}
  @{\lambda ${ident i} . $p}}}.

(*CSC: the URI must disappear: there is a bug now *)
interpretation "external for all 2" 'xforall2 \eta.x \eta.y =
  (cic:/matita/PREDICATIVE-TOPOLOGY/class_defs/call2.ind#xpointer(1/1) _ _ x y).

notation > "hvbox(\xforall ident i1 opt (: ty1) ident i2 opt (: ty2) break . p)"
  right associative with precedence 20
for @{ 'xforall2 ${default
  @{\lambda ${ident i1} : $ty1. \lambda ${ident i2} : $ty2. $p}
  @{\lambda ${ident i1}, ${ident i2}. $p}}}.
