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

include "ng_pts.ma".

axiom A : Type.

axiom a : A. 
axiom b : A.

axiom B : Type.

axiom c : B. 
axiom d : B.


notation "#" with precedence 90 for @{ 'foo }.
interpretation "a" 'foo = a. 
interpretation "b" 'foo = b. 
interpretation "c" 'foo = c. 
interpretation "d" 'foo = d. 

alias symbol "foo" = "c".
alias symbol "foo" = "b".
alias symbol "foo" = "d".
alias symbol "foo" = "b".   

lemma xx : ∀P: A → B → Prop. P # #. (* NON STAMPA GLI ALIAS *) 

