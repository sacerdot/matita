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

include "subterms/carrier.ma".
include "subterms/boolean.ma".

(* BOOLEANIZE (EMPTY OR FILL)  **********************************************)

definition booleanize: bool → subterms → subterms ≝
   λb,F. {b}⇑⇓F.

interpretation "make boolean (subterms)"
   'ProjectSame b F = (booleanize b F).

notation "hvbox( { term 46 b } ⇕ break term 46 F)"
   non associative with precedence 46
   for @{ 'ProjectSame $b $F }.

lemma booleanize_inv_vref: ∀j,b0,b,F. {b}⇕ F = {b0}#j →
                           ∃∃b1. b = b0 & F = {b1}#j.
#j #b0 #b #F #H
elim (boolean_inv_vref … H) -H #H0 #H
elim (carrier_inv_vref … H) -H /2 width=2/
qed-.

lemma booleanize_inv_abst: ∀U,b0,b,F. {b}⇕ F = {b0}𝛌.U →
                           ∃∃b1,T. b = b0 & {b}⇕T = U & F = {b1}𝛌.T.
#U #b0 #b #F #H
elim (boolean_inv_abst … H) -H #C #H0 #H1 #H
elim (carrier_inv_abst … H) -H #b1 #U1 #H3 destruct /2 width=4/
qed-.

lemma booleanize_inv_appl: ∀W,U,b0,b,F. {b}⇕ F = {b0}@W.U →
                           ∃∃b1,V,T. b = b0 & {b}⇕V = W & {b}⇕T = U & F = {b1}@V.T.
#W #U #b0 #b #F #H
elim (boolean_inv_appl … H) -H #D #C #H0 #H1 #H2 #H
elim (carrier_inv_appl … H) -H #b1 #W1 #U1 #H3 #H4 destruct /2 width=6/
qed-.
(*
lemma booleanize_lift: ∀b,h,F,d. {b}⇕ ↑[d, h] F = ↑[d, h] {b}⇕ F.
#b #h #M elim M -M normalize //
qed.

lemma booleanize_dsubst: ∀b,G,F,d. {b}⇕ [d ↙ G] F = [d ↙ {b}⇕ G] {b}⇕ F.
#b #N #M elim M -M [2,3: normalize // ]
*)
