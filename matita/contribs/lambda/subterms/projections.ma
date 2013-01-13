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

include "terms/term.ma".
include "subterms/subterms.ma".

(* PROJECTIONS **************************************************************)

(* Note: the boolean subset of subterms *) 
let rec boolean b M on M ≝ match M with
[ VRef i   ⇒ {b}#i
| Abst A   ⇒ {b}𝛌.(boolean b A)
| Appl B A ⇒ {b}@(boolean b B).(boolean b A)
].

interpretation "boolean subset (subterms)"
   'ProjectUp b M = (boolean b M).

notation "hvbox( { term 46 b } ⇑ break term 46 M)"
   non associative with precedence 46
   for @{ 'ProjectUp $b $M }.

lemma boolean_inv_vref: ∀j,b0,b,M. {b}⇑ M = {b0}#j → b = b0 ∧ M = #j.
#j #b0 #b * normalize
[ #i #H destruct /2 width=1/
| #A #H destruct
| #B #A #H destruct
]
qed-.

lemma boolean_inv_abst: ∀U,b0,b,M. {b}⇑ M = {b0}𝛌.U →
                        ∃∃C. b = b0 & {b}⇑C = U & M = 𝛌.C.
#U #b0 #b * normalize
[ #i #H destruct
| #A #H destruct /2 width=3/
| #B #A #H destruct
]
qed-.

lemma boolean_inv_appl: ∀W,U,b0,b,M. {b}⇑ M = {b0}@W.U →
                        ∃∃D,C. b = b0 & {b}⇑D = W & {b}⇑C = U & M = @D.C.
#W #U #b0 #b * normalize
[ #i #H destruct
| #A #H destruct
| #B #A #H destruct /2 width=5/
]
qed-.

(* Note: the carrier (underlying term) of a subset of subterms *)
let rec carrier F on F ≝ match F with
[ SVRef _ i   ⇒ #i
| SAbst _ T   ⇒ 𝛌.(carrier T)
| SAppl _ V T ⇒ @(carrier V).(carrier T)
].

interpretation "carrier (subterms)"
   'ProjectDown F = (carrier F).

notation "hvbox(⇓ term 46 F)"
   non associative with precedence 46
   for @{ 'ProjectDown $F }.

lemma carrier_inv_vref: ∀j,F. ⇓F = #j → ∃b. F = {b}#j.
#j * normalize
[ #b #i #H destruct /2 width=2/
| #b #T #H destruct
| #b #V #T #H destruct
]
qed-.

lemma carrier_inv_abst: ∀C,F. ⇓F = 𝛌.C → ∃∃b,U. ⇓U = C & F = {b}𝛌.U.
#C * normalize
[ #b #i #H destruct
| #b #T #H destruct /2 width=4/
| #b #V #T #H destruct
]
qed-.

lemma carrier_inv_appl: ∀D,C,F. ⇓F = @D.C →
                        ∃∃b,W,U. ⇓W = D & ⇓U = C & F = {b}@W.U.
#D #C * normalize
[ #b #i #H destruct
| #b #T #H destruct
| #b #V #T #H destruct /2 width=6/
]
qed-.

definition mk_boolean: bool → subterms → subterms ≝
   λb,F. {b}⇑⇓F.

interpretation "make boolean (subterms)"
   'ProjectSame b F = (mk_boolean b F).

notation "hvbox( { term 46 b } ⇕ break term 46 F)"
   non associative with precedence 46
   for @{ 'ProjectSame $b $F }.

lemma mk_boolean_inv_vref: ∀j,b0,b,F. {b}⇕ F = {b0}#j →
                           ∃∃b1. b = b0 & F = {b1}#j.
#j #b0 #b #F #H
elim (boolean_inv_vref … H) -H #H0 #H
elim (carrier_inv_vref … H) -H /2 width=2/
qed-.

lemma mk_boolean_inv_abst: ∀U,b0,b,F. {b}⇕ F = {b0}𝛌.U →
                           ∃∃b1,T. b = b0 & {b}⇕T = U & F = {b1}𝛌.T.
#U #b0 #b #F #H
elim (boolean_inv_abst … H) -H #C #H0 #H1 #H
elim (carrier_inv_abst … H) -H #b1 #U1 #H3 destruct /2 width=4/
qed-.

lemma mk_boolean_inv_appl: ∀W,U,b0,b,F. {b}⇕ F = {b0}@W.U →
                           ∃∃b1,V,T. b = b0 & {b}⇕V = W & {b}⇕T = U & F = {b1}@V.T.
#W #U #b0 #b #F #H
elim (boolean_inv_appl … H) -H #D #C #H0 #H1 #H2 #H
elim (carrier_inv_appl … H) -H #b1 #W1 #U1 #H3 #H4 destruct /2 width=6/
qed-.
