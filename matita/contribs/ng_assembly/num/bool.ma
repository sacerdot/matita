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

(* ********************************************************************** *)
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "common/theory.ma".

(* ******** *)
(* BOOLEANI *)
(* ******** *)

ninductive bool : Type ≝ 
  true : bool
| false : bool.

(* operatori booleani *)

ndefinition eq_bool ≝
λb1,b2:bool.match b1 with
 [ true ⇒ match b2 with [ true ⇒ true | false ⇒ false ]
 | false ⇒ match b2 with [ true ⇒ false | false ⇒ true ]
 ].

ndefinition not_bool ≝
λb:bool.match b with [ true ⇒ false | false ⇒ true ].

ndefinition and_bool ≝
λb1,b2:bool.match b1 with
 [ true ⇒ b2 | false ⇒ false ].

ndefinition or_bool ≝
λb1,b2:bool.match b1 with
 [ true ⇒ true | false ⇒ b2 ].

ndefinition xor_bool ≝
λb1,b2:bool.match b1 with
 [ true ⇒ not_bool b2
 | false ⇒ b2 ].

(* \ominus *)
notation "hvbox(⊖ a)" non associative with precedence 36
 for @{ 'not_bool $a }.
interpretation "not_bool" 'not_bool x = (not_bool x).

(* \otimes *)
notation "hvbox(a break ⊗ b)" left associative with precedence 35
 for @{ 'and_bool $a $b }.
interpretation "and_bool" 'and_bool x y = (and_bool x y).

(* \oplus *)
notation "hvbox(a break ⊕ b)" left associative with precedence 34
 for @{ 'or_bool $a $b }.
interpretation "or_bool" 'or_bool x y = (or_bool x y).

(* \odot *)
notation "hvbox(a break ⊙ b)" left associative with precedence 33
 for @{ 'xor_bool $a $b }.
interpretation "xor_bool" 'xor_bool x y = (xor_bool x y).

ndefinition boolRelation : Type → Type ≝
λA:Type.A → A → bool.
