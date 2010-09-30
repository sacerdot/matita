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

include "num/word16.ma".

(* raggruppamento di byte e word in un tipo unico *)
ninductive byte8_or_word16 : Type ≝
  Byte: byte8  → byte8_or_word16
| Word: word16 → byte8_or_word16.

ndefinition eq_b8w16 ≝
λbw1,bw2:byte8_or_word16.
 match bw1 with
  [ Byte b1 ⇒ match bw2 with [ Byte b2 ⇒ eqc ? b1 b2 | Word _ ⇒ false ]
  | Word w1 ⇒ match bw2 with [ Byte _ ⇒ false | Word w2 ⇒ eqc ? w1 w2 ]
  ].
