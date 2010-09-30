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

include "common/nat.ma".
include "num/word32.ma".

(* ************************ *)
(* NUMERI FINITI → NATURALI *)
(* ************************ *)

nlet rec nat_of_qu_aux n (r:rec_quatern n) on r ≝
 match r with
  [ qu_O ⇒ O
  | qu_S t n' ⇒ S (nat_of_qu_aux t n')
  ].

ndefinition nat_of_qu : quatern → nat ≝ λn.nat_of_qu_aux n (qu_to_recqu n).

nlet rec nat_of_oct_aux n (r:rec_oct n) on r ≝
 match r with
  [ oc_O ⇒ O
  | oc_S t n' ⇒ S (nat_of_oct_aux t n')
  ].

ndefinition nat_of_oct : oct → nat ≝ λn.nat_of_oct_aux n (oct_to_recoct n).

nlet rec nat_of_ex_aux n (r:rec_exadecim n) on r ≝
 match r with
  [ ex_O ⇒ O
  | ex_S t n' ⇒ S (nat_of_ex_aux t n')
  ].

ndefinition nat_of_ex : exadecim → nat ≝ λn.nat_of_ex_aux n (ex_to_recex n).

nlet rec nat_of_bit_aux n (r:rec_bitrigesim n) on r ≝
 match r with
  [ bi_O ⇒ O
  | bi_S t n' ⇒ S (nat_of_bit_aux t n')
  ].

ndefinition nat_of_bit : bitrigesim → nat ≝ λn.nat_of_bit_aux n (bit_to_recbit n).

nlet rec nat_of_b8_aux n (r:rec_byte8 n) on r ≝
 match r with
  [ b8_O ⇒ O
  | b8_S t n' ⇒ S (nat_of_b8_aux t n')
  ].

ndefinition nat_of_b8 : byte8 → nat ≝ λn:byte8.nat_of_b8_aux n (b8_to_recb8 n).

nlet rec nat_of_w16_aux n (r:rec_word16 n) on r : nat ≝
 match r with
  [ w16_O ⇒ O
  | w16_S t n' ⇒ S (nat_of_w16_aux t n')
  ].

ndefinition nat_of_w16 : word16 → nat ≝ λn:word16.nat_of_w16_aux n (w16_to_recw16 n).

ndefinition nat_of_w32 : word32 → nat ≝ λn:word32.(nat65536 * (nat_of_w16 (cnH ? n))) + (nat_of_w16 (cnL ? n)).
