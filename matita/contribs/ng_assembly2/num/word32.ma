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

(* ***** *)
(* DWORD *)
(* ***** *)

ndefinition word32 ≝ comp_num word16.
ndefinition mk_word32 ≝ λw1,w2.mk_comp_num word16 w1 w2.

(* \langle \rangle *)
notation "〈x.y〉" non associative with precedence 80
 for @{ mk_comp_num word16 $x $y }.

ndefinition word32_is_comparable ≝ cn_is_comparable word16_is_comparable.
ndefinition word32_is_comparable_ext ≝ cn_is_comparable_ext word16_is_comparable_ext.
unification hint 0 ≔ ⊢ carr (comp_base word32_is_comparable_ext) ≡ comp_num (comp_num (comp_num exadecim)).
unification hint 0 ≔ ⊢ carr (comp_base word32_is_comparable_ext) ≡ comp_num (comp_num byte8).
unification hint 0 ≔ ⊢ carr (comp_base word32_is_comparable_ext) ≡ comp_num word16.
unification hint 0 ≔ ⊢ carr (comp_base word32_is_comparable_ext) ≡ word32.
unification hint 0 ≔ ⊢ carr word32_is_comparable ≡ comp_num (comp_num (comp_num exadecim)).
unification hint 0 ≔ ⊢ carr word32_is_comparable ≡ comp_num (comp_num byte8).
unification hint 0 ≔ ⊢ carr word32_is_comparable ≡ comp_num word16.
unification hint 0 ≔ ⊢ carr word32_is_comparable ≡ word32.

(* operatore estensione unsigned *)
ndefinition extu_w32 ≝ λw2.〈zeroc ?.w2〉.
ndefinition extu2_w32 ≝ λb2.〈zeroc ?.〈zeroc ?:b2〉〉.
ndefinition extu3_w32 ≝ λe2.〈zeroc ?.〈zeroc ?:〈zeroc ?,e2〉〉〉.

(* operatore estensione signed *)
ndefinition exts_w32 ≝
λw2.〈(match getMSBc ? w2 with
      [ true ⇒ predc ? (zeroc ?) | false ⇒ zeroc ? ]).w2〉.
ndefinition exts2_w32 ≝
λb2.(match getMSBc ? b2 with
      [ true ⇒ 〈predc ? (zeroc ?).〈predc ? (zeroc ?):b2〉〉
      | false ⇒ 〈zeroc ?.〈zeroc ?:b2〉〉 ]).
ndefinition exts3_w32 ≝
λe2.(match getMSBc ? e2 with
      [ true ⇒ 〈predc ? (zeroc ?).〈predc ? (zeroc ?):〈predc ? (zeroc ?),e2〉〉〉
      | false ⇒ 〈zeroc ?.〈zeroc ?:〈zeroc ?,e2〉〉〉 ]).

(* operatore moltiplicazione senza segno *)
(* 〈a1,a2〉 * 〈b1,b2〉 = (a1*b1) x0 x0 + x0 (a1*b2) x0 + x0 (a2*b1) x0 + x0 x0 (a2*b2) *)
ndefinition mulu_w16_aux ≝
λw:word32.nat_it ? (rolc ?) w nat8.

ndefinition mulu_w16 ≝
λw1,w2:word16.
 plusc_d_d ? 〈(mulu_b8 (cnH ? w1) (cnH ? w2)).zeroc ?〉
 (plusc_d_d ? (mulu_w16_aux (extu_w32 (mulu_b8 (cnH ? w1) (cnL ? w2))))
  (plusc_d_d ? (mulu_w16_aux (extu_w32 (mulu_b8 (cnL ? w1) (cnH ? w2))))
                (extu_w32 (mulu_b8 (cnL ? w1) (cnL ? w2))))).

(* operatore moltiplicazione con segno *)
(* x * y = sgn(x) * sgn(y) * |x| * |y| *)
ndefinition muls_w16 ≝
λw1,w2:word16.
(* ++/-- → +, +-/-+ → - *)
 match (getMSBc ? w1) ⊙ (getMSBc ? w2) with
  (* +- -+ → - *)
  [ true ⇒ complc ?
  (* ++/-- → + *)
  | false ⇒ λx.x ] (mulu_w16 (absc ? w1) (absc ? w2)).
