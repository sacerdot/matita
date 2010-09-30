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

include "num/byte8.ma".
include "common/nat.ma".

(* **** *)
(* WORD *)
(* **** *)

ndefinition word16 ≝ comp_num byte8.
ndefinition mk_word16 ≝ λb1,b2.mk_comp_num byte8 b1 b2.

(* \langle \rangle *)
notation "〈x:y〉" non associative with precedence 80
 for @{ mk_comp_num byte8 $x $y }.

ndefinition word16_is_comparable ≝ cn_is_comparable byte8_is_comparable.
ndefinition word16_is_comparable_ext ≝ cn_is_comparable_ext byte8_is_comparable_ext.
unification hint 0 ≔ ⊢ carr (comp_base word16_is_comparable_ext) ≡ comp_num (comp_num exadecim).
unification hint 0 ≔ ⊢ carr (comp_base word16_is_comparable_ext) ≡ comp_num byte8.
unification hint 0 ≔ ⊢ carr (comp_base word16_is_comparable_ext) ≡ word16.
unification hint 0 ≔ ⊢ carr word16_is_comparable ≡ comp_num (comp_num exadecim).
unification hint 0 ≔ ⊢ carr word16_is_comparable ≡ comp_num byte8.
unification hint 0 ≔ ⊢ carr word16_is_comparable ≡ word16.

(* operatore estensione unsigned *)
ndefinition extu_w16 ≝ λb2.〈zeroc ?:b2〉.
ndefinition extu2_w16 ≝ λe2.〈zeroc ?:〈zeroc ?,e2〉〉.

(* operatore estensione signed *)
ndefinition exts_w16 ≝
λb2.〈(match getMSBc ? b2 with
      [ true ⇒ predc ? (zeroc ?) | false ⇒ zeroc ? ]):b2〉.
ndefinition exts2_w16 ≝
λe2.(match getMSBc ? e2 with
      [ true ⇒ 〈predc ? (zeroc ?):〈predc ? (zeroc ?),e2〉〉
      | false ⇒ 〈zeroc ?:〈zeroc ?,e2〉〉 ]).

(* operatore moltiplicazione senza segno *)
(* 〈a1,a2〉 * 〈b1,b2〉 = (a1*b1) x0 x0 + x0 (a1*b2) x0 + x0 (a2*b1) x0 + x0 x0 (a2*b2) *)
ndefinition mulu_b8_aux ≝
λw:word16.nat_it ? (rolc ?) w nat4.

ndefinition mulu_b8 ≝
λb1,b2:byte8.
 plusc_d_d ? 〈(mulu_ex (cnH ? b1) (cnH ? b2)):zeroc ?〉
 (plusc_d_d ? (mulu_b8_aux (extu_w16 (mulu_ex (cnH ? b1) (cnL ? b2))))
  (plusc_d_d ? (mulu_b8_aux (extu_w16 (mulu_ex (cnL ? b1) (cnH ? b2))))
               (extu_w16 (mulu_ex (cnL ? b1) (cnL ? b2))))).

(* operatore moltiplicazione con segno *)
(* x * y = sgn(x) * sgn(y) * |x| * |y| *)
ndefinition muls_b8 ≝
λb1,b2:byte8.
(* ++/-- → +, +-/-+ → - *)
 match (getMSBc ? b1) ⊙ (getMSBc ? b2) with
  (* +- -+ → - *)
  [ true ⇒ complc ?
  (* ++/-- → + *)
  | false ⇒ λx.x ] (mulu_b8 (absc ? b1) (absc ? b2)).

(* divisione senza segno (secondo la logica delle ALU): (quoziente resto) overflow *)
nlet rec div_b8_aux (divd:word16) (divs:word16) (molt:byte8) (q:byte8) (n:nat) on n ≝
 let w' ≝ plusc_d_d ? divd (complc ? divs) in
  match n with
  [ O ⇒ match lec ? divs divd with
   [ true ⇒ triple … (orc ? molt q) (cnL ? w') (⊖ (eqc ? (cnH ? w') (zeroc ?)))
   | false ⇒ triple … q (cnL ? divd) (⊖ (eqc ? (cnH ? divd) (zeroc ?))) ]
  | S n' ⇒ match lec ? divs divd with
   [ true ⇒ div_b8_aux w' (rorc ? divs) (rorc ? molt) (orc ? molt q) n'
   | false ⇒ div_b8_aux divd (rorc ? divs) (rorc ? molt) q n' ]].

ndefinition div_b8 ≝
λw:word16.λb:byte8.match eqc ? b (zeroc ?) with
(* la combinazione n/0 e' illegale, segnala solo overflow senza dare risultato *)
 [ true ⇒ triple … 〈xF,xF〉 (cnL ? w) true
 | false ⇒ match eqc ? w (zeroc ?) with
(* 0 diviso qualsiasi cosa diverso da 0 da' q=0 r=0 o=false *)
  [ true ⇒ triple … (zeroc ?) (zeroc ?) false
(* 1) e' una divisione sensata che produrra' overflow/risultato *)
(* 2) parametri: dividendo, divisore, moltiplicatore, quoziente, contatore *)
(* 3) ad ogni ciclo il divisore e il moltiplicatore vengono scalati di 1 a dx *)
(* 4) il moltiplicatore e' la quantita' aggiunta al quoziente se il divisore *)
(*    puo' essere sottratto al dividendo *) 
  | false ⇒ div_b8_aux w (nat_it ? (rolc ?) (extu_w16 b) nat7) 〈x8,x0〉 (zeroc ?) nat7 ]].

(* word16 ricorsive *)
ninductive rec_word16 : word16 → Type ≝
  w16_O : rec_word16 (zeroc ?)
| w16_S : ∀n.rec_word16 n → rec_word16 (succc ? n).

(* word16 → word16 ricorsive *)

(* EX: ancora problema di tempi ???
ndefinition w16_to_recw16_aux1_1 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈n:〈x1,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S ? (w16_S ? (w16_S ? (w16_S ? (w16_S ? (w16_S ? (w16_S ? (w16_S ? (
 w16_S ? (w16_S ? (w16_S ? (w16_S ? (w16_S ? (w16_S ? (w16_S ? (w16_S ? recw
 ))))))))))))))).
*)

ndefinition w16_to_recw16_aux1_1 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈n:〈x1,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S 〈n:〈x0,xF〉〉 (w16_S 〈n:〈x0,xE〉〉 (w16_S 〈n:〈x0,xD〉〉 (w16_S 〈n:〈x0,xC〉〉 (
 w16_S 〈n:〈x0,xB〉〉 (w16_S 〈n:〈x0,xA〉〉 (w16_S 〈n:〈x0,x9〉〉 (w16_S 〈n:〈x0,x8〉〉 (
 w16_S 〈n:〈x0,x7〉〉 (w16_S 〈n:〈x0,x6〉〉 (w16_S 〈n:〈x0,x5〉〉 (w16_S 〈n:〈x0,x4〉〉 (
 w16_S 〈n:〈x0,x3〉〉 (w16_S 〈n:〈x0,x2〉〉 (w16_S 〈n:〈x0,x1〉〉 (w16_S 〈n:〈x0,x0〉〉 recw
 ))))))))))))))).

ndefinition w16_to_recw16_aux1_2 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈n:〈x2,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S 〈n:〈x1,xF〉〉 (w16_S 〈n:〈x1,xE〉〉 (w16_S 〈n:〈x1,xD〉〉 (w16_S 〈n:〈x1,xC〉〉 (
 w16_S 〈n:〈x1,xB〉〉 (w16_S 〈n:〈x1,xA〉〉 (w16_S 〈n:〈x1,x9〉〉 (w16_S 〈n:〈x1,x8〉〉 (
 w16_S 〈n:〈x1,x7〉〉 (w16_S 〈n:〈x1,x6〉〉 (w16_S 〈n:〈x1,x5〉〉 (w16_S 〈n:〈x1,x4〉〉 (
 w16_S 〈n:〈x1,x3〉〉 (w16_S 〈n:〈x1,x2〉〉 (w16_S 〈n:〈x1,x1〉〉 (w16_S 〈n:〈x1,x0〉〉 (w16_to_recw16_aux1_1 ? recw)
 ))))))))))))))).

ndefinition w16_to_recw16_aux1_3 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈n:〈x3,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S 〈n:〈x2,xF〉〉 (w16_S 〈n:〈x2,xE〉〉 (w16_S 〈n:〈x2,xD〉〉 (w16_S 〈n:〈x2,xC〉〉 (
 w16_S 〈n:〈x2,xB〉〉 (w16_S 〈n:〈x2,xA〉〉 (w16_S 〈n:〈x2,x9〉〉 (w16_S 〈n:〈x2,x8〉〉 (
 w16_S 〈n:〈x2,x7〉〉 (w16_S 〈n:〈x2,x6〉〉 (w16_S 〈n:〈x2,x5〉〉 (w16_S 〈n:〈x2,x4〉〉 (
 w16_S 〈n:〈x2,x3〉〉 (w16_S 〈n:〈x2,x2〉〉 (w16_S 〈n:〈x2,x1〉〉 (w16_S 〈n:〈x2,x0〉〉 (w16_to_recw16_aux1_2 ? recw)
 ))))))))))))))).

ndefinition w16_to_recw16_aux1_4 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈n:〈x4,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S 〈n:〈x3,xF〉〉 (w16_S 〈n:〈x3,xE〉〉 (w16_S 〈n:〈x3,xD〉〉 (w16_S 〈n:〈x3,xC〉〉 (
 w16_S 〈n:〈x3,xB〉〉 (w16_S 〈n:〈x3,xA〉〉 (w16_S 〈n:〈x3,x9〉〉 (w16_S 〈n:〈x3,x8〉〉 (
 w16_S 〈n:〈x3,x7〉〉 (w16_S 〈n:〈x3,x6〉〉 (w16_S 〈n:〈x3,x5〉〉 (w16_S 〈n:〈x3,x4〉〉 (
 w16_S 〈n:〈x3,x3〉〉 (w16_S 〈n:〈x3,x2〉〉 (w16_S 〈n:〈x3,x1〉〉 (w16_S 〈n:〈x3,x0〉〉 (w16_to_recw16_aux1_3 ? recw)
 ))))))))))))))).

ndefinition w16_to_recw16_aux1_5 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈n:〈x5,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S 〈n:〈x4,xF〉〉 (w16_S 〈n:〈x4,xE〉〉 (w16_S 〈n:〈x4,xD〉〉 (w16_S 〈n:〈x4,xC〉〉 (
 w16_S 〈n:〈x4,xB〉〉 (w16_S 〈n:〈x4,xA〉〉 (w16_S 〈n:〈x4,x9〉〉 (w16_S 〈n:〈x4,x8〉〉 (
 w16_S 〈n:〈x4,x7〉〉 (w16_S 〈n:〈x4,x6〉〉 (w16_S 〈n:〈x4,x5〉〉 (w16_S 〈n:〈x4,x4〉〉 (
 w16_S 〈n:〈x4,x3〉〉 (w16_S 〈n:〈x4,x2〉〉 (w16_S 〈n:〈x4,x1〉〉 (w16_S 〈n:〈x4,x0〉〉 (w16_to_recw16_aux1_4 ? recw)
 ))))))))))))))).

ndefinition w16_to_recw16_aux1_6 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈n:〈x6,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S 〈n:〈x5,xF〉〉 (w16_S 〈n:〈x5,xE〉〉 (w16_S 〈n:〈x5,xD〉〉 (w16_S 〈n:〈x5,xC〉〉 (
 w16_S 〈n:〈x5,xB〉〉 (w16_S 〈n:〈x5,xA〉〉 (w16_S 〈n:〈x5,x9〉〉 (w16_S 〈n:〈x5,x8〉〉 (
 w16_S 〈n:〈x5,x7〉〉 (w16_S 〈n:〈x5,x6〉〉 (w16_S 〈n:〈x5,x5〉〉 (w16_S 〈n:〈x5,x4〉〉 (
 w16_S 〈n:〈x5,x3〉〉 (w16_S 〈n:〈x5,x2〉〉 (w16_S 〈n:〈x5,x1〉〉 (w16_S 〈n:〈x5,x0〉〉 (w16_to_recw16_aux1_5 ? recw)
 ))))))))))))))).

ndefinition w16_to_recw16_aux1_7 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈n:〈x7,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S 〈n:〈x6,xF〉〉 (w16_S 〈n:〈x6,xE〉〉 (w16_S 〈n:〈x6,xD〉〉 (w16_S 〈n:〈x6,xC〉〉 (
 w16_S 〈n:〈x6,xB〉〉 (w16_S 〈n:〈x6,xA〉〉 (w16_S 〈n:〈x6,x9〉〉 (w16_S 〈n:〈x6,x8〉〉 (
 w16_S 〈n:〈x6,x7〉〉 (w16_S 〈n:〈x6,x6〉〉 (w16_S 〈n:〈x6,x5〉〉 (w16_S 〈n:〈x6,x4〉〉 (
 w16_S 〈n:〈x6,x3〉〉 (w16_S 〈n:〈x6,x2〉〉 (w16_S 〈n:〈x6,x1〉〉 (w16_S 〈n:〈x6,x0〉〉 (w16_to_recw16_aux1_6 ? recw)
 ))))))))))))))).

ndefinition w16_to_recw16_aux1_8 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈n:〈x8,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S 〈n:〈x7,xF〉〉 (w16_S 〈n:〈x7,xE〉〉 (w16_S 〈n:〈x7,xD〉〉 (w16_S 〈n:〈x7,xC〉〉 (
 w16_S 〈n:〈x7,xB〉〉 (w16_S 〈n:〈x7,xA〉〉 (w16_S 〈n:〈x7,x9〉〉 (w16_S 〈n:〈x7,x8〉〉 (
 w16_S 〈n:〈x7,x7〉〉 (w16_S 〈n:〈x7,x6〉〉 (w16_S 〈n:〈x7,x5〉〉 (w16_S 〈n:〈x7,x4〉〉 (
 w16_S 〈n:〈x7,x3〉〉 (w16_S 〈n:〈x7,x2〉〉 (w16_S 〈n:〈x7,x1〉〉 (w16_S 〈n:〈x7,x0〉〉 (w16_to_recw16_aux1_7 ? recw)
 ))))))))))))))).

ndefinition w16_to_recw16_aux1_9 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈n:〈x9,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S 〈n:〈x8,xF〉〉 (w16_S 〈n:〈x8,xE〉〉 (w16_S 〈n:〈x8,xD〉〉 (w16_S 〈n:〈x8,xC〉〉 (
 w16_S 〈n:〈x8,xB〉〉 (w16_S 〈n:〈x8,xA〉〉 (w16_S 〈n:〈x8,x9〉〉 (w16_S 〈n:〈x8,x8〉〉 (
 w16_S 〈n:〈x8,x7〉〉 (w16_S 〈n:〈x8,x6〉〉 (w16_S 〈n:〈x8,x5〉〉 (w16_S 〈n:〈x8,x4〉〉 (
 w16_S 〈n:〈x8,x3〉〉 (w16_S 〈n:〈x8,x2〉〉 (w16_S 〈n:〈x8,x1〉〉 (w16_S 〈n:〈x8,x0〉〉 (w16_to_recw16_aux1_8 ? recw)
 ))))))))))))))).

ndefinition w16_to_recw16_aux1_10 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈n:〈xA,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S 〈n:〈x9,xF〉〉 (w16_S 〈n:〈x9,xE〉〉 (w16_S 〈n:〈x9,xD〉〉 (w16_S 〈n:〈x9,xC〉〉 (
 w16_S 〈n:〈x9,xB〉〉 (w16_S 〈n:〈x9,xA〉〉 (w16_S 〈n:〈x9,x9〉〉 (w16_S 〈n:〈x9,x8〉〉 (
 w16_S 〈n:〈x9,x7〉〉 (w16_S 〈n:〈x9,x6〉〉 (w16_S 〈n:〈x9,x5〉〉 (w16_S 〈n:〈x9,x4〉〉 (
 w16_S 〈n:〈x9,x3〉〉 (w16_S 〈n:〈x9,x2〉〉 (w16_S 〈n:〈x9,x1〉〉 (w16_S 〈n:〈x9,x0〉〉 (w16_to_recw16_aux1_9 ? recw)
 ))))))))))))))).

ndefinition w16_to_recw16_aux1_11 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈n:〈xB,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S 〈n:〈xA,xF〉〉 (w16_S 〈n:〈xA,xE〉〉 (w16_S 〈n:〈xA,xD〉〉 (w16_S 〈n:〈xA,xC〉〉 (
 w16_S 〈n:〈xA,xB〉〉 (w16_S 〈n:〈xA,xA〉〉 (w16_S 〈n:〈xA,x9〉〉 (w16_S 〈n:〈xA,x8〉〉 (
 w16_S 〈n:〈xA,x7〉〉 (w16_S 〈n:〈xA,x6〉〉 (w16_S 〈n:〈xA,x5〉〉 (w16_S 〈n:〈xA,x4〉〉 (
 w16_S 〈n:〈xA,x3〉〉 (w16_S 〈n:〈xA,x2〉〉 (w16_S 〈n:〈xA,x1〉〉 (w16_S 〈n:〈xA,x0〉〉 (w16_to_recw16_aux1_10 ? recw)
 ))))))))))))))).

ndefinition w16_to_recw16_aux1_12 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈n:〈xC,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S 〈n:〈xB,xF〉〉 (w16_S 〈n:〈xB,xE〉〉 (w16_S 〈n:〈xB,xD〉〉 (w16_S 〈n:〈xB,xC〉〉 (
 w16_S 〈n:〈xB,xB〉〉 (w16_S 〈n:〈xB,xA〉〉 (w16_S 〈n:〈xB,x9〉〉 (w16_S 〈n:〈xB,x8〉〉 (
 w16_S 〈n:〈xB,x7〉〉 (w16_S 〈n:〈xB,x6〉〉 (w16_S 〈n:〈xB,x5〉〉 (w16_S 〈n:〈xB,x4〉〉 (
 w16_S 〈n:〈xB,x3〉〉 (w16_S 〈n:〈xB,x2〉〉 (w16_S 〈n:〈xB,x1〉〉 (w16_S 〈n:〈xB,x0〉〉 (w16_to_recw16_aux1_11 ? recw)
 ))))))))))))))).

ndefinition w16_to_recw16_aux1_13 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈n:〈xD,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S 〈n:〈xC,xF〉〉 (w16_S 〈n:〈xC,xE〉〉 (w16_S 〈n:〈xC,xD〉〉 (w16_S 〈n:〈xC,xC〉〉 (
 w16_S 〈n:〈xC,xB〉〉 (w16_S 〈n:〈xC,xA〉〉 (w16_S 〈n:〈xC,x9〉〉 (w16_S 〈n:〈xC,x8〉〉 (
 w16_S 〈n:〈xC,x7〉〉 (w16_S 〈n:〈xC,x6〉〉 (w16_S 〈n:〈xC,x5〉〉 (w16_S 〈n:〈xC,x4〉〉 (
 w16_S 〈n:〈xC,x3〉〉 (w16_S 〈n:〈xC,x2〉〉 (w16_S 〈n:〈xC,x1〉〉 (w16_S 〈n:〈xC,x0〉〉 (w16_to_recw16_aux1_12 ? recw)
 ))))))))))))))).

ndefinition w16_to_recw16_aux1_14 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈n:〈xE,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S 〈n:〈xD,xF〉〉 (w16_S 〈n:〈xD,xE〉〉 (w16_S 〈n:〈xD,xD〉〉 (w16_S 〈n:〈xD,xC〉〉 (
 w16_S 〈n:〈xD,xB〉〉 (w16_S 〈n:〈xD,xA〉〉 (w16_S 〈n:〈xD,x9〉〉 (w16_S 〈n:〈xD,x8〉〉 (
 w16_S 〈n:〈xD,x7〉〉 (w16_S 〈n:〈xD,x6〉〉 (w16_S 〈n:〈xD,x5〉〉 (w16_S 〈n:〈xD,x4〉〉 (
 w16_S 〈n:〈xD,x3〉〉 (w16_S 〈n:〈xD,x2〉〉 (w16_S 〈n:〈xD,x1〉〉 (w16_S 〈n:〈xD,x0〉〉 (w16_to_recw16_aux1_13 ? recw)
 ))))))))))))))).

ndefinition w16_to_recw16_aux1_15 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈n:〈xF,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S 〈n:〈xE,xF〉〉 (w16_S 〈n:〈xE,xE〉〉 (w16_S 〈n:〈xE,xD〉〉 (w16_S 〈n:〈xE,xC〉〉 (
 w16_S 〈n:〈xE,xB〉〉 (w16_S 〈n:〈xE,xA〉〉 (w16_S 〈n:〈xE,x9〉〉 (w16_S 〈n:〈xE,x8〉〉 (
 w16_S 〈n:〈xE,x7〉〉 (w16_S 〈n:〈xE,x6〉〉 (w16_S 〈n:〈xE,x5〉〉 (w16_S 〈n:〈xE,x4〉〉 (
 w16_S 〈n:〈xE,x3〉〉 (w16_S 〈n:〈xE,x2〉〉 (w16_S 〈n:〈xE,x1〉〉 (w16_S 〈n:〈xE,x0〉〉 (w16_to_recw16_aux1_14 ? recw)
 ))))))))))))))).

ndefinition w16_to_recw16_aux1 : Πn.rec_word16 〈n:〈x0,x0〉〉 → rec_word16 〈(succc ? n):〈x0,x0〉〉 ≝
λn.λrecw:rec_word16 〈n:〈x0,x0〉〉.
 w16_S 〈n:〈xF,xF〉〉 (w16_S 〈n:〈xF,xE〉〉 (w16_S 〈n:〈xF,xD〉〉 (w16_S 〈n:〈xF,xC〉〉 (
 w16_S 〈n:〈xF,xB〉〉 (w16_S 〈n:〈xF,xA〉〉 (w16_S 〈n:〈xF,x9〉〉 (w16_S 〈n:〈xF,x8〉〉 (
 w16_S 〈n:〈xF,x7〉〉 (w16_S 〈n:〈xF,x6〉〉 (w16_S 〈n:〈xF,x5〉〉 (w16_S 〈n:〈xF,x4〉〉 (
 w16_S 〈n:〈xF,x3〉〉 (w16_S 〈n:〈xF,x2〉〉 (w16_S 〈n:〈xF,x1〉〉 (w16_S 〈n:〈xF,x0〉〉 (w16_to_recw16_aux1_15 ? recw)
 ))))))))))))))).

(* ... cifra byte superiore *)
nlet rec w16_to_recw16_aux2 (n:byte8) (r:rec_byte8 n) on r ≝
 match r return λx.λy:rec_byte8 x.rec_word16 〈x:〈x0,x0〉〉 with
  [ b8_O ⇒ w16_O
  | b8_S t n' ⇒ w16_to_recw16_aux1 ? (w16_to_recw16_aux2 t n')
  ].

(* ... cifra esadecimale n.2 *)
ndefinition w16_to_recw16_aux3 ≝
λb,n.λrecw:rec_word16 〈b:〈x0,x0〉〉.
 match n return λx.rec_word16 〈b:〈x,x0〉〉 with
 [ x0 ⇒ recw
 | x1 ⇒ w16_to_recw16_aux1_1 ? recw
 | x2 ⇒ w16_to_recw16_aux1_2 ? recw
 | x3 ⇒ w16_to_recw16_aux1_3 ? recw
 | x4 ⇒ w16_to_recw16_aux1_4 ? recw
 | x5 ⇒ w16_to_recw16_aux1_5 ? recw
 | x6 ⇒ w16_to_recw16_aux1_6 ? recw
 | x7 ⇒ w16_to_recw16_aux1_7 ? recw
 | x8 ⇒ w16_to_recw16_aux1_8 ? recw
 | x9 ⇒ w16_to_recw16_aux1_9 ? recw
 | xA ⇒ w16_to_recw16_aux1_10 ? recw
 | xB ⇒ w16_to_recw16_aux1_11 ? recw
 | xC ⇒ w16_to_recw16_aux1_12 ? recw
 | xD ⇒ w16_to_recw16_aux1_13 ? recw
 | xE ⇒ w16_to_recw16_aux1_14 ? recw
 | xF ⇒ w16_to_recw16_aux1_15 ? recw
 ].

ndefinition w16_to_recw16_aux4_1 : Πn,e.rec_word16 〈n:〈e,x0〉〉 → rec_word16 〈n:〈e,x1〉〉 ≝
λn,e.
 match e return λx.rec_word16 〈n:〈x,x0〉〉 → rec_word16 〈n:〈x,x1〉〉 with
  [ x0 ⇒ λrecw:rec_word16 〈n:〈x0,x0〉〉.w16_S ? recw
  | x1 ⇒ λrecw:rec_word16 〈n:〈x1,x0〉〉.w16_S ? recw
  | x2 ⇒ λrecw:rec_word16 〈n:〈x2,x0〉〉.w16_S ? recw
  | x3 ⇒ λrecw:rec_word16 〈n:〈x3,x0〉〉.w16_S ? recw
  | x4 ⇒ λrecw:rec_word16 〈n:〈x4,x0〉〉.w16_S ? recw
  | x5 ⇒ λrecw:rec_word16 〈n:〈x5,x0〉〉.w16_S ? recw
  | x6 ⇒ λrecw:rec_word16 〈n:〈x6,x0〉〉.w16_S ? recw
  | x7 ⇒ λrecw:rec_word16 〈n:〈x7,x0〉〉.w16_S ? recw
  | x8 ⇒ λrecw:rec_word16 〈n:〈x8,x0〉〉.w16_S ? recw
  | x9 ⇒ λrecw:rec_word16 〈n:〈x9,x0〉〉.w16_S ? recw
  | xA ⇒ λrecw:rec_word16 〈n:〈xA,x0〉〉.w16_S ? recw
  | xB ⇒ λrecw:rec_word16 〈n:〈xB,x0〉〉.w16_S ? recw
  | xC ⇒ λrecw:rec_word16 〈n:〈xC,x0〉〉.w16_S ? recw
  | xD ⇒ λrecw:rec_word16 〈n:〈xD,x0〉〉.w16_S ? recw
  | xE ⇒ λrecw:rec_word16 〈n:〈xE,x0〉〉.w16_S ? recw
  | xF ⇒ λrecw:rec_word16 〈n:〈xF,x0〉〉.w16_S ? recw
  ].

ndefinition w16_to_recw16_aux4_2 : Πn,e.rec_word16 〈n:〈e,x0〉〉 → rec_word16 〈n:〈e,x2〉〉 ≝
λn,e.
 match e return λx.rec_word16 〈n:〈x,x0〉〉 → rec_word16 〈n:〈x,x2〉〉 with
  [ x0 ⇒ λrecw:rec_word16 〈n:〈x0,x0〉〉.w16_S ? (w16_to_recw16_aux4_1 … recw)
  | x1 ⇒ λrecw:rec_word16 〈n:〈x1,x0〉〉.w16_S ? (w16_to_recw16_aux4_1 … recw)
  | x2 ⇒ λrecw:rec_word16 〈n:〈x2,x0〉〉.w16_S ? (w16_to_recw16_aux4_1 … recw)
  | x3 ⇒ λrecw:rec_word16 〈n:〈x3,x0〉〉.w16_S ? (w16_to_recw16_aux4_1 … recw)
  | x4 ⇒ λrecw:rec_word16 〈n:〈x4,x0〉〉.w16_S ? (w16_to_recw16_aux4_1 … recw)
  | x5 ⇒ λrecw:rec_word16 〈n:〈x5,x0〉〉.w16_S ? (w16_to_recw16_aux4_1 … recw)
  | x6 ⇒ λrecw:rec_word16 〈n:〈x6,x0〉〉.w16_S ? (w16_to_recw16_aux4_1 … recw)
  | x7 ⇒ λrecw:rec_word16 〈n:〈x7,x0〉〉.w16_S ? (w16_to_recw16_aux4_1 … recw)
  | x8 ⇒ λrecw:rec_word16 〈n:〈x8,x0〉〉.w16_S ? (w16_to_recw16_aux4_1 … recw)
  | x9 ⇒ λrecw:rec_word16 〈n:〈x9,x0〉〉.w16_S ? (w16_to_recw16_aux4_1 … recw)
  | xA ⇒ λrecw:rec_word16 〈n:〈xA,x0〉〉.w16_S ? (w16_to_recw16_aux4_1 … recw)
  | xB ⇒ λrecw:rec_word16 〈n:〈xB,x0〉〉.w16_S ? (w16_to_recw16_aux4_1 … recw)
  | xC ⇒ λrecw:rec_word16 〈n:〈xC,x0〉〉.w16_S ? (w16_to_recw16_aux4_1 … recw)
  | xD ⇒ λrecw:rec_word16 〈n:〈xD,x0〉〉.w16_S ? (w16_to_recw16_aux4_1 … recw)
  | xE ⇒ λrecw:rec_word16 〈n:〈xE,x0〉〉.w16_S ? (w16_to_recw16_aux4_1 … recw)
  | xF ⇒ λrecw:rec_word16 〈n:〈xF,x0〉〉.w16_S ? (w16_to_recw16_aux4_1 … recw)
  ].

ndefinition w16_to_recw16_aux4_3 : Πn,e.rec_word16 〈n:〈e,x0〉〉 → rec_word16 〈n:〈e,x3〉〉 ≝
λn,e.
 match e return λx.rec_word16 〈n:〈x,x0〉〉 → rec_word16 〈n:〈x,x3〉〉 with
  [ x0 ⇒ λrecw:rec_word16 〈n:〈x0,x0〉〉.w16_S ? (w16_to_recw16_aux4_2 … recw)
  | x1 ⇒ λrecw:rec_word16 〈n:〈x1,x0〉〉.w16_S ? (w16_to_recw16_aux4_2 … recw)
  | x2 ⇒ λrecw:rec_word16 〈n:〈x2,x0〉〉.w16_S ? (w16_to_recw16_aux4_2 … recw)
  | x3 ⇒ λrecw:rec_word16 〈n:〈x3,x0〉〉.w16_S ? (w16_to_recw16_aux4_2 … recw)
  | x4 ⇒ λrecw:rec_word16 〈n:〈x4,x0〉〉.w16_S ? (w16_to_recw16_aux4_2 … recw)
  | x5 ⇒ λrecw:rec_word16 〈n:〈x5,x0〉〉.w16_S ? (w16_to_recw16_aux4_2 … recw)
  | x6 ⇒ λrecw:rec_word16 〈n:〈x6,x0〉〉.w16_S ? (w16_to_recw16_aux4_2 … recw)
  | x7 ⇒ λrecw:rec_word16 〈n:〈x7,x0〉〉.w16_S ? (w16_to_recw16_aux4_2 … recw)
  | x8 ⇒ λrecw:rec_word16 〈n:〈x8,x0〉〉.w16_S ? (w16_to_recw16_aux4_2 … recw)
  | x9 ⇒ λrecw:rec_word16 〈n:〈x9,x0〉〉.w16_S ? (w16_to_recw16_aux4_2 … recw)
  | xA ⇒ λrecw:rec_word16 〈n:〈xA,x0〉〉.w16_S ? (w16_to_recw16_aux4_2 … recw)
  | xB ⇒ λrecw:rec_word16 〈n:〈xB,x0〉〉.w16_S ? (w16_to_recw16_aux4_2 … recw)
  | xC ⇒ λrecw:rec_word16 〈n:〈xC,x0〉〉.w16_S ? (w16_to_recw16_aux4_2 … recw)
  | xD ⇒ λrecw:rec_word16 〈n:〈xD,x0〉〉.w16_S ? (w16_to_recw16_aux4_2 … recw)
  | xE ⇒ λrecw:rec_word16 〈n:〈xE,x0〉〉.w16_S ? (w16_to_recw16_aux4_2 … recw)
  | xF ⇒ λrecw:rec_word16 〈n:〈xF,x0〉〉.w16_S ? (w16_to_recw16_aux4_2 … recw)
  ].

ndefinition w16_to_recw16_aux4_4 : Πn,e.rec_word16 〈n:〈e,x0〉〉 → rec_word16 〈n:〈e,x4〉〉 ≝
λn,e.
 match e return λx.rec_word16 〈n:〈x,x0〉〉 → rec_word16 〈n:〈x,x4〉〉 with
  [ x0 ⇒ λrecw:rec_word16 〈n:〈x0,x0〉〉.w16_S ? (w16_to_recw16_aux4_3 … recw)
  | x1 ⇒ λrecw:rec_word16 〈n:〈x1,x0〉〉.w16_S ? (w16_to_recw16_aux4_3 … recw)
  | x2 ⇒ λrecw:rec_word16 〈n:〈x2,x0〉〉.w16_S ? (w16_to_recw16_aux4_3 … recw)
  | x3 ⇒ λrecw:rec_word16 〈n:〈x3,x0〉〉.w16_S ? (w16_to_recw16_aux4_3 … recw)
  | x4 ⇒ λrecw:rec_word16 〈n:〈x4,x0〉〉.w16_S ? (w16_to_recw16_aux4_3 … recw)
  | x5 ⇒ λrecw:rec_word16 〈n:〈x5,x0〉〉.w16_S ? (w16_to_recw16_aux4_3 … recw)
  | x6 ⇒ λrecw:rec_word16 〈n:〈x6,x0〉〉.w16_S ? (w16_to_recw16_aux4_3 … recw)
  | x7 ⇒ λrecw:rec_word16 〈n:〈x7,x0〉〉.w16_S ? (w16_to_recw16_aux4_3 … recw)
  | x8 ⇒ λrecw:rec_word16 〈n:〈x8,x0〉〉.w16_S ? (w16_to_recw16_aux4_3 … recw)
  | x9 ⇒ λrecw:rec_word16 〈n:〈x9,x0〉〉.w16_S ? (w16_to_recw16_aux4_3 … recw)
  | xA ⇒ λrecw:rec_word16 〈n:〈xA,x0〉〉.w16_S ? (w16_to_recw16_aux4_3 … recw)
  | xB ⇒ λrecw:rec_word16 〈n:〈xB,x0〉〉.w16_S ? (w16_to_recw16_aux4_3 … recw)
  | xC ⇒ λrecw:rec_word16 〈n:〈xC,x0〉〉.w16_S ? (w16_to_recw16_aux4_3 … recw)
  | xD ⇒ λrecw:rec_word16 〈n:〈xD,x0〉〉.w16_S ? (w16_to_recw16_aux4_3 … recw)
  | xE ⇒ λrecw:rec_word16 〈n:〈xE,x0〉〉.w16_S ? (w16_to_recw16_aux4_3 … recw)
  | xF ⇒ λrecw:rec_word16 〈n:〈xF,x0〉〉.w16_S ? (w16_to_recw16_aux4_3 … recw)
  ].

ndefinition w16_to_recw16_aux4_5 : Πn,e.rec_word16 〈n:〈e,x0〉〉 → rec_word16 〈n:〈e,x5〉〉 ≝
λn,e.
 match e return λx.rec_word16 〈n:〈x,x0〉〉 → rec_word16 〈n:〈x,x5〉〉 with
  [ x0 ⇒ λrecw:rec_word16 〈n:〈x0,x0〉〉.w16_S ? (w16_to_recw16_aux4_4 … recw)
  | x1 ⇒ λrecw:rec_word16 〈n:〈x1,x0〉〉.w16_S ? (w16_to_recw16_aux4_4 … recw)
  | x2 ⇒ λrecw:rec_word16 〈n:〈x2,x0〉〉.w16_S ? (w16_to_recw16_aux4_4 … recw)
  | x3 ⇒ λrecw:rec_word16 〈n:〈x3,x0〉〉.w16_S ? (w16_to_recw16_aux4_4 … recw)
  | x4 ⇒ λrecw:rec_word16 〈n:〈x4,x0〉〉.w16_S ? (w16_to_recw16_aux4_4 … recw)
  | x5 ⇒ λrecw:rec_word16 〈n:〈x5,x0〉〉.w16_S ? (w16_to_recw16_aux4_4 … recw)
  | x6 ⇒ λrecw:rec_word16 〈n:〈x6,x0〉〉.w16_S ? (w16_to_recw16_aux4_4 … recw)
  | x7 ⇒ λrecw:rec_word16 〈n:〈x7,x0〉〉.w16_S ? (w16_to_recw16_aux4_4 … recw)
  | x8 ⇒ λrecw:rec_word16 〈n:〈x8,x0〉〉.w16_S ? (w16_to_recw16_aux4_4 … recw)
  | x9 ⇒ λrecw:rec_word16 〈n:〈x9,x0〉〉.w16_S ? (w16_to_recw16_aux4_4 … recw)
  | xA ⇒ λrecw:rec_word16 〈n:〈xA,x0〉〉.w16_S ? (w16_to_recw16_aux4_4 … recw)
  | xB ⇒ λrecw:rec_word16 〈n:〈xB,x0〉〉.w16_S ? (w16_to_recw16_aux4_4 … recw)
  | xC ⇒ λrecw:rec_word16 〈n:〈xC,x0〉〉.w16_S ? (w16_to_recw16_aux4_4 … recw)
  | xD ⇒ λrecw:rec_word16 〈n:〈xD,x0〉〉.w16_S ? (w16_to_recw16_aux4_4 … recw)
  | xE ⇒ λrecw:rec_word16 〈n:〈xE,x0〉〉.w16_S ? (w16_to_recw16_aux4_4 … recw)
  | xF ⇒ λrecw:rec_word16 〈n:〈xF,x0〉〉.w16_S ? (w16_to_recw16_aux4_4 … recw)
  ].

ndefinition w16_to_recw16_aux4_6 : Πn,e.rec_word16 〈n:〈e,x0〉〉 → rec_word16 〈n:〈e,x6〉〉 ≝
λn,e.
 match e return λx.rec_word16 〈n:〈x,x0〉〉 → rec_word16 〈n:〈x,x6〉〉 with
  [ x0 ⇒ λrecw:rec_word16 〈n:〈x0,x0〉〉.w16_S ? (w16_to_recw16_aux4_5 … recw)
  | x1 ⇒ λrecw:rec_word16 〈n:〈x1,x0〉〉.w16_S ? (w16_to_recw16_aux4_5 … recw)
  | x2 ⇒ λrecw:rec_word16 〈n:〈x2,x0〉〉.w16_S ? (w16_to_recw16_aux4_5 … recw)
  | x3 ⇒ λrecw:rec_word16 〈n:〈x3,x0〉〉.w16_S ? (w16_to_recw16_aux4_5 … recw)
  | x4 ⇒ λrecw:rec_word16 〈n:〈x4,x0〉〉.w16_S ? (w16_to_recw16_aux4_5 … recw)
  | x5 ⇒ λrecw:rec_word16 〈n:〈x5,x0〉〉.w16_S ? (w16_to_recw16_aux4_5 … recw)
  | x6 ⇒ λrecw:rec_word16 〈n:〈x6,x0〉〉.w16_S ? (w16_to_recw16_aux4_5 … recw)
  | x7 ⇒ λrecw:rec_word16 〈n:〈x7,x0〉〉.w16_S ? (w16_to_recw16_aux4_5 … recw)
  | x8 ⇒ λrecw:rec_word16 〈n:〈x8,x0〉〉.w16_S ? (w16_to_recw16_aux4_5 … recw)
  | x9 ⇒ λrecw:rec_word16 〈n:〈x9,x0〉〉.w16_S ? (w16_to_recw16_aux4_5 … recw)
  | xA ⇒ λrecw:rec_word16 〈n:〈xA,x0〉〉.w16_S ? (w16_to_recw16_aux4_5 … recw)
  | xB ⇒ λrecw:rec_word16 〈n:〈xB,x0〉〉.w16_S ? (w16_to_recw16_aux4_5 … recw)
  | xC ⇒ λrecw:rec_word16 〈n:〈xC,x0〉〉.w16_S ? (w16_to_recw16_aux4_5 … recw)
  | xD ⇒ λrecw:rec_word16 〈n:〈xD,x0〉〉.w16_S ? (w16_to_recw16_aux4_5 … recw)
  | xE ⇒ λrecw:rec_word16 〈n:〈xE,x0〉〉.w16_S ? (w16_to_recw16_aux4_5 … recw)
  | xF ⇒ λrecw:rec_word16 〈n:〈xF,x0〉〉.w16_S ? (w16_to_recw16_aux4_5 … recw)
  ].

ndefinition w16_to_recw16_aux4_7 : Πn,e.rec_word16 〈n:〈e,x0〉〉 → rec_word16 〈n:〈e,x7〉〉 ≝
λn,e.
 match e return λx.rec_word16 〈n:〈x,x0〉〉 → rec_word16 〈n:〈x,x7〉〉 with
  [ x0 ⇒ λrecw:rec_word16 〈n:〈x0,x0〉〉.w16_S ? (w16_to_recw16_aux4_6 … recw)
  | x1 ⇒ λrecw:rec_word16 〈n:〈x1,x0〉〉.w16_S ? (w16_to_recw16_aux4_6 … recw)
  | x2 ⇒ λrecw:rec_word16 〈n:〈x2,x0〉〉.w16_S ? (w16_to_recw16_aux4_6 … recw)
  | x3 ⇒ λrecw:rec_word16 〈n:〈x3,x0〉〉.w16_S ? (w16_to_recw16_aux4_6 … recw)
  | x4 ⇒ λrecw:rec_word16 〈n:〈x4,x0〉〉.w16_S ? (w16_to_recw16_aux4_6 … recw)
  | x5 ⇒ λrecw:rec_word16 〈n:〈x5,x0〉〉.w16_S ? (w16_to_recw16_aux4_6 … recw)
  | x6 ⇒ λrecw:rec_word16 〈n:〈x6,x0〉〉.w16_S ? (w16_to_recw16_aux4_6 … recw)
  | x7 ⇒ λrecw:rec_word16 〈n:〈x7,x0〉〉.w16_S ? (w16_to_recw16_aux4_6 … recw)
  | x8 ⇒ λrecw:rec_word16 〈n:〈x8,x0〉〉.w16_S ? (w16_to_recw16_aux4_6 … recw)
  | x9 ⇒ λrecw:rec_word16 〈n:〈x9,x0〉〉.w16_S ? (w16_to_recw16_aux4_6 … recw)
  | xA ⇒ λrecw:rec_word16 〈n:〈xA,x0〉〉.w16_S ? (w16_to_recw16_aux4_6 … recw)
  | xB ⇒ λrecw:rec_word16 〈n:〈xB,x0〉〉.w16_S ? (w16_to_recw16_aux4_6 … recw)
  | xC ⇒ λrecw:rec_word16 〈n:〈xC,x0〉〉.w16_S ? (w16_to_recw16_aux4_6 … recw)
  | xD ⇒ λrecw:rec_word16 〈n:〈xD,x0〉〉.w16_S ? (w16_to_recw16_aux4_6 … recw)
  | xE ⇒ λrecw:rec_word16 〈n:〈xE,x0〉〉.w16_S ? (w16_to_recw16_aux4_6 … recw)
  | xF ⇒ λrecw:rec_word16 〈n:〈xF,x0〉〉.w16_S ? (w16_to_recw16_aux4_6 … recw)
  ].

ndefinition w16_to_recw16_aux4_8 : Πn,e.rec_word16 〈n:〈e,x0〉〉 → rec_word16 〈n:〈e,x8〉〉 ≝
λn,e.
 match e return λx.rec_word16 〈n:〈x,x0〉〉 → rec_word16 〈n:〈x,x8〉〉 with
  [ x0 ⇒ λrecw:rec_word16 〈n:〈x0,x0〉〉.w16_S ? (w16_to_recw16_aux4_7 … recw)
  | x1 ⇒ λrecw:rec_word16 〈n:〈x1,x0〉〉.w16_S ? (w16_to_recw16_aux4_7 … recw)
  | x2 ⇒ λrecw:rec_word16 〈n:〈x2,x0〉〉.w16_S ? (w16_to_recw16_aux4_7 … recw)
  | x3 ⇒ λrecw:rec_word16 〈n:〈x3,x0〉〉.w16_S ? (w16_to_recw16_aux4_7 … recw)
  | x4 ⇒ λrecw:rec_word16 〈n:〈x4,x0〉〉.w16_S ? (w16_to_recw16_aux4_7 … recw)
  | x5 ⇒ λrecw:rec_word16 〈n:〈x5,x0〉〉.w16_S ? (w16_to_recw16_aux4_7 … recw)
  | x6 ⇒ λrecw:rec_word16 〈n:〈x6,x0〉〉.w16_S ? (w16_to_recw16_aux4_7 … recw)
  | x7 ⇒ λrecw:rec_word16 〈n:〈x7,x0〉〉.w16_S ? (w16_to_recw16_aux4_7 … recw)
  | x8 ⇒ λrecw:rec_word16 〈n:〈x8,x0〉〉.w16_S ? (w16_to_recw16_aux4_7 … recw)
  | x9 ⇒ λrecw:rec_word16 〈n:〈x9,x0〉〉.w16_S ? (w16_to_recw16_aux4_7 … recw)
  | xA ⇒ λrecw:rec_word16 〈n:〈xA,x0〉〉.w16_S ? (w16_to_recw16_aux4_7 … recw)
  | xB ⇒ λrecw:rec_word16 〈n:〈xB,x0〉〉.w16_S ? (w16_to_recw16_aux4_7 … recw)
  | xC ⇒ λrecw:rec_word16 〈n:〈xC,x0〉〉.w16_S ? (w16_to_recw16_aux4_7 … recw)
  | xD ⇒ λrecw:rec_word16 〈n:〈xD,x0〉〉.w16_S ? (w16_to_recw16_aux4_7 … recw)
  | xE ⇒ λrecw:rec_word16 〈n:〈xE,x0〉〉.w16_S ? (w16_to_recw16_aux4_7 … recw)
  | xF ⇒ λrecw:rec_word16 〈n:〈xF,x0〉〉.w16_S ? (w16_to_recw16_aux4_7 … recw)
  ].

ndefinition w16_to_recw16_aux4_9 : Πn,e.rec_word16 〈n:〈e,x0〉〉 → rec_word16 〈n:〈e,x9〉〉 ≝
λn,e.
 match e return λx.rec_word16 〈n:〈x,x0〉〉 → rec_word16 〈n:〈x,x9〉〉 with
  [ x0 ⇒ λrecw:rec_word16 〈n:〈x0,x0〉〉.w16_S ? (w16_to_recw16_aux4_8 … recw)
  | x1 ⇒ λrecw:rec_word16 〈n:〈x1,x0〉〉.w16_S ? (w16_to_recw16_aux4_8 … recw)
  | x2 ⇒ λrecw:rec_word16 〈n:〈x2,x0〉〉.w16_S ? (w16_to_recw16_aux4_8 … recw)
  | x3 ⇒ λrecw:rec_word16 〈n:〈x3,x0〉〉.w16_S ? (w16_to_recw16_aux4_8 … recw)
  | x4 ⇒ λrecw:rec_word16 〈n:〈x4,x0〉〉.w16_S ? (w16_to_recw16_aux4_8 … recw)
  | x5 ⇒ λrecw:rec_word16 〈n:〈x5,x0〉〉.w16_S ? (w16_to_recw16_aux4_8 … recw)
  | x6 ⇒ λrecw:rec_word16 〈n:〈x6,x0〉〉.w16_S ? (w16_to_recw16_aux4_8 … recw)
  | x7 ⇒ λrecw:rec_word16 〈n:〈x7,x0〉〉.w16_S ? (w16_to_recw16_aux4_8 … recw)
  | x8 ⇒ λrecw:rec_word16 〈n:〈x8,x0〉〉.w16_S ? (w16_to_recw16_aux4_8 … recw)
  | x9 ⇒ λrecw:rec_word16 〈n:〈x9,x0〉〉.w16_S ? (w16_to_recw16_aux4_8 … recw)
  | xA ⇒ λrecw:rec_word16 〈n:〈xA,x0〉〉.w16_S ? (w16_to_recw16_aux4_8 … recw)
  | xB ⇒ λrecw:rec_word16 〈n:〈xB,x0〉〉.w16_S ? (w16_to_recw16_aux4_8 … recw)
  | xC ⇒ λrecw:rec_word16 〈n:〈xC,x0〉〉.w16_S ? (w16_to_recw16_aux4_8 … recw)
  | xD ⇒ λrecw:rec_word16 〈n:〈xD,x0〉〉.w16_S ? (w16_to_recw16_aux4_8 … recw)
  | xE ⇒ λrecw:rec_word16 〈n:〈xE,x0〉〉.w16_S ? (w16_to_recw16_aux4_8 … recw)
  | xF ⇒ λrecw:rec_word16 〈n:〈xF,x0〉〉.w16_S ? (w16_to_recw16_aux4_8 … recw)
  ].

ndefinition w16_to_recw16_aux4_10 : Πn,e.rec_word16 〈n:〈e,x0〉〉 → rec_word16 〈n:〈e,xA〉〉 ≝
λn,e.
 match e return λx.rec_word16 〈n:〈x,x0〉〉 → rec_word16 〈n:〈x,xA〉〉 with
  [ x0 ⇒ λrecw:rec_word16 〈n:〈x0,x0〉〉.w16_S ? (w16_to_recw16_aux4_9 … recw)
  | x1 ⇒ λrecw:rec_word16 〈n:〈x1,x0〉〉.w16_S ? (w16_to_recw16_aux4_9 … recw)
  | x2 ⇒ λrecw:rec_word16 〈n:〈x2,x0〉〉.w16_S ? (w16_to_recw16_aux4_9 … recw)
  | x3 ⇒ λrecw:rec_word16 〈n:〈x3,x0〉〉.w16_S ? (w16_to_recw16_aux4_9 … recw)
  | x4 ⇒ λrecw:rec_word16 〈n:〈x4,x0〉〉.w16_S ? (w16_to_recw16_aux4_9 … recw)
  | x5 ⇒ λrecw:rec_word16 〈n:〈x5,x0〉〉.w16_S ? (w16_to_recw16_aux4_9 … recw)
  | x6 ⇒ λrecw:rec_word16 〈n:〈x6,x0〉〉.w16_S ? (w16_to_recw16_aux4_9 … recw)
  | x7 ⇒ λrecw:rec_word16 〈n:〈x7,x0〉〉.w16_S ? (w16_to_recw16_aux4_9 … recw)
  | x8 ⇒ λrecw:rec_word16 〈n:〈x8,x0〉〉.w16_S ? (w16_to_recw16_aux4_9 … recw)
  | x9 ⇒ λrecw:rec_word16 〈n:〈x9,x0〉〉.w16_S ? (w16_to_recw16_aux4_9 … recw)
  | xA ⇒ λrecw:rec_word16 〈n:〈xA,x0〉〉.w16_S ? (w16_to_recw16_aux4_9 … recw)
  | xB ⇒ λrecw:rec_word16 〈n:〈xB,x0〉〉.w16_S ? (w16_to_recw16_aux4_9 … recw)
  | xC ⇒ λrecw:rec_word16 〈n:〈xC,x0〉〉.w16_S ? (w16_to_recw16_aux4_9 … recw)
  | xD ⇒ λrecw:rec_word16 〈n:〈xD,x0〉〉.w16_S ? (w16_to_recw16_aux4_9 … recw)
  | xE ⇒ λrecw:rec_word16 〈n:〈xE,x0〉〉.w16_S ? (w16_to_recw16_aux4_9 … recw)
  | xF ⇒ λrecw:rec_word16 〈n:〈xF,x0〉〉.w16_S ? (w16_to_recw16_aux4_9 … recw)
  ].

ndefinition w16_to_recw16_aux4_11 : Πn,e.rec_word16 〈n:〈e,x0〉〉 → rec_word16 〈n:〈e,xB〉〉 ≝
λn,e.
 match e return λx.rec_word16 〈n:〈x,x0〉〉 → rec_word16 〈n:〈x,xB〉〉 with
  [ x0 ⇒ λrecw:rec_word16 〈n:〈x0,x0〉〉.w16_S ? (w16_to_recw16_aux4_10 … recw)
  | x1 ⇒ λrecw:rec_word16 〈n:〈x1,x0〉〉.w16_S ? (w16_to_recw16_aux4_10 … recw)
  | x2 ⇒ λrecw:rec_word16 〈n:〈x2,x0〉〉.w16_S ? (w16_to_recw16_aux4_10 … recw)
  | x3 ⇒ λrecw:rec_word16 〈n:〈x3,x0〉〉.w16_S ? (w16_to_recw16_aux4_10 … recw)
  | x4 ⇒ λrecw:rec_word16 〈n:〈x4,x0〉〉.w16_S ? (w16_to_recw16_aux4_10 … recw)
  | x5 ⇒ λrecw:rec_word16 〈n:〈x5,x0〉〉.w16_S ? (w16_to_recw16_aux4_10 … recw)
  | x6 ⇒ λrecw:rec_word16 〈n:〈x6,x0〉〉.w16_S ? (w16_to_recw16_aux4_10 … recw)
  | x7 ⇒ λrecw:rec_word16 〈n:〈x7,x0〉〉.w16_S ? (w16_to_recw16_aux4_10 … recw)
  | x8 ⇒ λrecw:rec_word16 〈n:〈x8,x0〉〉.w16_S ? (w16_to_recw16_aux4_10 … recw)
  | x9 ⇒ λrecw:rec_word16 〈n:〈x9,x0〉〉.w16_S ? (w16_to_recw16_aux4_10 … recw)
  | xA ⇒ λrecw:rec_word16 〈n:〈xA,x0〉〉.w16_S ? (w16_to_recw16_aux4_10 … recw)
  | xB ⇒ λrecw:rec_word16 〈n:〈xB,x0〉〉.w16_S ? (w16_to_recw16_aux4_10 … recw)
  | xC ⇒ λrecw:rec_word16 〈n:〈xC,x0〉〉.w16_S ? (w16_to_recw16_aux4_10 … recw)
  | xD ⇒ λrecw:rec_word16 〈n:〈xD,x0〉〉.w16_S ? (w16_to_recw16_aux4_10 … recw)
  | xE ⇒ λrecw:rec_word16 〈n:〈xE,x0〉〉.w16_S ? (w16_to_recw16_aux4_10 … recw)
  | xF ⇒ λrecw:rec_word16 〈n:〈xF,x0〉〉.w16_S ? (w16_to_recw16_aux4_10 … recw)
  ].

ndefinition w16_to_recw16_aux4_12 : Πn,e.rec_word16 〈n:〈e,x0〉〉 → rec_word16 〈n:〈e,xC〉〉 ≝
λn,e.
 match e return λx.rec_word16 〈n:〈x,x0〉〉 → rec_word16 〈n:〈x,xC〉〉 with
  [ x0 ⇒ λrecw:rec_word16 〈n:〈x0,x0〉〉.w16_S ? (w16_to_recw16_aux4_11 … recw)
  | x1 ⇒ λrecw:rec_word16 〈n:〈x1,x0〉〉.w16_S ? (w16_to_recw16_aux4_11 … recw)
  | x2 ⇒ λrecw:rec_word16 〈n:〈x2,x0〉〉.w16_S ? (w16_to_recw16_aux4_11 … recw)
  | x3 ⇒ λrecw:rec_word16 〈n:〈x3,x0〉〉.w16_S ? (w16_to_recw16_aux4_11 … recw)
  | x4 ⇒ λrecw:rec_word16 〈n:〈x4,x0〉〉.w16_S ? (w16_to_recw16_aux4_11 … recw)
  | x5 ⇒ λrecw:rec_word16 〈n:〈x5,x0〉〉.w16_S ? (w16_to_recw16_aux4_11 … recw)
  | x6 ⇒ λrecw:rec_word16 〈n:〈x6,x0〉〉.w16_S ? (w16_to_recw16_aux4_11 … recw)
  | x7 ⇒ λrecw:rec_word16 〈n:〈x7,x0〉〉.w16_S ? (w16_to_recw16_aux4_11 … recw)
  | x8 ⇒ λrecw:rec_word16 〈n:〈x8,x0〉〉.w16_S ? (w16_to_recw16_aux4_11 … recw)
  | x9 ⇒ λrecw:rec_word16 〈n:〈x9,x0〉〉.w16_S ? (w16_to_recw16_aux4_11 … recw)
  | xA ⇒ λrecw:rec_word16 〈n:〈xA,x0〉〉.w16_S ? (w16_to_recw16_aux4_11 … recw)
  | xB ⇒ λrecw:rec_word16 〈n:〈xB,x0〉〉.w16_S ? (w16_to_recw16_aux4_11 … recw)
  | xC ⇒ λrecw:rec_word16 〈n:〈xC,x0〉〉.w16_S ? (w16_to_recw16_aux4_11 … recw)
  | xD ⇒ λrecw:rec_word16 〈n:〈xD,x0〉〉.w16_S ? (w16_to_recw16_aux4_11 … recw)
  | xE ⇒ λrecw:rec_word16 〈n:〈xE,x0〉〉.w16_S ? (w16_to_recw16_aux4_11 … recw)
  | xF ⇒ λrecw:rec_word16 〈n:〈xF,x0〉〉.w16_S ? (w16_to_recw16_aux4_11 … recw)
  ].

ndefinition w16_to_recw16_aux4_13 : Πn,e.rec_word16 〈n:〈e,x0〉〉 → rec_word16 〈n:〈e,xD〉〉 ≝
λn,e.
 match e return λx.rec_word16 〈n:〈x,x0〉〉 → rec_word16 〈n:〈x,xD〉〉 with
  [ x0 ⇒ λrecw:rec_word16 〈n:〈x0,x0〉〉.w16_S ? (w16_to_recw16_aux4_12 … recw)
  | x1 ⇒ λrecw:rec_word16 〈n:〈x1,x0〉〉.w16_S ? (w16_to_recw16_aux4_12 … recw)
  | x2 ⇒ λrecw:rec_word16 〈n:〈x2,x0〉〉.w16_S ? (w16_to_recw16_aux4_12 … recw)
  | x3 ⇒ λrecw:rec_word16 〈n:〈x3,x0〉〉.w16_S ? (w16_to_recw16_aux4_12 … recw)
  | x4 ⇒ λrecw:rec_word16 〈n:〈x4,x0〉〉.w16_S ? (w16_to_recw16_aux4_12 … recw)
  | x5 ⇒ λrecw:rec_word16 〈n:〈x5,x0〉〉.w16_S ? (w16_to_recw16_aux4_12 … recw)
  | x6 ⇒ λrecw:rec_word16 〈n:〈x6,x0〉〉.w16_S ? (w16_to_recw16_aux4_12 … recw)
  | x7 ⇒ λrecw:rec_word16 〈n:〈x7,x0〉〉.w16_S ? (w16_to_recw16_aux4_12 … recw)
  | x8 ⇒ λrecw:rec_word16 〈n:〈x8,x0〉〉.w16_S ? (w16_to_recw16_aux4_12 … recw)
  | x9 ⇒ λrecw:rec_word16 〈n:〈x9,x0〉〉.w16_S ? (w16_to_recw16_aux4_12 … recw)
  | xA ⇒ λrecw:rec_word16 〈n:〈xA,x0〉〉.w16_S ? (w16_to_recw16_aux4_12 … recw)
  | xB ⇒ λrecw:rec_word16 〈n:〈xB,x0〉〉.w16_S ? (w16_to_recw16_aux4_12 … recw)
  | xC ⇒ λrecw:rec_word16 〈n:〈xC,x0〉〉.w16_S ? (w16_to_recw16_aux4_12 … recw)
  | xD ⇒ λrecw:rec_word16 〈n:〈xD,x0〉〉.w16_S ? (w16_to_recw16_aux4_12 … recw)
  | xE ⇒ λrecw:rec_word16 〈n:〈xE,x0〉〉.w16_S ? (w16_to_recw16_aux4_12 … recw)
  | xF ⇒ λrecw:rec_word16 〈n:〈xF,x0〉〉.w16_S ? (w16_to_recw16_aux4_12 … recw)
  ].

ndefinition w16_to_recw16_aux4_14 : Πn,e.rec_word16 〈n:〈e,x0〉〉 → rec_word16 〈n:〈e,xE〉〉 ≝
λn,e.
 match e return λx.rec_word16 〈n:〈x,x0〉〉 → rec_word16 〈n:〈x,xE〉〉 with
  [ x0 ⇒ λrecw:rec_word16 〈n:〈x0,x0〉〉.w16_S ? (w16_to_recw16_aux4_13 … recw)
  | x1 ⇒ λrecw:rec_word16 〈n:〈x1,x0〉〉.w16_S ? (w16_to_recw16_aux4_13 … recw)
  | x2 ⇒ λrecw:rec_word16 〈n:〈x2,x0〉〉.w16_S ? (w16_to_recw16_aux4_13 … recw)
  | x3 ⇒ λrecw:rec_word16 〈n:〈x3,x0〉〉.w16_S ? (w16_to_recw16_aux4_13 … recw)
  | x4 ⇒ λrecw:rec_word16 〈n:〈x4,x0〉〉.w16_S ? (w16_to_recw16_aux4_13 … recw)
  | x5 ⇒ λrecw:rec_word16 〈n:〈x5,x0〉〉.w16_S ? (w16_to_recw16_aux4_13 … recw)
  | x6 ⇒ λrecw:rec_word16 〈n:〈x6,x0〉〉.w16_S ? (w16_to_recw16_aux4_13 … recw)
  | x7 ⇒ λrecw:rec_word16 〈n:〈x7,x0〉〉.w16_S ? (w16_to_recw16_aux4_13 … recw)
  | x8 ⇒ λrecw:rec_word16 〈n:〈x8,x0〉〉.w16_S ? (w16_to_recw16_aux4_13 … recw)
  | x9 ⇒ λrecw:rec_word16 〈n:〈x9,x0〉〉.w16_S ? (w16_to_recw16_aux4_13 … recw)
  | xA ⇒ λrecw:rec_word16 〈n:〈xA,x0〉〉.w16_S ? (w16_to_recw16_aux4_13 … recw)
  | xB ⇒ λrecw:rec_word16 〈n:〈xB,x0〉〉.w16_S ? (w16_to_recw16_aux4_13 … recw)
  | xC ⇒ λrecw:rec_word16 〈n:〈xC,x0〉〉.w16_S ? (w16_to_recw16_aux4_13 … recw)
  | xD ⇒ λrecw:rec_word16 〈n:〈xD,x0〉〉.w16_S ? (w16_to_recw16_aux4_13 … recw)
  | xE ⇒ λrecw:rec_word16 〈n:〈xE,x0〉〉.w16_S ? (w16_to_recw16_aux4_13 … recw)
  | xF ⇒ λrecw:rec_word16 〈n:〈xF,x0〉〉.w16_S ? (w16_to_recw16_aux4_13 … recw)
  ].

ndefinition w16_to_recw16_aux4_15 : Πn,e.rec_word16 〈n:〈e,x0〉〉 → rec_word16 〈n:〈e,xF〉〉 ≝
λn,e.
 match e return λx.rec_word16 〈n:〈x,x0〉〉 → rec_word16 〈n:〈x,xF〉〉 with
  [ x0 ⇒ λrecw:rec_word16 〈n:〈x0,x0〉〉.w16_S ? (w16_to_recw16_aux4_14 … recw)
  | x1 ⇒ λrecw:rec_word16 〈n:〈x1,x0〉〉.w16_S ? (w16_to_recw16_aux4_14 … recw)
  | x2 ⇒ λrecw:rec_word16 〈n:〈x2,x0〉〉.w16_S ? (w16_to_recw16_aux4_14 … recw)
  | x3 ⇒ λrecw:rec_word16 〈n:〈x3,x0〉〉.w16_S ? (w16_to_recw16_aux4_14 … recw)
  | x4 ⇒ λrecw:rec_word16 〈n:〈x4,x0〉〉.w16_S ? (w16_to_recw16_aux4_14 … recw)
  | x5 ⇒ λrecw:rec_word16 〈n:〈x5,x0〉〉.w16_S ? (w16_to_recw16_aux4_14 … recw)
  | x6 ⇒ λrecw:rec_word16 〈n:〈x6,x0〉〉.w16_S ? (w16_to_recw16_aux4_14 … recw)
  | x7 ⇒ λrecw:rec_word16 〈n:〈x7,x0〉〉.w16_S ? (w16_to_recw16_aux4_14 … recw)
  | x8 ⇒ λrecw:rec_word16 〈n:〈x8,x0〉〉.w16_S ? (w16_to_recw16_aux4_14 … recw)
  | x9 ⇒ λrecw:rec_word16 〈n:〈x9,x0〉〉.w16_S ? (w16_to_recw16_aux4_14 … recw)
  | xA ⇒ λrecw:rec_word16 〈n:〈xA,x0〉〉.w16_S ? (w16_to_recw16_aux4_14 … recw)
  | xB ⇒ λrecw:rec_word16 〈n:〈xB,x0〉〉.w16_S ? (w16_to_recw16_aux4_14 … recw)
  | xC ⇒ λrecw:rec_word16 〈n:〈xC,x0〉〉.w16_S ? (w16_to_recw16_aux4_14 … recw)
  | xD ⇒ λrecw:rec_word16 〈n:〈xD,x0〉〉.w16_S ? (w16_to_recw16_aux4_14 … recw)
  | xE ⇒ λrecw:rec_word16 〈n:〈xE,x0〉〉.w16_S ? (w16_to_recw16_aux4_14 … recw)
  | xF ⇒ λrecw:rec_word16 〈n:〈xF,x0〉〉.w16_S ? (w16_to_recw16_aux4_14 … recw)
  ].

(* ... cifra esadecimale n.1 *)
ndefinition w16_to_recw16_aux4 ≝
λb,e,n.λrecw:rec_word16 〈b:〈e,x0〉〉.
 match n return λx.rec_word16 〈b:〈e,x〉〉 with
 [ x0 ⇒ recw
 | x1 ⇒ w16_to_recw16_aux4_1 … recw
 | x2 ⇒ w16_to_recw16_aux4_2 … recw
 | x3 ⇒ w16_to_recw16_aux4_3 … recw
 | x4 ⇒ w16_to_recw16_aux4_4 … recw
 | x5 ⇒ w16_to_recw16_aux4_5 … recw
 | x6 ⇒ w16_to_recw16_aux4_6 … recw
 | x7 ⇒ w16_to_recw16_aux4_7 … recw
 | x8 ⇒ w16_to_recw16_aux4_8 … recw
 | x9 ⇒ w16_to_recw16_aux4_9 … recw
 | xA ⇒ w16_to_recw16_aux4_10 … recw
 | xB ⇒ w16_to_recw16_aux4_11 … recw
 | xC ⇒ w16_to_recw16_aux4_12 … recw
 | xD ⇒ w16_to_recw16_aux4_13 … recw
 | xE ⇒ w16_to_recw16_aux4_14 … recw
 | xF ⇒ w16_to_recw16_aux4_15 … recw
 ].

ndefinition w16_to_recw16 : Πw.rec_word16 w ≝
λw.
 match w with [ mk_comp_num h l ⇒
 match l with [ mk_comp_num lh ll ⇒
  w16_to_recw16_aux4 h lh ll (w16_to_recw16_aux3 h lh (w16_to_recw16_aux2 h (b8_to_recb8 h))) ]].
