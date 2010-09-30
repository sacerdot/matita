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
(*                           Progetto FreeScale                           *)
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* Questo materiale fa parte della tesi:                                  *)
(*   "Formalizzazione Interattiva dei Microcontroller a 8bit FreeScale"   *)
(*                                                                        *)
(*                    data ultima modifica 15/11/2007                     *)
(* ********************************************************************** *)

include "freescale/exadecim.ma".

(* ******************** *)
(* DEFINIZIONE DEI BYTE *)
(* ******************** *)

record byte8 : Type ≝
 {
 b8h: exadecim;
 b8l: exadecim
 }.

(* \langle \rangle *)
notation "〈x,y〉" non associative with precedence 80
 for @{ 'mk_byte8 $x $y }.
interpretation "mk_byte8" 'mk_byte8 x y = (mk_byte8 x y).

(* operatore = *)
definition eq_b8 ≝ λb1,b2:byte8.(eq_ex (b8h b1) (b8h b2)) ⊗ (eq_ex (b8l b1) (b8l b2)).

(* operatore < *)
definition lt_b8 ≝
λb1,b2:byte8.match lt_ex (b8h b1) (b8h b2) with
 [ true ⇒ true
 | false ⇒ match gt_ex (b8h b1) (b8h b2) with
  [ true ⇒ false
  | false ⇒ lt_ex (b8l b1) (b8l b2) ]].

(* operatore ≤ *)
definition le_b8 ≝ λb1,b2:byte8.(eq_b8 b1 b2) ⊕ (lt_b8 b1 b2). 

(* operatore > *)
definition gt_b8 ≝ λb1,b2:byte8.⊖ (le_b8 b1 b2).

(* operatore ≥ *)
definition ge_b8 ≝ λb1,b2:byte8.⊖ (lt_b8 b1 b2).

(* operatore and *)
definition and_b8 ≝
λb1,b2:byte8.mk_byte8 (and_ex (b8h b1) (b8h b2)) (and_ex (b8l b1) (b8l b2)).

(* operatore or *)
definition or_b8 ≝
λb1,b2:byte8.mk_byte8 (or_ex (b8h b1) (b8h b2)) (or_ex (b8l b1) (b8l b2)).

(* operatore xor *)
definition xor_b8 ≝
λb1,b2:byte8.mk_byte8 (xor_ex (b8h b1) (b8h b2)) (xor_ex (b8l b1) (b8l b2)).

(* operatore rotazione destra con carry *)
definition rcr_b8 ≝
λb:byte8.λc:bool.match rcr_ex (b8h b) c with
 [ pair bh' c' ⇒ match rcr_ex (b8l b) c' with
  [ pair bl' c'' ⇒ pair ?? (mk_byte8 bh' bl') c'' ]]. 

(* operatore shift destro *)
definition shr_b8 ≝
λb:byte8.match rcr_ex (b8h b) false with
 [ pair bh' c' ⇒ match rcr_ex (b8l b) c' with
  [ pair bl' c'' ⇒ pair ?? (mk_byte8 bh' bl') c'' ]].

(* operatore rotazione destra *)
definition ror_b8 ≝
λb:byte8.match rcr_ex (b8h b) false with
 [ pair bh' c' ⇒ match rcr_ex (b8l b) c' with
  [ pair bl' c'' ⇒ match c'' with
   [ true ⇒ mk_byte8 (or_ex x8 bh') bl'
   | false ⇒ mk_byte8 bh' bl' ]]].

(* operatore rotazione destra n-volte *)
let rec ror_b8_n (b:byte8) (n:nat) on n ≝
 match n with
  [ O ⇒ b
  | S n' ⇒ ror_b8_n (ror_b8 b) n' ].

(* operatore rotazione sinistra con carry *)
definition rcl_b8 ≝
λb:byte8.λc:bool.match rcl_ex (b8l b) c with
 [ pair bl' c' ⇒ match rcl_ex (b8h b) c' with
  [ pair bh' c'' ⇒ pair ?? (mk_byte8 bh' bl') c'' ]]. 

(* operatore shift sinistro *)
definition shl_b8 ≝
λb:byte8.match rcl_ex (b8l b) false with
 [ pair bl' c' ⇒ match rcl_ex (b8h b) c' with
  [ pair bh' c'' ⇒ pair ?? (mk_byte8 bh' bl') c'' ]].

(* operatore rotazione sinistra *)
definition rol_b8 ≝
λb:byte8.match rcl_ex (b8l b) false with
 [ pair bl' c' ⇒ match rcl_ex (b8h b) c' with
  [ pair bh' c'' ⇒ match c'' with
   [ true ⇒ mk_byte8 bh' (or_ex x1 bl')
   | false ⇒ mk_byte8 bh' bl' ]]].

(* operatore rotazione sinistra n-volte *)
let rec rol_b8_n (b:byte8) (n:nat) on n ≝
 match n with
  [ O ⇒ b
  | S n' ⇒ rol_b8_n (rol_b8 b) n' ].

(* operatore not/complemento a 1 *)
definition not_b8 ≝
λb:byte8.mk_byte8 (not_ex (b8h b)) (not_ex (b8l b)).

(* operatore somma con carry *)
definition plus_b8 ≝
λb1,b2:byte8.λc:bool.
 match plus_ex (b8l b1) (b8l b2) c with
  [ pair l c' ⇒ match plus_ex (b8h b1) (b8h b2) c' with
   [ pair h c'' ⇒ pair ?? (mk_byte8 h l) c'' ]].

(* operatore somma senza carry *)
definition plus_b8nc ≝
λb1,b2:byte8.fst ?? (plus_b8 b1 b2 false).

(* operatore carry della somma *)
definition plus_b8c ≝
λb1,b2:byte8.snd ?? (plus_b8 b1 b2 false).

(* operatore Most Significant Bit *)
definition MSB_b8 ≝ λb:byte8.eq_ex x8 (and_ex x8 (b8h b)).

(* byte → naturali *)
definition nat_of_byte8 ≝ λb:byte8.16*(b8h b) + (b8l b).

coercion nat_of_byte8.

(* naturali → byte *)
definition byte8_of_nat ≝ λn.mk_byte8 (exadecim_of_nat (n/16)) (exadecim_of_nat n).

(* operatore predecessore *)
definition pred_b8 ≝
λb:byte8.match eq_ex (b8l b) x0 with
 [ true ⇒ mk_byte8 (pred_ex (b8h b)) (pred_ex (b8l b))
 | false ⇒ mk_byte8 (b8h b) (pred_ex (b8l b)) ]. 

(* operatore successore *)
definition succ_b8 ≝
λb:byte8.match eq_ex (b8l b) xF with
 [ true ⇒ mk_byte8 (succ_ex (b8h b)) (succ_ex (b8l b))
 | false ⇒ mk_byte8 (b8h b) (succ_ex (b8l b)) ]. 

(* operatore neg/complemento a 2 *)
definition compl_b8 ≝
λb:byte8.match MSB_b8 b with
 [ true ⇒ succ_b8 (not_b8 b)
 | false ⇒ not_b8 (pred_b8 b) ].

(* operatore moltiplicazione senza segno: e*e=[0x00,0xE1] *)
definition mul_ex ≝
λe1,e2:exadecim.match e1 with
 [ x0 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉   | x1 ⇒ 〈x0,x0〉   | x2 ⇒ 〈x0,x0〉   | x3 ⇒ 〈x0,x0〉
  | x4 ⇒ 〈x0,x0〉   | x5 ⇒ 〈x0,x0〉   | x6 ⇒ 〈x0,x0〉   | x7 ⇒ 〈x0,x0〉
  | x8 ⇒ 〈x0,x0〉   | x9 ⇒ 〈x0,x0〉   | xA ⇒ 〈x0,x0〉   | xB ⇒ 〈x0,x0〉
  | xC ⇒ 〈x0,x0〉   | xD ⇒ 〈x0,x0〉   | xE ⇒ 〈x0,x0〉   | xF ⇒ 〈x0,x0〉 ]
 | x1 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉   | x1 ⇒ 〈x0,x1〉   | x2 ⇒ 〈x0,x2〉   | x3 ⇒ 〈x0,x3〉
  | x4 ⇒ 〈x0,x4〉   | x5 ⇒ 〈x0,x5〉   | x6 ⇒ 〈x0,x6〉   | x7 ⇒ 〈x0,x7〉
  | x8 ⇒ 〈x0,x8〉   | x9 ⇒ 〈x0,x9〉   | xA ⇒ 〈x0,xA〉   | xB ⇒ 〈x0,xB〉
  | xC ⇒ 〈x0,xC〉   | xD ⇒ 〈x0,xD〉   | xE ⇒ 〈x0,xE〉   | xF ⇒ 〈x0,xF〉 ]
 | x2 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉   | x1 ⇒ 〈x0,x2〉   | x2 ⇒ 〈x0,x4〉   | x3 ⇒ 〈x0,x6〉
  | x4 ⇒ 〈x0,x8〉   | x5 ⇒ 〈x0,xA〉   | x6 ⇒ 〈x0,xC〉   | x7 ⇒ 〈x0,xE〉
  | x8 ⇒ 〈x1,x0〉   | x9 ⇒ 〈x1,x2〉   | xA ⇒ 〈x1,x4〉   | xB ⇒ 〈x1,x6〉
  | xC ⇒ 〈x1,x8〉   | xD ⇒ 〈x1,xA〉   | xE ⇒ 〈x1,xC〉   | xF ⇒ 〈x1,xE〉 ]
 | x3 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉   | x1 ⇒ 〈x0,x3〉   | x2 ⇒ 〈x0,x6〉   | x3 ⇒ 〈x0,x9〉
  | x4 ⇒ 〈x0,xC〉   | x5 ⇒ 〈x0,xF〉   | x6 ⇒ 〈x1,x2〉   | x7 ⇒ 〈x1,x5〉
  | x8 ⇒ 〈x1,x8〉   | x9 ⇒ 〈x1,xB〉   | xA ⇒ 〈x1,xE〉   | xB ⇒ 〈x2,x1〉
  | xC ⇒ 〈x2,x4〉   | xD ⇒ 〈x2,x7〉   | xE ⇒ 〈x2,xA〉   | xF ⇒ 〈x2,xD〉 ]
 | x4 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉   | x1 ⇒ 〈x0,x4〉   | x2 ⇒ 〈x0,x8〉   | x3 ⇒ 〈x0,xC〉
  | x4 ⇒ 〈x1,x0〉   | x5 ⇒ 〈x1,x4〉   | x6 ⇒ 〈x1,x8〉   | x7 ⇒ 〈x1,xC〉
  | x8 ⇒ 〈x2,x0〉   | x9 ⇒ 〈x2,x4〉   | xA ⇒ 〈x2,x8〉   | xB ⇒ 〈x2,xC〉
  | xC ⇒ 〈x3,x0〉   | xD ⇒ 〈x3,x4〉   | xE ⇒ 〈x3,x8〉   | xF ⇒ 〈x3,xC〉 ]
 | x5 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉   | x1 ⇒ 〈x0,x5〉   | x2 ⇒ 〈x0,xA〉   | x3 ⇒ 〈x0,xF〉
  | x4 ⇒ 〈x1,x4〉   | x5 ⇒ 〈x1,x9〉   | x6 ⇒ 〈x1,xE〉   | x7 ⇒ 〈x2,x3〉
  | x8 ⇒ 〈x2,x8〉   | x9 ⇒ 〈x2,xD〉   | xA ⇒ 〈x3,x2〉   | xB ⇒ 〈x3,x7〉
  | xC ⇒ 〈x3,xC〉   | xD ⇒ 〈x4,x1〉   | xE ⇒ 〈x4,x6〉   | xF ⇒ 〈x4,xB〉 ]
 | x6 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉   | x1 ⇒ 〈x0,x6〉   | x2 ⇒ 〈x0,xC〉   | x3 ⇒ 〈x1,x2〉
  | x4 ⇒ 〈x1,x8〉   | x5 ⇒ 〈x1,xE〉   | x6 ⇒ 〈x2,x4〉   | x7 ⇒ 〈x2,xA〉
  | x8 ⇒ 〈x3,x0〉   | x9 ⇒ 〈x3,x6〉   | xA ⇒ 〈x3,xC〉   | xB ⇒ 〈x4,x2〉
  | xC ⇒ 〈x4,x8〉   | xD ⇒ 〈x4,xE〉   | xE ⇒ 〈x5,x4〉   | xF ⇒ 〈x5,xA〉 ]
 | x7 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉   | x1 ⇒ 〈x0,x7〉   | x2 ⇒ 〈x0,xE〉   | x3 ⇒ 〈x1,x5〉
  | x4 ⇒ 〈x1,xC〉   | x5 ⇒ 〈x2,x3〉   | x6 ⇒ 〈x2,xA〉   | x7 ⇒ 〈x3,x1〉
  | x8 ⇒ 〈x3,x8〉   | x9 ⇒ 〈x3,xF〉   | xA ⇒ 〈x4,x6〉   | xB ⇒ 〈x4,xD〉
  | xC ⇒ 〈x5,x4〉   | xD ⇒ 〈x5,xB〉   | xE ⇒ 〈x6,x2〉   | xF ⇒ 〈x6,x9〉 ]
 | x8 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉   | x1 ⇒ 〈x0,x8〉   | x2 ⇒ 〈x1,x0〉   | x3 ⇒ 〈x1,x8〉
  | x4 ⇒ 〈x2,x0〉   | x5 ⇒ 〈x2,x8〉   | x6 ⇒ 〈x3,x0〉   | x7 ⇒ 〈x3,x8〉
  | x8 ⇒ 〈x4,x0〉   | x9 ⇒ 〈x4,x8〉   | xA ⇒ 〈x5,x0〉   | xB ⇒ 〈x5,x8〉
  | xC ⇒ 〈x6,x0〉   | xD ⇒ 〈x6,x8〉   | xE ⇒ 〈x7,x0〉   | xF ⇒ 〈x7,x8〉 ]
 | x9 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉   | x1 ⇒ 〈x0,x9〉   | x2 ⇒ 〈x1,x2〉   | x3 ⇒ 〈x1,xB〉
  | x4 ⇒ 〈x2,x4〉   | x5 ⇒ 〈x2,xD〉   | x6 ⇒ 〈x3,x6〉   | x7 ⇒ 〈x3,xF〉
  | x8 ⇒ 〈x4,x8〉   | x9 ⇒ 〈x5,x1〉   | xA ⇒ 〈x5,xA〉   | xB ⇒ 〈x6,x3〉
  | xC ⇒ 〈x6,xC〉   | xD ⇒ 〈x7,x5〉   | xE ⇒ 〈x7,xE〉   | xF ⇒ 〈x8,x7〉 ]
 | xA ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉   | x1 ⇒ 〈x0,xA〉   | x2 ⇒ 〈x1,x4〉   | x3 ⇒ 〈x1,xE〉
  | x4 ⇒ 〈x2,x8〉   | x5 ⇒ 〈x3,x2〉   | x6 ⇒ 〈x3,xC〉   | x7 ⇒ 〈x4,x6〉
  | x8 ⇒ 〈x5,x0〉   | x9 ⇒ 〈x5,xA〉   | xA ⇒ 〈x6,x4〉   | xB ⇒ 〈x6,xE〉
  | xC ⇒ 〈x7,x8〉   | xD ⇒ 〈x8,x2〉   | xE ⇒ 〈x8,xC〉   | xF ⇒ 〈x9,x6〉 ]
 | xB ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉   | x1 ⇒ 〈x0,xB〉   | x2 ⇒ 〈x1,x6〉   | x3 ⇒ 〈x2,x1〉
  | x4 ⇒ 〈x2,xC〉   | x5 ⇒ 〈x3,x7〉   | x6 ⇒ 〈x4,x2〉   | x7 ⇒ 〈x4,xD〉
  | x8 ⇒ 〈x5,x8〉   | x9 ⇒ 〈x6,x3〉   | xA ⇒ 〈x6,xE〉   | xB ⇒ 〈x7,x9〉
  | xC ⇒ 〈x8,x4〉   | xD ⇒ 〈x8,xF〉   | xE ⇒ 〈x9,xA〉   | xF ⇒ 〈xA,x5〉 ]
 | xC ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉   | x1 ⇒ 〈x0,xC〉   | x2 ⇒ 〈x1,x8〉   | x3 ⇒ 〈x2,x4〉
  | x4 ⇒ 〈x3,x0〉   | x5 ⇒ 〈x3,xC〉   | x6 ⇒ 〈x4,x8〉   | x7 ⇒ 〈x5,x4〉
  | x8 ⇒ 〈x6,x0〉   | x9 ⇒ 〈x6,xC〉   | xA ⇒ 〈x7,x8〉   | xB ⇒ 〈x8,x4〉
  | xC ⇒ 〈x9,x0〉   | xD ⇒ 〈x9,xC〉   | xE ⇒ 〈xA,x8〉   | xF ⇒ 〈xB,x4〉 ]
 | xD ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉   | x1 ⇒ 〈x0,xD〉   | x2 ⇒ 〈x1,xA〉   | x3 ⇒ 〈x2,x7〉
  | x4 ⇒ 〈x3,x4〉   | x5 ⇒ 〈x4,x1〉   | x6 ⇒ 〈x4,xE〉   | x7 ⇒ 〈x5,xB〉
  | x8 ⇒ 〈x6,x8〉   | x9 ⇒ 〈x7,x5〉   | xA ⇒ 〈x8,x2〉   | xB ⇒ 〈x8,xF〉
  | xC ⇒ 〈x9,xC〉   | xD ⇒ 〈xA,x9〉   | xE ⇒ 〈xB,x6〉   | xF ⇒ 〈xC,x3〉 ]
 | xE ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉   | x1 ⇒ 〈x0,xE〉   | x2 ⇒ 〈x1,xC〉   | x3 ⇒ 〈x2,xA〉
  | x4 ⇒ 〈x3,x8〉   | x5 ⇒ 〈x4,x6〉   | x6 ⇒ 〈x5,x4〉   | x7 ⇒ 〈x6,x2〉
  | x8 ⇒ 〈x7,x0〉   | x9 ⇒ 〈x7,xE〉   | xA ⇒ 〈x8,xC〉   | xB ⇒ 〈x9,xA〉
  | xC ⇒ 〈xA,x8〉   | xD ⇒ 〈xB,x6〉   | xE ⇒ 〈xC,x4〉   | xF ⇒ 〈xD,x2〉 ]
 | xF ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉   | x1 ⇒ 〈x0,xF〉   | x2 ⇒ 〈x1,xE〉   | x3 ⇒ 〈x2,xD〉
  | x4 ⇒ 〈x3,xC〉   | x5 ⇒ 〈x4,xB〉   | x6 ⇒ 〈x5,xA〉   | x7 ⇒ 〈x6,x9〉
  | x8 ⇒ 〈x7,x8〉   | x9 ⇒ 〈x8,x7〉   | xA ⇒ 〈x9,x6〉   | xB ⇒ 〈xA,x5〉
  | xC ⇒ 〈xB,x4〉   | xD ⇒ 〈xC,x3〉   | xE ⇒ 〈xD,x2〉   | xF ⇒ 〈xE,x1〉 ]
 ].

(* correzione per somma su BCD *)
(* input: halfcarry,carry,X(BCD+BCD) *)
(* output: X',carry' *)
definition daa_b8 ≝
λh,c:bool.λX:byte8.
 match lt_b8 X 〈x9,xA〉 with
  (* [X:0x00-0x99] *)
  (* c' = c *)
  (* X' = [(b16l X):0x0-0x9] X + [h=1 ? 0x06 : 0x00] + [c=1 ? 0x60 : 0x00]
          [(b16l X):0xA-0xF] X + 0x06 + [c=1 ? 0x60 : 0x00] *)
  [ true ⇒
   let X' ≝ match (lt_ex (b8l X) xA) ⊗ (⊖h) with
    [ true ⇒ X
    | false ⇒ plus_b8nc X 〈x0,x6〉 ] in
   let X'' ≝ match c with
    [ true ⇒ plus_b8nc X' 〈x6,x0〉
    | false ⇒ X' ] in
   pair ?? X'' c
  (* [X:0x9A-0xFF] *)
  (* c' = 1 *)
  (* X' = [X:0x9A-0xFF]
          [(b16l X):0x0-0x9] X + [h=1 ? 0x06 : 0x00] + 0x60
          [(b16l X):0xA-0xF] X + 0x6 + 0x60 *) 
  | false ⇒
   let X' ≝ match (lt_ex (b8l X) xA) ⊗ (⊖h) with
    [ true ⇒ X
    | false ⇒ plus_b8nc X 〈x0,x6〉 ] in
   let X'' ≝ plus_b8nc X' 〈x6,x0〉 in
   pair ?? X'' true
  ].

(* iteratore sui byte *)
definition forall_byte8 ≝
 λP.
  forall_exadecim (λbh.
  forall_exadecim (λbl.
   P (mk_byte8 bh bl))).

(* ********************** *)
(* TEOREMI/LEMMMI/ASSIOMI *)
(* ********************** *)

lemma byte8_of_nat_nat_of_byte8: ∀b. byte8_of_nat (nat_of_byte8 b) = b.
 intros;
 elim b;
 elim e;
 elim e1;
 reflexivity.
qed.

lemma lt_nat_of_byte8_256: ∀b. nat_of_byte8 b < 256.
 intro;
 unfold nat_of_byte8;
 letin H ≝ (lt_nat_of_exadecim_16 (b8h b)); clearbody H;
 letin K ≝ (lt_nat_of_exadecim_16 (b8l b)); clearbody K;
 unfold lt in H K ⊢ %;
 letin H' ≝ (le_S_S_to_le ? ? H); clearbody H'; clear H;
 letin K' ≝ (le_S_S_to_le ? ? K); clearbody K'; clear K;
 apply le_S_S;
 cut (16*b8h b ≤ 16*15);
  [ letin Hf ≝ (le_plus ? ? ? ? Hcut K'); clearbody Hf;
    simplify in Hf:(? ? %);
    assumption
  | apply le_times_r. apply H'.
  ]
qed.

lemma nat_of_byte8_byte8_of_nat: ∀n. nat_of_byte8 (byte8_of_nat n) = n \mod 256.
 intro;
 letin H ≝ (lt_nat_of_byte8_256 (byte8_of_nat n)); clearbody H;
 rewrite < (lt_to_eq_mod ? ? H); clear H;
 unfold byte8_of_nat;
 unfold nat_of_byte8;
 change with ((16*(exadecim_of_nat (n/16)) + exadecim_of_nat n) \mod 256 = n \mod 256);
 letin H ≝ (div_mod n 16 ?); clearbody H; [ autobatch | ];
 rewrite > symmetric_times in H;
 rewrite > nat_of_exadecim_exadecim_of_nat in ⊢ (? ? (? (? % ?) ?) ?);
 rewrite > nat_of_exadecim_exadecim_of_nat in ⊢ (? ? (? (? ? %) ?) ?);
 rewrite > H in ⊢ (? ? ? (? % ?)); clear H;
 rewrite > mod_plus in ⊢ (? ? % ?);
 rewrite > mod_plus in ⊢ (? ? ? %);
 apply eq_mod_to_eq_plus_mod;
 rewrite < mod_mod in ⊢ (? ? ? %); [ | autobatch by divides_n_n];
 rewrite < mod_mod in ⊢ (? ? % ?); [ | autobatch by divides_n_n];
 rewrite < (eq_mod_times_times_mod ? ? 16 256) in ⊢ (? ? (? % ?) ?); [2: reflexivity | ];
 rewrite < mod_mod in ⊢ (? ? % ?);
  [ reflexivity
  | autobatch by divides_n_n
  ].
qed.

lemma eq_nat_of_byte8_n_nat_of_byte8_mod_n_256:
 ∀n. byte8_of_nat n = byte8_of_nat (n \mod 256).
 intro;
 unfold byte8_of_nat;
 apply eq_f2;
  [ rewrite > exadecim_of_nat_mod in ⊢ (? ? % ?);
    rewrite > exadecim_of_nat_mod in ⊢ (? ? ? %);
    apply eq_f;
    elim daemon
  | rewrite > exadecim_of_nat_mod;
    rewrite > exadecim_of_nat_mod in ⊢ (? ? ? %);
    rewrite > divides_to_eq_mod_mod_mod;
     [ reflexivity
     | apply (witness ? ? 16). reflexivity.
     ]
  ]
qed.

lemma plusb8_ok:
 ∀b1,b2,c.
  match plus_b8 b1 b2 c with
   [ pair r c' ⇒ b1 + b2 + nat_of_bool c = nat_of_byte8 r + nat_of_bool c' * 256
   ].
 intros; elim daemon.
qed.

lemma plusb8_O_x:
 ∀b. plus_b8 (mk_byte8 x0 x0) b false = pair ?? b false.
 intros;
 elim b;
 elim e;
 elim e1;
 reflexivity.
qed.

lemma plusb8nc_O_x:
 ∀x. plus_b8nc (mk_byte8 x0 x0) x = x.
 intros;
 unfold plus_b8nc;
 rewrite > plusb8_O_x;
 reflexivity.
qed.

lemma eq_nat_of_byte8_mod: ∀b. nat_of_byte8 b = nat_of_byte8 b \mod 256.
 intro;
 lapply (lt_nat_of_byte8_256 b);
 rewrite > (lt_to_eq_mod ? ? Hletin) in ⊢ (? ? ? %);
 reflexivity.
qed.

theorem plusb8nc_ok:
 ∀b1,b2:byte8.nat_of_byte8 (plus_b8nc b1 b2) = (b1 + b2) \mod 256.
 intros;
 unfold plus_b8nc;
 generalize in match (plusb8_ok b1 b2 false);
 elim (plus_b8 b1 b2 false);
 simplify in H ⊢ %;
 change with (nat_of_byte8 a = (b1 + b2) \mod 256);
 rewrite < plus_n_O in H;
 rewrite > H; clear H;
 rewrite > mod_plus;
 letin K ≝ (eq_nat_of_byte8_mod a); clearbody K;
 letin K' ≝ (eq_mod_times_n_m_m_O (nat_of_bool b) 256 ?); clearbody K';
  [ unfold;apply le_S_S;apply le_O_n| ];
 rewrite > K' in ⊢ (? ? ? (? (? ? %) ?));
 rewrite < K in ⊢ (? ? ? (? (? % ?) ?));
 rewrite < plus_n_O;
 apply K;
qed.

lemma eq_eqb8_x0_x0_byte8_of_nat_S_false:
 ∀b. b < 255 → eq_b8 (mk_byte8 x0 x0) (byte8_of_nat (S b)) = false.
 intros;
 unfold byte8_of_nat;
 cut (b < 15 ∨ b ≥ 15);
  [ elim Hcut;
    [ unfold eq_b8;
      change in ⊢ (? ? (? ? %) ?) with (eq_ex x0 (exadecim_of_nat (S b))); 
      rewrite > eq_eqex_S_x0_false;
       [ elim (eq_ex (b8h (mk_byte8 x0 x0))
          (b8h (mk_byte8 (exadecim_of_nat (S b/16)) (exadecim_of_nat (S b)))));
         simplify;
         reflexivity
       | assumption
       ]
    | unfold eq_b8;
      change in ⊢ (? ? (? % ?) ?) with (eq_ex x0 (exadecim_of_nat (S b/16)));
      letin K ≝ (leq_m_n_to_eq_div_n_m_S (S b) 16 ? ?);
       [ unfold; autobatch by le_S_S,le_O_n;
       | unfold in H1;
         apply le_S_S;
         assumption
       | clearbody K;
         elim K; clear K;
         rewrite > H2;
         rewrite > eq_eqex_S_x0_false;
          [ reflexivity
          | unfold lt;
            unfold lt in H;
            rewrite < H2;
            clear H2; clear a; clear H1; clear Hcut;
            apply (le_times_to_le 16) [ autobatch by le_S_S,le_O_n;| ] ;
            rewrite > (div_mod (S b) 16) in H;[2:unfold; autobatch by le_S_S,le_O_n;|]
            rewrite > (div_mod 255 16) in H:(? ? %);[2:unfold; autobatch by le_S_S,le_O_n;|]
            lapply (le_to_le_plus_to_le ? ? ? ? ? H);
            [apply lt_S_to_le;
             apply lt_mod_m_m; unfold; apply le_S_S; apply le_O_n;
            |rewrite > sym_times;
             rewrite > sym_times in ⊢ (? ? %);
             normalize in ⊢ (? ? %);apply Hletin;
            ]
          ] 
       ]
    ]
  | elim (or_lt_le b 15);unfold ge;autobatch
  ].
qed.

axiom eq_mod_O_to_exists: ∀n,m. n \mod m = 0 → ∃z. n = z*m.

lemma eq_b8pred_S_a_a:
 ∀a. a < 255 → pred_b8 (byte8_of_nat (S a)) = byte8_of_nat a.
 intros;
 unfold pred_b8;
 apply (bool_elim ? (eq_ex (b8l (byte8_of_nat (S a))) x0)); intros;
  [ change with (mk_byte8 (pred_ex (b8h (byte8_of_nat (S a)))) (pred_ex (b8l (byte8_of_nat (S a))))
     = byte8_of_nat a);
    rewrite > (eqex_true_to_eq ? ? H1);
    normalize in ⊢ (? ? (? ? %) ?);
    unfold byte8_of_nat;
    change with (mk_byte8 (pred_ex (exadecim_of_nat (S a/16))) xF =
                 mk_byte8 (exadecim_of_nat (a/16)) (exadecim_of_nat a));
    lapply (eqex_true_to_eq ? ? H1); clear H1;
    unfold byte8_of_nat in Hletin;
    change in Hletin with (exadecim_of_nat (S a) = x0);
    lapply (eq_f ? ? nat_of_exadecim ? ? Hletin); clear Hletin;
    normalize in Hletin1:(? ? ? %);
    rewrite > nat_of_exadecim_exadecim_of_nat in Hletin1;
    elim (eq_mod_O_to_exists ? ? Hletin1); clear Hletin1;
    rewrite > H1;
    rewrite > lt_O_to_div_times; [2: unfold; apply le_S_S; apply le_O_n; | ]
    lapply (eq_f ? ? (λx.x/16) ? ? H1);
    rewrite > lt_O_to_div_times in Hletin; [2: unfold; apply le_S_S; apply le_O_n; | ]
    lapply (eq_f ? ? (λx.x \mod 16) ? ? H1);
    rewrite > eq_mod_times_n_m_m_O in Hletin1;
    elim daemon
  | change with (mk_byte8 (b8h (byte8_of_nat (S a))) (pred_ex (b8l (byte8_of_nat (S a))))
    = byte8_of_nat a);
    unfold byte8_of_nat;
    change with (mk_byte8 (exadecim_of_nat (S a/16)) (pred_ex (exadecim_of_nat (S a)))
    = mk_byte8 (exadecim_of_nat (a/16)) (exadecim_of_nat a));
    lapply (eqex_false_to_not_eq ? ? H1);
    unfold byte8_of_nat in Hletin;
    change in Hletin with (exadecim_of_nat (S a) ≠ x0);
    cut (nat_of_exadecim (exadecim_of_nat (S a)) ≠ 0);
     [2: intro;
       apply Hletin;
       lapply (eq_f ? ? exadecim_of_nat ? ? H2);
       rewrite > exadecim_of_nat_nat_of_exadecim in Hletin1;
       apply Hletin1
     | ];
    elim daemon
  ]
qed.

lemma plusb8nc_S:
 ∀x:byte8.∀n.plus_b8nc (byte8_of_nat (x*n)) x = byte8_of_nat (x * S n).
 intros;
 rewrite < byte8_of_nat_nat_of_byte8;
 rewrite > (plusb8nc_ok (byte8_of_nat (x*n)) x);
 rewrite < times_n_Sm;
 rewrite > nat_of_byte8_byte8_of_nat in ⊢ (? ? (? (? (? % ?) ?)) ?);
 rewrite > eq_nat_of_byte8_n_nat_of_byte8_mod_n_256 in ⊢ (? ? ? %);
 rewrite > mod_plus in ⊢ (? ? (? %) ?);
 rewrite > mod_plus in ⊢ (? ? ? (? %));
 rewrite < mod_mod in ⊢ (? ? (? (? (? % ?) ?)) ?); [2: apply divides_n_n; | ];
 rewrite > sym_plus in ⊢ (? ? (? (? % ?)) ?);
 reflexivity.
qed.

lemma eq_plusb8c_x0_x0_x_false:
 ∀x.plus_b8c (mk_byte8 x0 x0) x = false.
 intro;
 elim x;
 elim e;
 elim e1;
 reflexivity.
qed.

axiom eqb8_true_to_eq: ∀b,b'. eq_b8 b b' = true → b=b'.

axiom eqb8_false_to_not_eq: ∀b,b'. eq_b8 b b' = false → b ≠ b'.

axiom byte8_of_nat_mod: ∀n.byte8_of_nat n = byte8_of_nat (n \mod 256).

(* nuovi *)

lemma ok_mul_ex :
∀e1,e2.nat_of_byte8 (mul_ex e1 e2) = (nat_of_exadecim e1) * (nat_of_exadecim e2).
intros;
elim e1;
elim e2;
reflexivity.
qed.
