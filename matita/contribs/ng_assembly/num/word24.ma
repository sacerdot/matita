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

(* ********* *)
(* BYTE+WORD *)
(* ********* *)

nrecord word24 : Type ≝
 {
 w24x: byte8;
 w24h: byte8;
 w24l: byte8
 }.

(* \langle \rangle *)
notation "〈x;y;z〉" non associative with precedence 80
 for @{ 'mk_word24 $x $y $z }.
interpretation "mk_word24" 'mk_word24 x y z = (mk_word24 x y z).

(* iteratore sulle word *)
ndefinition forall_w24 ≝
 λP.
  forall_b8 (λbx.
  forall_b8 (λbh.
  forall_b8 (λbl.
   P (mk_word24 bx bh bl )))).

(* operatore = *)
ndefinition eq_w24 ≝
λw1,w2.(eq_b8 (w24x w1) (w24x w2)) ⊗
       (eq_b8 (w24h w1) (w24h w2)) ⊗
       (eq_b8 (w24l w1) (w24l w2)).

(* operatore < *)
ndefinition lt_w24 ≝
λw1,w2:word24.
 (lt_b8 (w24x w1) (w24x w2)) ⊕
 ((eq_b8 (w24x w1) (w24x w2)) ⊗ ((lt_b8 (w24h w1) (w24h w2)) ⊕
                                 ((eq_b8 (w24h w1) (w24h w2)) ⊗ (lt_b8 (w24l w1) (w24l w2))))).

(* operatore ≤ *)
ndefinition le_w24 ≝
λw1,w2:word24.
 (lt_b8 (w24x w1) (w24x w2)) ⊕
 ((eq_b8 (w24x w1) (w24x w2)) ⊗ ((lt_b8 (w24h w1) (w24h w2)) ⊕
                                 ((eq_b8 (w24h w1) (w24h w2)) ⊗ (le_b8 (w24l w1) (w24l w2))))).

(* operatore > *)
ndefinition gt_w24 ≝
λw1,w2:word24.
 (gt_b8 (w24x w1) (w24x w2)) ⊕
 ((eq_b8 (w24x w1) (w24x w2)) ⊗ ((gt_b8 (w24h w1) (w24h w2)) ⊕
                                 ((eq_b8 (w24h w1) (w24h w2)) ⊗ (gt_b8 (w24l w1) (w24l w2))))).

(* operatore ≥ *)
ndefinition ge_w24 ≝
λw1,w2:word24.
 (gt_b8 (w24x w1) (w24x w2)) ⊕
 ((eq_b8 (w24x w1) (w24x w2)) ⊗ ((gt_b8 (w24h w1) (w24h w2)) ⊕
                                 ((eq_b8 (w24h w1) (w24h w2)) ⊗ (ge_b8 (w24l w1) (w24l w2))))).

(* operatore and *)
ndefinition and_w24 ≝
λw1,w2:word24.
 mk_word24 (and_b8 (w24x w1) (w24x w2))
           (and_b8 (w24h w1) (w24h w2))
           (and_b8 (w24l w1) (w24l w2)).

(* operatore or *)
ndefinition or_w24 ≝
λw1,w2:word24.
 mk_word24 (or_b8 (w24x w1) (w24x w2))
           (or_b8 (w24h w1) (w24h w2))
           (or_b8 (w24l w1) (w24l w2)).

(* operatore xor *)
ndefinition xor_w24 ≝
λw1,w2:word24.
 mk_word24 (xor_b8 (w24x w1) (w24x w2))
           (xor_b8 (w24h w1) (w24h w2))
           (xor_b8 (w24l w1) (w24l w2)).

(* operatore Most Significant Bit *)
ndefinition getMSB_w24 ≝ λw:word24.getMSB_b8 (w24x w).
ndefinition setMSB_w24 ≝ λw:word24.mk_word24 (setMSB_b8 (w24x w)) (w24h w) (w24l w).
ndefinition clrMSB_w24 ≝ λw:word24.mk_word24 (clrMSB_b8 (w24x w)) (w24h w) (w24l w).

(* operatore Least Significant Bit *)
ndefinition getLSB_w24 ≝ λw:word24.getLSB_b8 (w24l w).
ndefinition setLSB_w24 ≝ λw:word24.mk_word24 (w24x w) (w24h w) (setLSB_b8 (w24l w)).
ndefinition clrLSB_w24 ≝ λw:word24.mk_word24 (w24x w) (w24h w) (clrLSB_b8 (w24l w)).

(* operatore rotazione destra con carry *)
ndefinition rcr_w24 ≝
λc:bool.λw:word24.match rcr_b8 c (w24x w) with
 [ pair c' wx' ⇒ match rcr_b8 c' (w24h w) with
  [ pair c'' wh' ⇒ match rcr_b8 c'' (w24l w) with
   [ pair c''' wl' ⇒ pair … c''' (mk_word24 wx' wh' wl') ]]]. 

(* operatore shift destro *)
ndefinition shr_w24 ≝ rcr_w24 false.

(* operatore rotazione destra *)
ndefinition ror_w24 ≝
λw.match shr_w24 w with
 [ pair c w' ⇒ match c with
  [ true ⇒ setMSB_w24 w' | false ⇒ w' ]].

(* operatore rotazione sinistra con carry *)
ndefinition rcl_w24 ≝
λc:bool.λw:word24.match rcl_b8 c (w24l w) with
 [ pair c' wl' ⇒ match rcl_b8 c' (w24h w) with
  [ pair c'' wh' ⇒ match rcl_b8 c'' (w24x w) with
   [ pair c''' wx' ⇒ pair … c''' (mk_word24 wx' wh' wl') ]]].

(* operatore shift sinistro *)
ndefinition shl_w24 ≝ rcl_w24 false.

(* operatore rotazione sinistra *)
ndefinition rol_w24 ≝
λw.match shl_w24 w with
 [ pair c w' ⇒ match c with
  [ true ⇒ setLSB_w24 w' | false ⇒ w' ]].

(* operatore not/complemento a 1 *)
ndefinition not_w24 ≝
λw:word24.mk_word24 (not_b8 (w24x w)) (not_b8 (w24h w)) (not_b8 (w24l w)).

(* operatore somma con data+carry → data+carry *)
ndefinition plus_w24_dc_dc ≝
λc:bool.λw1,w2:word24.
 match plus_b8_dc_dc c (w24l w1) (w24l w2) with
  [ pair c' l ⇒ match plus_b8_dc_dc c' (w24h w1) (w24h w2) with
   [ pair c'' h ⇒ match plus_b8_dc_dc c'' (w24x w1) (w24x w2) with
    [ pair c''' x ⇒ pair … c''' 〈x;h;l〉 ]]].

(* operatore somma con data+carry → data *)
ndefinition plus_w24_dc_d ≝ λc,w1,w2.snd … (plus_w24_dc_dc c w1 w2).

(* operatore somma con data+carry → c *)
ndefinition plus_w24_dc_c ≝ λc,w1,w2.fst … (plus_w24_dc_dc c w1 w2).

(* operatore somma con data → data+carry *)
ndefinition plus_w24_d_dc ≝ plus_w24_dc_dc false.

(* operatore somma con data → data *)
ndefinition plus_w24_d_d ≝ λw1,w2.snd … (plus_w24_d_dc w1 w2).

(* operatore somma con data → c *)
ndefinition plus_w24_d_c ≝ λw1,w2.fst … (plus_w24_d_dc w1 w2).

(* operatore predecessore *)
ndefinition pred_w24 ≝
λw:word24.match eq_b8 (w24l w) 〈x0,x0〉 with
 [ true ⇒ match eq_b8 (w24h w) 〈x0,x0〉 with
  [ true ⇒ mk_word24 (pred_b8 (w24x w)) (pred_b8 (w24h w)) (pred_b8 (w24l w))
  | false ⇒ mk_word24 (w24x w) (pred_b8 (w24h w)) (pred_b8 (w24l w)) ]
 | false ⇒ mk_word24 (w24x w) (w24h w) (pred_b8 (w24l w)) ].

(* operatore successore *)
ndefinition succ_w24 ≝
λw:word24.match eq_b8 (w24l w) 〈xF,xF〉 with
 [ true ⇒ match eq_b8 (w24h w) 〈xF,xF〉 with
  [ true ⇒ mk_word24 (succ_b8 (w24x w)) (succ_b8 (w24h w)) (succ_b8 (w24l w))
  | false ⇒ mk_word24 (w24x w) (succ_b8 (w24h w)) (succ_b8 (w24l w)) ]
 | false ⇒ mk_word24 (w24x w) (w24h w) (succ_b8 (w24l w)) ].

(* operatore neg/complemento a 2 *)
ndefinition compl_w24 ≝
λw:word24.match getMSB_w24 w with
 [ true ⇒ succ_w24 (not_w24 w)
 | false ⇒ not_w24 (pred_w24 w) ].

(* operatore abs *)
ndefinition abs_w24 ≝
λw:word24.match getMSB_w24 w with
 [ true ⇒ compl_w24 w | false ⇒ w ].

(* operatore x in [inf,sup] o in sup],[inf *)
ndefinition inrange_w24 ≝
λx,inf,sup:word24.
 match le_w24 inf sup with
  [ true ⇒ and_bool | false ⇒ or_bool ]
 (le_w24 inf x) (le_w24 x sup).
