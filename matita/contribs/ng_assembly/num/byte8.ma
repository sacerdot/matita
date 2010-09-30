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

include "num/exadecim.ma".
include "num/comp_num.ma".
include "num/bitrigesim.ma".
include "common/nat.ma".

(* **** *)
(* BYTE *)
(* **** *)

ndefinition byte8 ≝ comp_num exadecim.
ndefinition mk_byte8 ≝ λe1,e2.mk_comp_num exadecim e1 e2.

(* \langle \rangle *)
notation "〈x,y〉" non associative with precedence 80
 for @{ mk_comp_num exadecim $x $y }.

(* iteratore sui byte *)
ndefinition forall_b8 ≝ forall_cn ? forall_ex.

(* operatore = *)
ndefinition eq_b8 ≝ eq2_cn ? eq_ex.

(* operatore < *)
ndefinition lt_b8 ≝ ltgt_cn ? eq_ex lt_ex.

(* operatore ≤ *)
ndefinition le_b8 ≝ lege_cn ? eq_ex lt_ex le_ex.

(* operatore > *)
ndefinition gt_b8 ≝ ltgt_cn ? eq_ex gt_ex.

(* operatore ≥ *)
ndefinition ge_b8 ≝ lege_cn ? eq_ex gt_ex ge_ex.

(* operatore and *)
ndefinition and_b8 ≝ fop2_cn ? and_ex.

(* operatore or *)
ndefinition or_b8 ≝ fop2_cn ? or_ex.

(* operatore xor *)
ndefinition xor_b8 ≝ fop2_cn ? xor_ex.

(* operatore Most Significant Bit *)
ndefinition getMSB_b8 ≝ getOPH_cn ? getMSB_ex.
ndefinition setMSB_b8 ≝ setOPH_cn ? setMSB_ex.
ndefinition clrMSB_b8 ≝ setOPH_cn ? clrMSB_ex.

(* operatore Least Significant Bit *)
ndefinition getLSB_b8 ≝ getOPL_cn ? getLSB_ex.
ndefinition setLSB_b8 ≝ setOPL_cn ? setLSB_ex.
ndefinition clrLSB_b8 ≝ setOPL_cn ? clrLSB_ex.

(* operatore estensione unsigned *)
ndefinition extu_b8 ≝ λe2.〈x0,e2〉.

(* operatore estensione signed *)
ndefinition exts_b8 ≝
λe2.〈(match getMSB_ex e2 with 
      [ true ⇒ xF | false ⇒ x0 ]),e2〉.

(* operatore rotazione destra con carry *)
ndefinition rcr_b8 ≝ opcr_cn ? rcr_ex.

(* operatore shift destro *)
ndefinition shr_b8 ≝ opcr_cn ? rcr_ex false.

(* operatore rotazione destra *)
ndefinition ror_b8 ≝
λb.match shr_b8 b with
 [ pair c b' ⇒ match c with
  [ true ⇒ setMSB_b8 b' | false ⇒ b' ]].

(* operatore rotazione sinistra con carry *)
ndefinition rcl_b8 ≝ opcl_cn ? rcl_ex.

(* operatore shift sinistro *)
ndefinition shl_b8 ≝ opcl_cn ? rcl_ex false.

(* operatore rotazione sinistra *)
ndefinition rol_b8 ≝
λb.match shl_b8 b with
 [ pair c b' ⇒ match c with
  [ true ⇒ setLSB_b8 b' | false ⇒ b' ]].

(* operatore not/complemento a 1 *)
ndefinition not_b8 ≝ fop_cn ? not_ex.

(* operatore somma con data+carry → data+carry *)
ndefinition plus_b8_dc_dc ≝ opcl2_cn ? plus_ex_dc_dc.

(* operatore somma con data+carry → data *)
ndefinition plus_b8_dc_d ≝ λc,b1,b2.snd … (plus_b8_dc_dc c b1 b2).

(* operatore somma con data+carry → c *)
ndefinition plus_b8_dc_c ≝ λc,b1,b2.fst … (plus_b8_dc_dc c b1 b2).

(* operatore somma con data → data+carry *)
ndefinition plus_b8_d_dc ≝ opcl2_cn ? plus_ex_dc_dc false.

(* operatore somma con data → data *)
ndefinition plus_b8_d_d ≝ λb1,b2.snd … (plus_b8_d_dc b1 b2).

(* operatore somma con data → c *)
ndefinition plus_b8_d_c ≝ λb1,b2.fst … (plus_b8_d_dc b1 b2).

(* operatore predecessore *)
ndefinition pred_b8 ≝ predsucc_cn ? (eq_ex x0) pred_ex.

(* operatore successore *)
ndefinition succ_b8 ≝ predsucc_cn ? (eq_ex xF) succ_ex.

(* operatore neg/complemento a 2 *)
ndefinition compl_b8 ≝
λb:byte8.match getMSB_b8 b with
 [ true ⇒ succ_b8 (not_b8 b)
 | false ⇒ not_b8 (pred_b8 b) ].

(* operatore abs *)
ndefinition abs_b8 ≝
λb:byte8.match getMSB_b8 b with
 [ true ⇒ compl_b8 b | false ⇒ b ].

(* operatore x in [inf,sup] o in sup],[inf *)
ndefinition inrange_b8 ≝
λx,inf,sup:byte8.
 match le_b8 inf sup with
  [ true ⇒ and_bool | false ⇒ or_bool ]
 (le_b8 inf x) (le_b8 x sup).

(* operatore moltiplicazione senza segno: e*e=[0x00,0xE1] *)
ndefinition mulu_ex ≝
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

(* operatore moltiplicazione con segno *)
ndefinition muls_ex ≝
λe1,e2:exadecim.match e1 with
 [ x0 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉 | x1 ⇒ 〈x0,x0〉 | x2 ⇒ 〈x0,x0〉 | x3 ⇒ 〈x0,x0〉
  | x4 ⇒ 〈x0,x0〉 | x5 ⇒ 〈x0,x0〉 | x6 ⇒ 〈x0,x0〉 | x7 ⇒ 〈x0,x0〉
  | x8 ⇒ 〈x0,x0〉 | x9 ⇒ 〈x0,x0〉 | xA ⇒ 〈x0,x0〉 | xB ⇒ 〈x0,x0〉
  | xC ⇒ 〈x0,x0〉 | xD ⇒ 〈x0,x0〉 | xE ⇒ 〈x0,x0〉 | xF ⇒ 〈x0,x0〉 ]
 | x1 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉 | x1 ⇒ 〈x0,x1〉 | x2 ⇒ 〈x0,x2〉 | x3 ⇒ 〈x0,x3〉
  | x4 ⇒ 〈x0,x4〉 | x5 ⇒ 〈x0,x5〉 | x6 ⇒ 〈x0,x6〉 | x7 ⇒ 〈x0,x7〉
  | x8 ⇒ 〈xF,x8〉 | x9 ⇒ 〈xF,x9〉 | xA ⇒ 〈xF,xA〉 | xB ⇒ 〈xF,xB〉
  | xC ⇒ 〈xF,xC〉 | xD ⇒ 〈xF,xD〉 | xE ⇒ 〈xF,xE〉 | xF ⇒ 〈xF,xF〉 ]
 | x2 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉 | x1 ⇒ 〈x0,x2〉 | x2 ⇒ 〈x0,x4〉 | x3 ⇒ 〈x0,x6〉
  | x4 ⇒ 〈x0,x8〉 | x5 ⇒ 〈x0,xA〉 | x6 ⇒ 〈x0,xC〉 | x7 ⇒ 〈x0,xE〉
  | x8 ⇒ 〈xF,x0〉 | x9 ⇒ 〈xF,x2〉 | xA ⇒ 〈xF,x4〉 | xB ⇒ 〈xF,x6〉
  | xC ⇒ 〈xF,x8〉 | xD ⇒ 〈xF,xA〉 | xE ⇒ 〈xF,xC〉 | xF ⇒ 〈xF,xE〉 ]
 | x3 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉 | x1 ⇒ 〈x0,x3〉 | x2 ⇒ 〈x0,x6〉 | x3 ⇒ 〈x0,x9〉
  | x4 ⇒ 〈x0,xC〉 | x5 ⇒ 〈x0,xF〉 | x6 ⇒ 〈x1,x2〉 | x7 ⇒ 〈x1,x5〉
  | x8 ⇒ 〈xE,x8〉 | x9 ⇒ 〈xE,xB〉 | xA ⇒ 〈xE,xE〉 | xB ⇒ 〈xF,x1〉
  | xC ⇒ 〈xF,x4〉 | xD ⇒ 〈xF,x7〉 | xE ⇒ 〈xF,xA〉 | xF ⇒ 〈xF,xD〉 ]
 | x4 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉 | x1 ⇒ 〈x0,x4〉 | x2 ⇒ 〈x0,x8〉 | x3 ⇒ 〈x0,xC〉
  | x4 ⇒ 〈x1,x0〉 | x5 ⇒ 〈x1,x4〉 | x6 ⇒ 〈x1,x8〉 | x7 ⇒ 〈x1,xC〉
  | x8 ⇒ 〈xE,x0〉 | x9 ⇒ 〈xE,x4〉 | xA ⇒ 〈xE,x8〉 | xB ⇒ 〈xE,xC〉
  | xC ⇒ 〈xF,x0〉 | xD ⇒ 〈xF,x4〉 | xE ⇒ 〈xF,x8〉 | xF ⇒ 〈xF,xC〉 ]
 | x5 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉 | x1 ⇒ 〈x0,x5〉 | x2 ⇒ 〈x0,xA〉 | x3 ⇒ 〈x0,xF〉
  | x4 ⇒ 〈x1,x4〉 | x5 ⇒ 〈x1,x9〉 | x6 ⇒ 〈x1,xE〉 | x7 ⇒ 〈x2,x3〉
  | x8 ⇒ 〈xD,x8〉 | x9 ⇒ 〈xD,xD〉 | xA ⇒ 〈xE,x2〉 | xB ⇒ 〈xE,x7〉
  | xC ⇒ 〈xE,xC〉 | xD ⇒ 〈xF,x1〉 | xE ⇒ 〈xF,x6〉 | xF ⇒ 〈xF,xB〉 ]
 | x6 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉 | x1 ⇒ 〈x0,x6〉 | x2 ⇒ 〈x0,xC〉 | x3 ⇒ 〈x1,x2〉
  | x4 ⇒ 〈x1,x8〉 | x5 ⇒ 〈x1,xE〉 | x6 ⇒ 〈x2,x4〉 | x7 ⇒ 〈x2,xA〉
  | x8 ⇒ 〈xD,x0〉 | x9 ⇒ 〈xD,x6〉 | xA ⇒ 〈xD,xC〉 | xB ⇒ 〈xE,x2〉
  | xC ⇒ 〈xE,x8〉 | xD ⇒ 〈xE,xE〉 | xE ⇒ 〈xF,x4〉 | xF ⇒ 〈xF,xA〉 ]
 | x7 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉 | x1 ⇒ 〈x0,x7〉 | x2 ⇒ 〈x0,xE〉 | x3 ⇒ 〈x1,x5〉
  | x4 ⇒ 〈x1,xC〉 | x5 ⇒ 〈x2,x3〉 | x6 ⇒ 〈x2,xA〉 | x7 ⇒ 〈x3,x1〉
  | x8 ⇒ 〈xC,x8〉 | x9 ⇒ 〈xC,xF〉 | xA ⇒ 〈xD,x6〉 | xB ⇒ 〈xD,xD〉
  | xC ⇒ 〈xE,x4〉 | xD ⇒ 〈xE,xB〉 | xE ⇒ 〈xF,x2〉 | xF ⇒ 〈xF,x9〉 ]
 | x8 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉 | x1 ⇒ 〈xF,x8〉 | x2 ⇒ 〈xF,x0〉 | x3 ⇒ 〈xE,x8〉
  | x4 ⇒ 〈xE,x0〉 | x5 ⇒ 〈xD,x8〉 | x6 ⇒ 〈xD,x0〉 | x7 ⇒ 〈xC,x8〉
  | x8 ⇒ 〈x4,x0〉 | x9 ⇒ 〈x3,x8〉 | xA ⇒ 〈x3,x0〉 | xB ⇒ 〈x2,x8〉
  | xC ⇒ 〈x2,x0〉 | xD ⇒ 〈x1,x8〉 | xE ⇒ 〈x1,x0〉 | xF ⇒ 〈x0,x8〉 ]
 | x9 ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉 | x1 ⇒ 〈xF,x9〉 | x2 ⇒ 〈xF,x2〉 | x3 ⇒ 〈xE,xB〉
  | x4 ⇒ 〈xE,x4〉 | x5 ⇒ 〈xD,xD〉 | x6 ⇒ 〈xD,x6〉 | x7 ⇒ 〈xC,xF〉
  | x8 ⇒ 〈x3,x8〉 | x9 ⇒ 〈x3,x1〉 | xA ⇒ 〈x2,xA〉 | xB ⇒ 〈x2,x3〉
  | xC ⇒ 〈x1,xC〉 | xD ⇒ 〈x1,x5〉 | xE ⇒ 〈x0,xE〉 | xF ⇒ 〈x0,x7〉 ]
 | xA ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉 | x1 ⇒ 〈xF,xA〉 | x2 ⇒ 〈xF,x4〉 | x3 ⇒ 〈xE,xE〉
  | x4 ⇒ 〈xE,x8〉 | x5 ⇒ 〈xE,x2〉 | x6 ⇒ 〈xD,xC〉 | x7 ⇒ 〈xD,x6〉
  | x8 ⇒ 〈x3,x0〉 | x9 ⇒ 〈x2,xA〉 | xA ⇒ 〈x2,x4〉 | xB ⇒ 〈x1,xE〉
  | xC ⇒ 〈x1,x8〉 | xD ⇒ 〈x1,x2〉 | xE ⇒ 〈x0,xC〉 | xF ⇒ 〈x0,x6〉 ]
 | xB ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉 | x1 ⇒ 〈xF,xB〉 | x2 ⇒ 〈xF,x6〉 | x3 ⇒ 〈xF,x1〉
  | x4 ⇒ 〈xE,xC〉 | x5 ⇒ 〈xE,x7〉 | x6 ⇒ 〈xE,x2〉 | x7 ⇒ 〈xD,xD〉
  | x8 ⇒ 〈x2,x8〉 | x9 ⇒ 〈x2,x3〉 | xA ⇒ 〈x1,xE〉 | xB ⇒ 〈x1,x9〉
  | xC ⇒ 〈x1,x4〉 | xD ⇒ 〈x0,xF〉 | xE ⇒ 〈x0,xA〉 | xF ⇒ 〈x0,x5〉 ]
 | xC ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉 | x1 ⇒ 〈xF,xC〉 | x2 ⇒ 〈xF,x8〉 | x3 ⇒ 〈xF,x4〉
  | x4 ⇒ 〈xF,x0〉 | x5 ⇒ 〈xE,xC〉 | x6 ⇒ 〈xE,x8〉 | x7 ⇒ 〈xE,x4〉
  | x8 ⇒ 〈x2,x0〉 | x9 ⇒ 〈x1,xC〉 | xA ⇒ 〈x1,x8〉 | xB ⇒ 〈x1,x4〉
  | xC ⇒ 〈x1,x0〉 | xD ⇒ 〈x0,xC〉 | xE ⇒ 〈x0,x8〉 | xF ⇒ 〈x0,x4〉 ]
 | xD ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉 | x1 ⇒ 〈xF,xD〉 | x2 ⇒ 〈xF,xA〉 | x3 ⇒ 〈xF,x7〉
  | x4 ⇒ 〈xF,x4〉 | x5 ⇒ 〈xF,x1〉 | x6 ⇒ 〈xE,xE〉 | x7 ⇒ 〈xE,xB〉
  | x8 ⇒ 〈x1,x8〉 | x9 ⇒ 〈x1,x5〉 | xA ⇒ 〈x1,x2〉 | xB ⇒ 〈x0,xF〉
  | xC ⇒ 〈x0,xC〉 | xD ⇒ 〈x0,x9〉 | xE ⇒ 〈x0,x6〉 | xF ⇒ 〈x0,x3〉 ]
 | xE ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉 | x1 ⇒ 〈xF,xE〉 | x2 ⇒ 〈xF,xC〉 | x3 ⇒ 〈xF,xA〉
  | x4 ⇒ 〈xF,x8〉 | x5 ⇒ 〈xF,x6〉 | x6 ⇒ 〈xF,x4〉 | x7 ⇒ 〈xF,x2〉
  | x8 ⇒ 〈x1,x0〉 | x9 ⇒ 〈x0,xE〉 | xA ⇒ 〈x0,xC〉 | xB ⇒ 〈x0,xA〉
  | xC ⇒ 〈x0,x8〉 | xD ⇒ 〈x0,x6〉 | xE ⇒ 〈x0,x4〉 | xF ⇒ 〈x0,x2〉 ]
 | xF ⇒ match e2 with
  [ x0 ⇒ 〈x0,x0〉 | x1 ⇒ 〈xF,xF〉 | x2 ⇒ 〈xF,xE〉 | x3 ⇒ 〈xF,xD〉
  | x4 ⇒ 〈xF,xC〉 | x5 ⇒ 〈xF,xB〉 | x6 ⇒ 〈xF,xA〉 | x7 ⇒ 〈xF,x9〉
  | x8 ⇒ 〈x0,x8〉 | x9 ⇒ 〈x0,x7〉 | xA ⇒ 〈x0,x6〉 | xB ⇒ 〈x0,x5〉
  | xC ⇒ 〈x0,x4〉 | xD ⇒ 〈x0,x3〉 | xE ⇒ 〈x0,x2〉 | xF ⇒ 〈x0,x1〉 ]
 ].

(* correzione per somma su BCD *)
(* input: halfcarry,carry,X(BCD+BCD) *)
(* output: X',carry' *)
ndefinition daa_b8 ≝
λh,c:bool.λX:byte8.
 match lt_b8 X 〈x9,xA〉 with
  (* [X:0x00-0x99] *)
  (* c' = c *)
  (* X' = [(b16l X):0x0-0x9] X + [h=1 ? 0x06 : 0x00] + [c=1 ? 0x60 : 0x00]
          [(b16l X):0xA-0xF] X + 0x06 + [c=1 ? 0x60 : 0x00] *)
  [ true ⇒
   let X' ≝ match (lt_ex (cnL ? X) xA) ⊗ (⊖h) with
    [ true ⇒ X
    | false ⇒ plus_b8_d_d X 〈x0,x6〉 ] in
   let X'' ≝ match c with
    [ true ⇒ plus_b8_d_d X' 〈x6,x0〉
    | false ⇒ X' ] in
   pair … c X''
  (* [X:0x9A-0xFF] *)
  (* c' = 1 *)
  (* X' = [X:0x9A-0xFF]
          [(b16l X):0x0-0x9] X + [h=1 ? 0x06 : 0x00] + 0x60
          [(b16l X):0xA-0xF] X + 0x6 + 0x60 *) 
  | false ⇒
   let X' ≝ match (lt_ex (cnL ? X) xA) ⊗ (⊖h) with
    [ true ⇒ X
    | false ⇒ plus_b8_d_d X 〈x0,x6〉 ] in
   let X'' ≝ plus_b8_d_d X' 〈x6,x0〉 in
   pair … true X''
  ].

(* byte ricorsivi *)
ninductive rec_byte8 : byte8 → Type ≝
  b8_O : rec_byte8 〈x0,x0〉
| b8_S : ∀n.rec_byte8 n → rec_byte8 (succ_b8 n).

(* byte → byte ricorsivi *)
ndefinition b8_to_recb8_aux1 : Πn.rec_byte8 〈n,x0〉 → rec_byte8 〈succ_ex n,x0〉 ≝
λn.λrecb:rec_byte8 〈n,x0〉.
 b8_S 〈n,xF〉 (b8_S 〈n,xE〉 (b8_S 〈n,xD〉 (b8_S 〈n,xC〉 (
 b8_S 〈n,xB〉 (b8_S 〈n,xA〉 (b8_S 〈n,x9〉 (b8_S 〈n,x8〉 (
 b8_S 〈n,x7〉 (b8_S 〈n,x6〉 (b8_S 〈n,x5〉 (b8_S 〈n,x4〉 (
 b8_S 〈n,x3〉 (b8_S 〈n,x2〉 (b8_S 〈n,x1〉 (b8_S 〈n,x0〉 recb))))))))))))))).

(* ... cifra esadecimale superiore *)
nlet rec b8_to_recb8_aux2 (n:exadecim) (r:rec_exadecim n) on r ≝
 match r return λx.λy:rec_exadecim x.rec_byte8 〈x,x0〉 with
  [ ex_O ⇒ b8_O
  | ex_S t n' ⇒ b8_to_recb8_aux1 ? (b8_to_recb8_aux2 t n')
  ].

(* ... cifra esadecimale inferiore *)
ndefinition b8_to_recb8_aux3 : Πn1,n2.rec_byte8 〈n1,x0〉 → rec_byte8 〈n1,n2〉 ≝
λn1,n2.λrecb:rec_byte8 〈n1,x0〉.
 match n2 return λx.rec_byte8 〈n1,x〉 with
  [ x0 ⇒ recb
  | x1 ⇒ b8_S 〈n1,x0〉 recb
  | x2 ⇒ b8_S 〈n1,x1〉 (b8_S 〈n1,x0〉 recb)
  | x3 ⇒ b8_S 〈n1,x2〉 (b8_S 〈n1,x1〉 (b8_S 〈n1,x0〉 recb))
  | x4 ⇒ b8_S 〈n1,x3〉 (b8_S 〈n1,x2〉 (b8_S 〈n1,x1〉 (b8_S 〈n1,x0〉 recb)))
  | x5 ⇒ b8_S 〈n1,x4〉 (b8_S 〈n1,x3〉 (b8_S 〈n1,x2〉 (b8_S 〈n1,x1〉 (
         b8_S 〈n1,x0〉 recb))))
  | x6 ⇒ b8_S 〈n1,x5〉 (b8_S 〈n1,x4〉 (b8_S 〈n1,x3〉 (b8_S 〈n1,x2〉 (
         b8_S 〈n1,x1〉 (b8_S 〈n1,x0〉 recb)))))
  | x7 ⇒ b8_S 〈n1,x6〉 (b8_S 〈n1,x5〉 (b8_S 〈n1,x4〉 (b8_S 〈n1,x3〉 (
         b8_S 〈n1,x2〉 (b8_S 〈n1,x1〉 (b8_S 〈n1,x0〉 recb))))))
  | x8 ⇒ b8_S 〈n1,x7〉 (b8_S 〈n1,x6〉 (b8_S 〈n1,x5〉 (b8_S 〈n1,x4〉 (
         b8_S 〈n1,x3〉 (b8_S 〈n1,x2〉 (b8_S 〈n1,x1〉 (b8_S 〈n1,x0〉 recb)))))))
  | x9 ⇒ b8_S 〈n1,x8〉 (b8_S 〈n1,x7〉 (b8_S 〈n1,x6〉 (b8_S 〈n1,x5〉 (
         b8_S 〈n1,x4〉 (b8_S 〈n1,x3〉 (b8_S 〈n1,x2〉 (b8_S 〈n1,x1〉 (
         b8_S 〈n1,x0〉 recb))))))))
  | xA ⇒ b8_S 〈n1,x9〉 (b8_S 〈n1,x8〉 (b8_S 〈n1,x7〉 (b8_S 〈n1,x6〉 (
         b8_S 〈n1,x5〉 (b8_S 〈n1,x4〉 (b8_S 〈n1,x3〉 (b8_S 〈n1,x2〉 (
         b8_S 〈n1,x1〉 (b8_S 〈n1,x0〉 recb)))))))))
  | xB ⇒ b8_S 〈n1,xA〉 (b8_S 〈n1,x9〉 (b8_S 〈n1,x8〉 (b8_S 〈n1,x7〉 (
         b8_S 〈n1,x6〉 (b8_S 〈n1,x5〉 (b8_S 〈n1,x4〉 (b8_S 〈n1,x3〉 (
         b8_S 〈n1,x2〉 (b8_S 〈n1,x1〉 (b8_S 〈n1,x0〉 recb))))))))))
  | xC ⇒ b8_S 〈n1,xB〉 (b8_S 〈n1,xA〉 (b8_S 〈n1,x9〉 (b8_S 〈n1,x8〉 (
         b8_S 〈n1,x7〉 (b8_S 〈n1,x6〉 (b8_S 〈n1,x5〉 (b8_S 〈n1,x4〉 (
         b8_S 〈n1,x3〉 (b8_S 〈n1,x2〉 (b8_S 〈n1,x1〉 (b8_S 〈n1,x0〉 recb)))))))))))
  | xD ⇒ b8_S 〈n1,xC〉 (b8_S 〈n1,xB〉 (b8_S 〈n1,xA〉 (b8_S 〈n1,x9〉 (
         b8_S 〈n1,x8〉 (b8_S 〈n1,x7〉 (b8_S 〈n1,x6〉 (b8_S 〈n1,x5〉 (
         b8_S 〈n1,x4〉 (b8_S 〈n1,x3〉 (b8_S 〈n1,x2〉 (b8_S 〈n1,x1〉 (
         b8_S 〈n1,x0〉 recb))))))))))))
  | xE ⇒ b8_S 〈n1,xD〉 (b8_S 〈n1,xC〉 (b8_S 〈n1,xB〉 (b8_S 〈n1,xA〉 (
         b8_S 〈n1,x9〉 (b8_S 〈n1,x8〉 (b8_S 〈n1,x7〉 (b8_S 〈n1,x6〉 (
         b8_S 〈n1,x5〉 (b8_S 〈n1,x4〉 (b8_S 〈n1,x3〉 (b8_S 〈n1,x2〉 (
         b8_S 〈n1,x1〉 (b8_S 〈n1,x0〉 recb)))))))))))))
  | xF ⇒ b8_S 〈n1,xE〉 (b8_S 〈n1,xD〉 (b8_S 〈n1,xC〉 (b8_S 〈n1,xB〉 (
         b8_S 〈n1,xA〉 (b8_S 〈n1,x9〉 (b8_S 〈n1,x8〉 (b8_S 〈n1,x7〉 (
         b8_S 〈n1,x6〉 (b8_S 〈n1,x5〉 (b8_S 〈n1,x4〉 (b8_S 〈n1,x3〉 (
         b8_S 〈n1,x2〉 (b8_S 〈n1,x1〉 (b8_S 〈n1,x0〉 recb))))))))))))))
  ].

(*
nlemma b8_to_recb8 : Πb.rec_byte8 b.
 #b; nletin K ≝ (b8_to_recb8_aux3 
     (b8h b) (b8l b) (b8_to_recb8_aux2 (b8h b) (ex_to_recex (b8h b))));
 ncases b in K; #e1; #e2; #K; napply K;
nqed.
*)

ndefinition b8_to_recb8 : Πb.rec_byte8 b ≝
λb.match b with
 [ mk_comp_num h l ⇒ b8_to_recb8_aux3 h l (b8_to_recb8_aux2 h (ex_to_recex h)) ].

(* ottali → esadecimali *)
ndefinition b8_of_bit ≝
λn.match n with
 [ t00 ⇒ 〈x0,x0〉 | t01 ⇒ 〈x0,x1〉 | t02 ⇒ 〈x0,x2〉 | t03 ⇒ 〈x0,x3〉
 | t04 ⇒ 〈x0,x4〉 | t05 ⇒ 〈x0,x5〉 | t06 ⇒ 〈x0,x6〉 | t07 ⇒ 〈x0,x7〉
 | t08 ⇒ 〈x0,x8〉 | t09 ⇒ 〈x0,x9〉 | t0A ⇒ 〈x0,xA〉 | t0B ⇒ 〈x0,xB〉
 | t0C ⇒ 〈x0,xC〉 | t0D ⇒ 〈x0,xD〉 | t0E ⇒ 〈x0,xE〉 | t0F ⇒ 〈x0,xF〉
 | t10 ⇒ 〈x1,x0〉 | t11 ⇒ 〈x1,x1〉 | t12 ⇒ 〈x1,x2〉 | t13 ⇒ 〈x1,x3〉
 | t14 ⇒ 〈x1,x4〉 | t15 ⇒ 〈x1,x5〉 | t16 ⇒ 〈x1,x6〉 | t17 ⇒ 〈x1,x7〉
 | t18 ⇒ 〈x1,x8〉 | t19 ⇒ 〈x1,x9〉 | t1A ⇒ 〈x1,xA〉 | t1B ⇒ 〈x1,xB〉
 | t1C ⇒ 〈x1,xC〉 | t1D ⇒ 〈x1,xD〉 | t1E ⇒ 〈x1,xE〉 | t1F ⇒ 〈x1,xF〉
 ].
