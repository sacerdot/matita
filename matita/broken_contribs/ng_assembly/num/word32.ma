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
ndefinition ext_word32 ≝ λw2.mk_comp_num word16 〈〈x0,x0〉:〈x0,x0〉〉 w2.

(* \langle \rangle *)
notation "〈x.y〉" non associative with precedence 80
 for @{ mk_comp_num word16 $x $y }.

(* iteratore sulle dword *)
ndefinition forall_w32 ≝ forall_cn ? forall_w16.

(* operatore = *)
ndefinition eq_w32 ≝ eq2_cn ? eq_w16.

(* operatore < *)
ndefinition lt_w32 ≝ ltgt_cn ? eq_w16 lt_w16.

(* operatore ≤ *)
ndefinition le_w32 ≝ lege_cn ? eq_w16 lt_w16 le_w16.

(* operatore > *)
ndefinition gt_w32 ≝ ltgt_cn ? eq_w16 gt_w16.

(* operatore ≥ *)
ndefinition ge_w32 ≝ lege_cn ? eq_w16 gt_w16 ge_w16.

(* operatore and *)
ndefinition and_w32 ≝ fop2_cn ? and_w16.

(* operatore or *)
ndefinition or_w32 ≝ fop2_cn ? or_w16.

(* operatore xor *)
ndefinition xor_w32 ≝ fop2_cn ? xor_w16.

(* operatore Most Significant Bit *)
ndefinition getMSB_w32 ≝ getOPH_cn ? getMSB_w16.
ndefinition setMSB_w32 ≝ setOPH_cn ? setMSB_w16.
ndefinition clrMSB_w32 ≝ setOPH_cn ? clrMSB_w16.

(* operatore Least Significant Bit *)
ndefinition getLSB_w32 ≝ getOPL_cn ? getLSB_w16.
ndefinition setLSB_w32 ≝ setOPL_cn ? setLSB_w16.
ndefinition clrLSB_w32 ≝ setOPL_cn ? clrLSB_w16.

(* operatore estensione unsigned *)
ndefinition extu_w32 ≝ λw2.〈〈〈x0,x0〉:〈x0,x0〉〉.w2〉.
ndefinition extu2_w32 ≝ λb2.〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:b2〉〉.
ndefinition extu3_w32 ≝ λe2.〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,e2〉〉〉.

(* operatore estensione signed *)
ndefinition exts_w32 ≝
λw2.〈(match getMSB_w16 w2 with
      [ true ⇒ 〈〈xF,xF〉:〈xF,xF〉〉 | false ⇒ 〈〈x0,x0〉:〈x0,x0〉〉 ]).w2〉.
ndefinition exts2_w32 ≝
λb2.(match getMSB_b8 b2 with
      [ true ⇒ 〈〈〈xF,xF〉:〈xF,xF〉〉.〈〈xF,xF〉:b2〉〉 | false ⇒ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:b2〉〉 ]).
ndefinition exts3_w32 ≝
λe2.(match getMSB_ex e2 with
      [ true ⇒ 〈〈〈xF,xF〉:〈xF,xF〉〉.〈〈xF,xF〉:〈xF,e2〉〉〉 | false ⇒ 〈〈〈x0,x0〉:〈x0,x0〉〉.〈〈x0,x0〉:〈x0,e2〉〉〉 ]).

(* operatore rotazione destra con carry *)
ndefinition rcr_w32 ≝ opcr_cn ? rcr_w16.

(* operatore shift destro *)
ndefinition shr_w32 ≝ opcr_cn ? rcr_w16 false.

(* operatore rotazione destra *)
ndefinition ror_w32 ≝
λw.match shr_w32 w with
 [ pair c w' ⇒ match c with
  [ true ⇒ setMSB_w32 w' | false ⇒ w' ]].

(* operatore rotazione sinistra con carry *)
ndefinition rcl_w32 ≝ opcl_cn ? rcl_w16.

(* operatore shift sinistro *)
ndefinition shl_w32 ≝ opcl_cn ? rcl_w16 false.

(* operatore rotazione sinistra *)
ndefinition rol_w32 ≝
λw.match shl_w32 w with
 [ pair c w' ⇒ match c with
  [ true ⇒ setLSB_w32 w' | false ⇒ w' ]].

(* operatore not/complemento a 1 *)
ndefinition not_w32 ≝ fop_cn ? not_w16.

(* operatore somma con data+carry → data+carry *)
ndefinition plus_w32_dc_dc ≝ opcl2_cn ? plus_w16_dc_dc.

(* operatore somma con data+carry → data *)
ndefinition plus_w32_dc_d ≝ λc,w1,w2.snd … (plus_w32_dc_dc c w1 w2).

(* operatore somma con data+carry → c *)
ndefinition plus_w32_dc_c ≝ λc,w1,w2.fst … (plus_w32_dc_dc c w1 w2).

(* operatore somma con data → data+carry *)
ndefinition plus_w32_d_dc ≝ opcl2_cn ? plus_w16_dc_dc false.

(* operatore somma con data → data *)
ndefinition plus_w32_d_d ≝ λw1,w2.snd … (plus_w32_d_dc w1 w2).

(* operatore somma con data → c *)
ndefinition plus_w32_d_c ≝ λw1,w2.fst … (plus_w32_d_dc w1 w2).

(* operatore predecessore *)
ndefinition pred_w32 ≝ predsucc_cn ? (eq_w16 〈〈x0,x0〉:〈x0,x0〉〉) pred_w16.

(* operatore successore *)
ndefinition succ_w32 ≝ predsucc_cn ? (eq_w16 〈〈xF,xF〉:〈xF,xF〉〉) succ_w16.

(* operatore neg/complemento a 2 *)
ndefinition compl_w32 ≝
λw:word32.match getMSB_w32 w with
 [ true ⇒ succ_w32 (not_w32 w)
 | false ⇒ not_w32 (pred_w32 w) ].

(* operatore abs *)
ndefinition abs_w32 ≝
λw:word32.match getMSB_w32 w with
 [ true ⇒ compl_w32 w | false ⇒ w ].

(* operatore x in [inf,sup] o in sup],[inf *)
ndefinition inrange_w32 ≝
λx,inf,sup:word32.
 match le_w32 inf sup with
  [ true ⇒ and_bool | false ⇒ or_bool ]
 (le_w32 inf x) (le_w32 x sup).

(* operatore moltiplicazione senza segno *)
(* 〈a1,a2〉 * 〈b1,b2〉 = (a1*b1) x0 x0 + x0 (a1*b2) x0 + x0 (a2*b1) x0 + x0 x0 (a2*b2) *)
ndefinition mulu_w16_aux ≝
λw.nat_it ? rol_w32 w nat8.

ndefinition mulu_w16 ≝
λw1,w2:word16.
 plus_w32_d_d 〈(mulu_b8 (cnH ? w1) (cnH ? w2)).〈〈x0,x0〉:〈x0,x0〉〉〉
 (plus_w32_d_d (mulu_w16_aux (extu_w32 (mulu_b8 (cnH ? w1) (cnL ? w2))))
  (plus_w32_d_d (mulu_w16_aux (extu_w32 (mulu_b8 (cnL ? w1) (cnH ? w2))))
                (extu_w32 (mulu_b8 (cnL ? w1) (cnL ? w2))))).

(* operatore moltiplicazione con segno *)
(* x * y = sgn(x) * sgn(y) * |x| * |y| *)
ndefinition muls_w16 ≝
λw1,w2:word16.
(* ++/-- → +, +-/-+ → - *)
 match (getMSB_w16 w1) ⊙ (getMSB_w16 w2) with
  (* +- -+ → - *)
  [ true ⇒ compl_w32
  (* ++/-- → + *)
  | false ⇒ λx.x ] (mulu_w16 (abs_w16 w1) (abs_w16 w2)).

nlemma pippo : ∃b.b=(muls_w16 〈〈xC,x3〉:〈x0,x4〉〉 〈〈x7,xE〉:〈xF,x9〉〉). nnormalize;

