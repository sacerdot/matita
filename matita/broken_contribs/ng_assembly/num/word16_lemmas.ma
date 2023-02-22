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
include "num/byte8_lemmas.ma".

(* **** *)
(* WORD *)
(* **** *)

ndefinition word16_destruct_1 ≝ cn_destruct_1 word16.
ndefinition word16_destruct_2 ≝ cn_destruct_2 word16.

ndefinition symmetric_eqw16 ≝ symmetric_eqcn ? eq_b8 symmetric_eqb8.

ndefinition eqw16_to_eq ≝ eqcn_to_eq ? eq_b8 eqb8_to_eq.
ndefinition eq_to_eqw16 ≝ eq_to_eqcn ? eq_b8 eq_to_eqb8.

ndefinition decidable_w16 ≝ decidable_cn ? decidable_b8.

ndefinition neqw16_to_neq ≝ neqcn_to_neq ? eq_b8 neqb8_to_neq.
ndefinition neq_to_neqw16 ≝ neq_to_neqcn ? eq_b8 neq_to_neqb8 decidable_b8.
