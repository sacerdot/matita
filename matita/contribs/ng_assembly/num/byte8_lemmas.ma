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
include "num/exadecim_lemmas.ma".
include "num/comp_num_lemmas.ma".

(* **** *)
(* BYTE *)
(* **** *)

ndefinition byte8_destruct_1 ≝ cn_destruct_1 byte8.
ndefinition byte8_destruct_2 ≝ cn_destruct_2 byte8.

ndefinition symmetric_eqb8 ≝ symmetric_eqcn ? eq_ex symmetric_eqex.

ndefinition eqb8_to_eq ≝ eqcn_to_eq ? eq_ex eqex_to_eq.
ndefinition eq_to_eqb8 ≝ eq_to_eqcn ? eq_ex eq_to_eqex.

ndefinition decidable_b8 ≝ decidable_cn ? decidable_ex.

ndefinition neqb8_to_neq ≝ neqcn_to_neq ? eq_ex neqex_to_neq.
ndefinition neq_to_neqb8 ≝ neq_to_neqcn ? eq_ex neq_to_neqex decidable_ex.
