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

include "num/word32.ma".
include "num/word16_lemmas.ma".

(* ***** *)
(* DWORD *)
(* ***** *)

ndefinition word32_destruct_1 ≝ cn_destruct_1 word32.
ndefinition word32_destruct_2 ≝ cn_destruct_2 word32.

ndefinition symmetric_eqw32 ≝ symmetric_eqcn ? eq_w16 symmetric_eqw16.

ndefinition eqw32_to_eq ≝ eqcn_to_eq ? eq_w16 eqw16_to_eq.
ndefinition eq_to_eqw32 ≝ eq_to_eqcn ? eq_w16 eq_to_eqw16.

ndefinition decidable_w32 ≝ decidable_cn ? decidable_w16.

ndefinition neqw32_to_neq ≝ neqcn_to_neq ? eq_w16 neqw16_to_neq.
ndefinition neq_to_neqw32 ≝ neq_to_neqcn ? eq_w16 neq_to_neqw16 decidable_w16.
