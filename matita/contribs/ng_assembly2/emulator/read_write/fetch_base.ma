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

include "emulator/translation/translation.ma".

(* errori possibili nel fetch OPCODE / ILLEGAL ADDRESS *)
ninductive error_type : Type ≝
  ILL_OP: error_type
| ILL_FETCH_AD: error_type
.

(* - errore: interessa solo l'errore
   - ok: interessa info, nuovo pc *)
ninductive fetch_result (A:Type) : Type ≝
  FetchERR : error_type → fetch_result A
| FetchOK  : A → word16 → fetch_result A.

ndefinition fetch_byte_aux ≝
λm:mcu_type.λcur_pc:word16.λbh:byte8.
 match full_info_of_word16 m (Byte bh) with
  [ None ⇒ FetchERR ? ILL_FETCH_AD
  | Some info ⇒ FetchOK ? info cur_pc
  ].

ndefinition fetch_word_aux ≝
λm:mcu_type.λcur_pc:word16.λw:word16.
 match full_info_of_word16 m (Word w) with
  [ None ⇒ FetchERR ? ILL_FETCH_AD
  | Some info ⇒ FetchOK ? info cur_pc
  ].
