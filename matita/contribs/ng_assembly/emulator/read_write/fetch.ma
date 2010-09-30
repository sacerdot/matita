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

include "emulator/memory/memory_abs.ma".
include "emulator/translation/translation.ma".
include "emulator/status/status_getter.ma".

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

(* opcode a byte : HC05 / RS08 *)
ndefinition fetch_byte ≝
λm:mcu_type.λfR:word32 → option byte8.λpc:word16.
 match fR (extu_w32 pc) with
  [ None ⇒ FetchERR ? ILL_FETCH_AD
  | Some bh ⇒ fetch_byte_aux m (succ_w16 pc) bh ].

(* opcode a byte o 0x9E + byte : HC08 / HCS08 *)
ndefinition Freescale_fetch_byte_or_word ≝
λm:mcu_type.λfR:word32 → option byte8.λpc:word16.
 match fR (extu_w32 pc) with
  [ None ⇒ FetchERR ? ILL_FETCH_AD
  | Some bh ⇒ match eq_b8 bh 〈x9,xE〉 with
   [ true ⇒ match fR (extu_w32 (succ_w16 pc)) with
    [ None ⇒ FetchERR ? ILL_FETCH_AD
    | Some bl ⇒ fetch_word_aux m (succ_w16 (succ_w16 pc)) 〈bh:bl〉
    ]
   | false ⇒ fetch_byte_aux m (succ_w16 pc) bh
   ]
  ].

(* opcode a byte o 0x00 + byte : IP2022 *)
(* opcode + operando a dimensione fissa 16bit *)
(* pc word aligned, mappato in 0x02000000-0x0201FFFF *)
ndefinition IP2022_fetch_byte_or_word ≝
λm:mcu_type.λfR:word32 → option byte8.λpc:word16.
 match fR (rol_w32 〈〈〈x0,x1〉:〈x0,x0〉〉.pc〉) with
  [ None ⇒ FetchERR ? ILL_FETCH_AD
  | Some bh ⇒ match eq_b8 bh 〈x0,x0〉 with
   [ true ⇒ match fR (rol_w32 〈〈〈x8,x1〉:〈x0,x0〉〉.pc〉) with
    [ None ⇒ FetchERR ? ILL_FETCH_AD
    | Some bl ⇒ fetch_word_aux m (succ_w16 pc) 〈bh:bl〉
    ]
   | false ⇒ fetch_byte_aux m (succ_w16 pc) bh
   ]
  ].

ndefinition fetch ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m with
  [ HC05 ⇒ fetch_byte
  | HC08 ⇒ Freescale_fetch_byte_or_word
  | HCS08 ⇒ Freescale_fetch_byte_or_word
  | RS08 ⇒ fetch_byte
  | IP2022 ⇒ IP2022_fetch_byte_or_word
  ] m (mem_read t (mem_desc … s) (chk_desc … s)) (get_pc_reg … s).
