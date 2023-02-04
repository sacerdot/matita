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

include "emulator/read_write/fetch_base.ma".
include "emulator/status/status.ma".

(* opcode a byte : HC05 / RS08 *)
(* caricamento solo da segmento 0 *)
ndefinition fetch_byte ≝
λm,t.λs:any_status m t.λpc:word16.
 match mem_read t (mem_desc … s) (chk_desc … s) o0 pc with
  [ None ⇒ FetchERR ? ILL_FETCH_AD
  | Some bh ⇒ fetch_byte_aux m (succc ? pc) bh ].

(* opcode a byte o 0x9E + byte : HC08 / HCS08 *)
(* caricamento solo da segmento 0 *)
ndefinition Freescale_fetch_byte_or_word ≝
λm,t.λs:any_status m t.λpc:word16.
 match mem_read t (mem_desc … s) (chk_desc … s) o0 pc with
  [ None ⇒ FetchERR ? ILL_FETCH_AD
  | Some bh ⇒ match eqc ? bh 〈x9,xE〉 with
   [ true ⇒ match mem_read t (mem_desc … s) (chk_desc … s) o0 (succc ? pc) with
    [ None ⇒ FetchERR ? ILL_FETCH_AD
    | Some bl ⇒ fetch_word_aux m (succc ? (succc ? pc)) 〈bh:bl〉
    ]
   | false ⇒ fetch_byte_aux m (succc ? pc) bh
   ]
  ].
