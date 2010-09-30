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

(* PC word aligned *)
(* PC < 0x8000 → segmento 1 program ram *)
(*else         → segmento 2 program flash *)
ndefinition IP2022_pc_flashtest ≝
λpc:word16.getMSBc ? pc.

ndefinition IP2022_pc_translation ≝
λpc:word16.match shlc ? pc with
 [ pair msb pc' ⇒ pair …
  match msb with [ true ⇒ o2 | false ⇒ o1 ] pc' ].

(* opcode a byte o 0x00 + byte : IP2022 *)
(* opcode + operando a dimensione fissa 16bit *)
ndefinition IP2022_fetch_byte_or_word ≝
λm,t.λs:any_status m t.λpc:word16.
 match mem_read t (mem_desc … s) (chk_desc … s)
                (fst … (IP2022_pc_translation pc))
                (snd … (IP2022_pc_translation pc)) with
  [ None ⇒ FetchERR ? ILL_FETCH_AD
  | Some bh ⇒ match eqc ? bh 〈x0,x0〉 with
   [ true ⇒ match mem_read t (mem_desc … s) (chk_desc … s)
                             (fst … (IP2022_pc_translation pc))
                             (succc ? (snd … (IP2022_pc_translation pc))) with
    [ None ⇒ FetchERR ? ILL_FETCH_AD
    | Some bl ⇒ fetch_word_aux m (succc ? pc) 〈bh:bl〉
    ]
   | false ⇒ fetch_byte_aux m (succc ? pc) bh
   ]
  ].
