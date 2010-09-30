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

include "emulator/opcodes/pseudo.ma".
include "common/option.ma".
include "emulator/opcodes/HC05_table.ma".
include "emulator/opcodes/HC08_table.ma".
include "emulator/opcodes/HCS08_table.ma".
include "emulator/opcodes/RS08_table.ma".
include "emulator/opcodes/IP2022_table.ma".

(* ***************************** *)
(* TRADUZIONE ESADECIMALE → INFO *)
(* ***************************** *)

(* accesso alla tabella della ALU prescelta *)
ndefinition opcode_table ≝
λm:mcu_type.
 match m
  return λm:mcu_type.list (aux_table_type m)
 with
  [ HC05  ⇒ opcode_table_HC05
  | HC08  ⇒ opcode_table_HC08
  | HCS08 ⇒ opcode_table_HCS08
  | RS08  ⇒ opcode_table_RS08
  | IP2022 ⇒ opcode_table_IP2022
 ].

(* traduzione mcu+esadecimale → info *)
(* NB: la ricerca per byte non matcha con una word con lo stesso byte superiore uguale *)
(* NB: per matchare una word (precode+code) bisogna passare una word *)
(* NB: il risultato e' sempre un'opzione, NON esiste un dummy opcode tipo UNKNOWN/ILLEGAL *)
nlet rec full_info_of_word16_aux (m:mcu_type) (borw:byte8_or_word16) (param:list (aux_table_type m)) on param ≝
 match param with
  [ nil ⇒ None ?
  | cons hd tl ⇒
   match thd4T … hd with
    [ Byte b ⇒ match borw with
     [ Byte borw' ⇒ match eq_b8 borw' b with
      [ true ⇒ Some ? hd
      | false ⇒ full_info_of_word16_aux m borw tl ]
     | Word _ ⇒ full_info_of_word16_aux m borw tl ]
    | Word w ⇒ match borw with
     [ Byte _ ⇒ full_info_of_word16_aux m borw tl
     | Word borw' ⇒ match eq_w16 borw' w with
      [ true ⇒ Some ? hd
      | false ⇒ full_info_of_word16_aux m borw tl ]            
    ]]].

ndefinition full_info_of_word16 ≝
λm:mcu_type.λborw:byte8_or_word16.
full_info_of_word16_aux m borw (opcode_table m).

(* introduzione di un tipo byte8 dipendente dall'mcu_type (phantom type) *)
ninductive t_byte8 (m:mcu_type) : Type ≝
 TByte : byte8 → t_byte8 m.

ndefinition eq_tbyte8 ≝
λm.λtb1,tb2:t_byte8 m.
 match tb1 with
  [ TByte b1 ⇒ match tb2 with
   [ TByte b2 ⇒ eq_b8 b1 b2 ]].
