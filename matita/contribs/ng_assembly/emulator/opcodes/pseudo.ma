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

include "emulator/opcodes/Freescale_pseudo.ma".
include "emulator/opcodes/Freescale_instr_mode.ma".
include "emulator/opcodes/IP2022_pseudo.ma".
include "emulator/opcodes/IP2022_instr_mode.ma".
include "emulator/opcodes/byte_or_word.ma".
include "common/list.ma".

(* ********************************************** *)
(* MATTONI BASE PER DEFINIRE LE TABELLE DELLE MCU *)
(* ********************************************** *)

(* enumerazione delle ALU *)
ninductive mcu_type: Type ≝
  HC05   : mcu_type
| HC08   : mcu_type
| HCS08  : mcu_type
| RS08   : mcu_type
| IP2022 : mcu_type.

ndefinition eq_mcutype ≝
λm1,m2:mcu_type.
 match m1 with
  [ HC05 ⇒ match m2 with [ HC05 ⇒ true | _ ⇒ false ]
  | HC08 ⇒ match m2 with [ HC08 ⇒ true | _ ⇒ false ]
  | HCS08 ⇒ match m2 with [ HCS08 ⇒ true | _ ⇒ false ]
  | RS08 ⇒ match m2 with [ RS08 ⇒ true | _ ⇒ false ]
  | IP2022 ⇒ match m2 with [ IP2022 ⇒ true | _ ⇒ false ]
  ].

ndefinition aux_pseudo_type ≝
λmcu:mcu_type.match mcu with
 [ HC05 ⇒ Freescale_pseudo
 | HC08 ⇒ Freescale_pseudo
 | HCS08 ⇒ Freescale_pseudo
 | RS08 ⇒ Freescale_pseudo
 | IP2022 ⇒ IP2022_pseudo
 ].

ndefinition aux_im_type ≝
λmcu:mcu_type.match mcu with
 [ HC05 ⇒ Freescale_instr_mode
 | HC08 ⇒ Freescale_instr_mode
 | HCS08 ⇒ Freescale_instr_mode
 | RS08 ⇒ Freescale_instr_mode
 | IP2022 ⇒ IP2022_instr_mode
 ].

ndefinition eq_pseudo ≝
λmcu:mcu_type.
 match mcu
  return λm.aux_pseudo_type m → aux_pseudo_type m → bool
 with
  [ HC05 ⇒ eq_Freescale_pseudo
  | HC08 ⇒ eq_Freescale_pseudo
  | HCS08 ⇒ eq_Freescale_pseudo
  | RS08 ⇒ eq_Freescale_pseudo
  | IP2022 ⇒ eq_IP2022_pseudo
  ].

ndefinition eq_im ≝
λmcu:mcu_type.
 match mcu
  return λm.aux_im_type m → aux_im_type m → bool
 with
  [ HC05 ⇒ eq_Freescale_im
  | HC08 ⇒ eq_Freescale_im
  | HCS08 ⇒ eq_Freescale_im
  | RS08 ⇒ eq_Freescale_im
  | IP2022 ⇒ eq_IP2022_im
  ].

ndefinition forall_pseudo ≝
λmcu:mcu_type.
 match mcu
  return λm.(aux_pseudo_type m → bool) → bool
 with
  [ HC05 ⇒ forall_Freescale_pseudo
  | HC08 ⇒ forall_Freescale_pseudo
  | HCS08 ⇒ forall_Freescale_pseudo
  | RS08 ⇒ forall_Freescale_pseudo
  | IP2022 ⇒ forall_IP2022_pseudo
  ].

ndefinition forall_im ≝
λmcu:mcu_type.
 match mcu
  return λm.(aux_im_type m → bool) → bool
 with
  [ HC05 ⇒ forall_Freescale_im
  | HC08 ⇒ forall_Freescale_im
  | HCS08 ⇒ forall_Freescale_im
  | RS08 ⇒ forall_Freescale_im
  | IP2022 ⇒ forall_IP2022_im
  ].

(* ********************************************* *)
(* STRUMENTI PER LE DIMOSTRAZIONI DI CORRETTEZZA *)
(* ********************************************* *)

ndefinition aux_table_type ≝ λmcu:mcu_type.Prod4T (aux_pseudo_type mcu) (aux_im_type mcu) byte8_or_word16 byte8.

(* su tutta la lista quante volte compare il byte *)
nlet rec get_byte_count (m:mcu_type) (b:byte8) (c:word16) (l:list (aux_table_type m)) on l ≝
 match l with
  [ nil ⇒ c
  | cons hd tl ⇒ match thd4T … hd with
   [ Byte b' ⇒ match eq_b8 b b' with
    [ true ⇒ get_byte_count m b (succ_w16 c) tl
    | false ⇒ get_byte_count m b c tl
    ]
   | Word _ ⇒ get_byte_count m b c tl
   ]
  ].

(* su tutta la lista quante volte compare la word *)
nlet rec get_word_count (m:mcu_type) (w:word16) (c:word16) (l:list (aux_table_type m)) on l ≝
 match l with
  [ nil ⇒ c
  | cons hd tl ⇒ match thd4T … hd with
   [ Byte _ ⇒ get_word_count m w c tl
   | Word w' ⇒ match eq_w16 w w' with
    [ true ⇒ get_word_count m w (succ_w16 c) tl
    | false ⇒ get_word_count m w c tl
    ]
   ]
  ].

(* su tutta la lista quante volte compare lo pseudocodice *)
nlet rec get_pseudo_count (m:mcu_type) (o:aux_pseudo_type m) (c:word16) (l:list (aux_table_type m)) on l ≝
 match l with
  [ nil ⇒ c
  | cons hd tl ⇒ match eq_pseudo m o (fst4T … hd) with
   [ true ⇒ get_pseudo_count m o (succ_w16 c) tl
   | false ⇒ get_pseudo_count m o c tl
   ]
  ].

(* su tutta la lista quante volte compare la modalita' *)
nlet rec get_mode_count (m:mcu_type) (i:aux_im_type m) (c:word16) (l:list (aux_table_type m)) on l ≝
 match l with
  [ nil ⇒ c
  | cons hd tl ⇒ match eq_im m i (snd4T … hd) with
   [ true ⇒ get_mode_count m i (succ_w16 c) tl
   | false ⇒ get_mode_count m i c tl
   ]
  ].

(* b e' non implementato? *)
nlet rec test_not_impl_byte (b:byte8) (l:list byte8) on l ≝
 match l with
  [ nil ⇒ false
  | cons hd tl ⇒ match eq_b8 b hd with
   [ true ⇒ true
   | false ⇒ test_not_impl_byte b tl
   ]
  ].

(* su tutta la lista quante volte compare la coppia pseudo,instr_mode *)
nlet rec get_PsIm_count (m:mcu_type) (o:aux_pseudo_type m) (i:aux_im_type m) (c:word16) (l:list (aux_table_type m)) on l ≝
 match l with
  [ nil ⇒ c
  | cons hd tl ⇒
   match (eq_pseudo m o (fst4T … hd)) ⊗
         (eq_im m i (snd4T … hd)) with
    [ true ⇒ get_PsIm_count m o i (succ_w16 c) tl
    | false ⇒ get_PsIm_count m o i c tl
    ] 
  ].

(* o e' non implementato? *)
nlet rec test_not_impl_pseudo (m:mcu_type) (o:aux_pseudo_type m) (l:list (aux_pseudo_type m)) on l ≝
 match l with
  [ nil ⇒ false
  | cons hd tl ⇒ match eq_pseudo m o hd with
   [ true ⇒ true
   | false ⇒ test_not_impl_pseudo m o tl
   ]
  ].

(* i e' non implementato? *)
nlet rec test_not_impl_mode (m:mcu_type) (i:aux_im_type m) (l:list (aux_im_type m)) on l ≝
 match l with
  [ nil ⇒ false
  | cons hd tl ⇒ match eq_im m i hd with
   [ true ⇒ true
   | false ⇒ test_not_impl_mode m i tl
   ]
  ].
