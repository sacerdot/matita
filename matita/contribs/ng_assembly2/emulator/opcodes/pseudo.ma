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

ndefinition pseudo_is_comparable: mcu_type → comparable.
 #mcu; @ (aux_pseudo_type mcu)
  ##[ nelim mcu;
      ##[ ##1,2,3,4: napply (zeroc Freescalepseudo_is_comparable)
      ##| ##5: napply (zeroc IP2022pseudo_is_comparable) ##]
  ##| nelim mcu;
      ##[ ##1,2,3,4: napply (forallc Freescalepseudo_is_comparable)
      ##| ##5:  napply (forallc IP2022pseudo_is_comparable) ##]
  ##| nelim mcu;
      ##[ ##1,2,3,4: napply (eqc Freescalepseudo_is_comparable)
      ##| ##5: napply (eqc IP2022pseudo_is_comparable) ##]
  ##| nelim mcu;
      ##[ ##1,2,3,4: napply (eqc_to_eq Freescalepseudo_is_comparable)
      ##| ##5: napply (eqc_to_eq IP2022pseudo_is_comparable) ##]
  ##| nelim mcu;
      ##[ ##1,2,3,4: napply (eq_to_eqc Freescalepseudo_is_comparable)
      ##| ##5: napply (eq_to_eqc IP2022pseudo_is_comparable) ##]
  ##| nelim mcu;
      ##[ ##1,2,3,4: napply (neqc_to_neq Freescalepseudo_is_comparable)
      ##| ##5: napply (neqc_to_neq IP2022pseudo_is_comparable) ##]
  ##| nelim mcu;
      ##[ ##1,2,3,4: napply (neq_to_neqc Freescalepseudo_is_comparable)
      ##| ##5: napply (neq_to_neqc IP2022pseudo_is_comparable) ##]
  ##| nelim mcu;
      ##[ ##1,2,3,4: napply (decidable_c Freescalepseudo_is_comparable)
      ##| ##5: napply (decidable_c IP2022pseudo_is_comparable) ##]
  ##| nelim mcu;
      ##[ ##1,2,3,4: napply (symmetric_eqc Freescalepseudo_is_comparable)
      ##| ##5: napply (symmetric_eqc IP2022pseudo_is_comparable) ##]
  ##]
nqed.

unification hint 0 ≔ M:mcu_type ⊢ carr (pseudo_is_comparable M) ≡ aux_pseudo_type M.

ndefinition aux_im_type ≝
λmcu:mcu_type.match mcu with
 [ HC05 ⇒ Freescale_instr_mode
 | HC08 ⇒ Freescale_instr_mode
 | HCS08 ⇒ Freescale_instr_mode
 | RS08 ⇒ Freescale_instr_mode
 | IP2022 ⇒ IP2022_instr_mode
 ].

ndefinition im_is_comparable: mcu_type → comparable.
 #mcu; @ (aux_im_type mcu)
  ##[ nelim mcu;
      ##[ ##1,2,3,4: napply (zeroc Freescaleim_is_comparable)
      ##| ##5: napply (zeroc IP2022im_is_comparable) ##]
  ##| nelim mcu;
      ##[ ##1,2,3,4: napply (forallc Freescaleim_is_comparable)
      ##| ##5:  napply (forallc IP2022im_is_comparable) ##]
  ##| nelim mcu;
      ##[ ##1,2,3,4: napply (eqc Freescaleim_is_comparable)
      ##| ##5: napply (eqc IP2022im_is_comparable) ##]
  ##| nelim mcu;
      ##[ ##1,2,3,4: napply (eqc_to_eq Freescaleim_is_comparable)
      ##| ##5: napply (eqc_to_eq IP2022im_is_comparable) ##]
  ##| nelim mcu;
      ##[ ##1,2,3,4: napply (eq_to_eqc Freescaleim_is_comparable)
      ##| ##5: napply (eq_to_eqc IP2022im_is_comparable) ##]
  ##| nelim mcu;
      ##[ ##1,2,3,4: napply (neqc_to_neq Freescaleim_is_comparable)
      ##| ##5: napply (neqc_to_neq IP2022im_is_comparable) ##]
  ##| nelim mcu;
      ##[ ##1,2,3,4: napply (neq_to_neqc Freescaleim_is_comparable)
      ##| ##5: napply (neq_to_neqc IP2022im_is_comparable) ##]
  ##| nelim mcu;
      ##[ ##1,2,3,4: napply (decidable_c Freescaleim_is_comparable)
      ##| ##5: napply (decidable_c IP2022im_is_comparable) ##]
  ##| nelim mcu;
      ##[ ##1,2,3,4: napply (symmetric_eqc Freescaleim_is_comparable)
      ##| ##5: napply (symmetric_eqc IP2022im_is_comparable) ##]
  ##]
nqed.

unification hint 0 ≔ M:mcu_type ⊢ carr (im_is_comparable M) ≡ aux_im_type M.

(* ********************************************* *)
(* STRUMENTI PER LE DIMOSTRAZIONI DI CORRETTEZZA *)
(* ********************************************* *)

ndefinition aux_table_type ≝ λmcu:mcu_type.Prod4T (aux_pseudo_type mcu) (aux_im_type mcu) byte8_or_word16 nat.

(* su tutta la lista quante volte compare il byte *)
nlet rec get_byte_count (m:mcu_type) (b:byte8) (c:word16) (l:list (aux_table_type m)) on l ≝
 match l with
  [ nil ⇒ c
  | cons hd tl ⇒ match thd4T … hd with
   [ Byte b' ⇒ match eqc ? b b' with
    [ true ⇒ get_byte_count m b (succc ? c) tl
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
   | Word w' ⇒ match eqc ? w w' with
    [ true ⇒ get_word_count m w (succc ? c) tl
    | false ⇒ get_word_count m w c tl
    ]
   ]
  ].

(* su tutta la lista quante volte compare lo pseudocodice *)
nlet rec get_pseudo_count (m:mcu_type) (o:aux_pseudo_type m) (c:word16) (l:list (aux_table_type m)) on l ≝
 match l with
  [ nil ⇒ c
  | cons hd tl ⇒ match eqc ? o (fst4T … hd) with
   [ true ⇒ get_pseudo_count m o (succc ? c) tl
   | false ⇒ get_pseudo_count m o c tl
   ]
  ].

(* su tutta la lista quante volte compare la modalita' *)
nlet rec get_mode_count (m:mcu_type) (i:aux_im_type m) (c:word16) (l:list (aux_table_type m)) on l ≝
 match l with
  [ nil ⇒ c
  | cons hd tl ⇒ match eqc ? i (snd4T … hd) with
   [ true ⇒ get_mode_count m i (succc ? c) tl
   | false ⇒ get_mode_count m i c tl
   ]
  ].

(* b e' non implementato? *)
nlet rec test_not_impl_byte (b:byte8) (l:list byte8) on l ≝
 match l with
  [ nil ⇒ false
  | cons hd tl ⇒ match eqc ? b hd with
   [ true ⇒ true
   | false ⇒ test_not_impl_byte b tl
   ]
  ].

(* su tutta la lista quante volte compare la coppia pseudo,instr_mode *)
nlet rec get_PsIm_count (m:mcu_type) (o:aux_pseudo_type m) (i:aux_im_type m) (c:word16) (l:list (aux_table_type m)) on l ≝
 match l with
  [ nil ⇒ c
  | cons hd tl ⇒
   match (eqc ? o (fst4T … hd)) ⊗
         (eqc ? i (snd4T … hd)) with
    [ true ⇒ get_PsIm_count m o i (succc ? c) tl
    | false ⇒ get_PsIm_count m o i c tl
    ] 
  ].

(* o e' non implementato? *)
nlet rec test_not_impl_pseudo (m:mcu_type) (o:aux_pseudo_type m) (l:list (aux_pseudo_type m)) on l ≝
 match l with
  [ nil ⇒ false
  | cons hd tl ⇒ match eqc ? o hd with
   [ true ⇒ true
   | false ⇒ test_not_impl_pseudo m o tl
   ]
  ].

(* i e' non implementato? *)
nlet rec test_not_impl_mode (m:mcu_type) (i:aux_im_type m) (l:list (aux_im_type m)) on l ≝
 match l with
  [ nil ⇒ false
  | cons hd tl ⇒ match eqc ? i hd with
   [ true ⇒ true
   | false ⇒ test_not_impl_mode m i tl
   ]
  ].
