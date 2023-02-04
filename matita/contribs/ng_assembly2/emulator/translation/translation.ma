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

include "emulator/translation/Freescale_translation.ma".
include "emulator/translation/IP2022_translation.ma".

(* ******************************************************* *)
(* TRADUZIONE MCU+OPCODE+MODALITA'+ARGOMENTI → ESADECIMALE *)
(* ******************************************************* *)

(* introduzione di un tipo dipendente (dalla modalita') per gli argomenti *)
ndefinition MA_check ≝
λmcu:mcu_type.
 match mcu
  return λm.(aux_im_type m) → Type
 with
  [ HC05 ⇒ Freescale_MA_check
  | HC08 ⇒ Freescale_MA_check
  | HCS08 ⇒ Freescale_MA_check
  | RS08 ⇒ Freescale_MA_check
  | IP2022 ⇒ IP2022_MA_check
  ].

(* picker: trasforma l'argomento necessario in input a bytes_of_pseudo_instr_mode_param:
   MA_check i → list (t_byte8 m) *)
ndefinition args_picker ≝
λmcu:mcu_type.
 match mcu
  return λm.Πi:(aux_im_type m).MA_check m i → ?
 with
  [ HC05 ⇒ Freescale_args_picker HC05
  | HC08 ⇒ Freescale_args_picker HC08
  | HCS08 ⇒ Freescale_args_picker HCS08
  | RS08 ⇒ Freescale_args_picker RS08
  | IP2022 ⇒ IP2022_args_picker
  ].

(* trasformatore finale: mcu+opcode+instr_mode+args → list (t_byte8 m) *)
nlet rec bytes_of_pseudo_instr_mode_param_aux (m:mcu_type) (o:aux_pseudo_type m) (i:aux_im_type m) (p:MA_check m i)
                                             (param:list (aux_table_type m)) on param ≝
 match param with
 [ nil ⇒ None ? | cons hd tl ⇒
  match (eqc ? o (fst4T … hd)) ⊗ (eqc ? i (snd4T … hd)) with
   [ true ⇒ match thd4T … hd with 
    [ Byte isab ⇒ 
     Some ? ([ (TByte m isab) ]@(args_picker m i p))
    | Word isaw ⇒
     Some ? ([ (TByte m (cnH ? isaw)) ; (TByte m (cnL ? isaw)) ]@(args_picker m i p))
    ]
   | false ⇒ bytes_of_pseudo_instr_mode_param_aux m o i p tl ]].

ndefinition bytes_of_pseudo_instr_mode_param ≝
λm:mcu_type.λo:aux_pseudo_type m.λi:aux_im_type m.λp:MA_check m i.
bytes_of_pseudo_instr_mode_param_aux m o i p (opcode_table m).

(* ****************************** *)
(* APPROCCIO COMPILAZIONE AL VOLO *)
(* ****************************** *)

(* ausiliario di compile *)
ndefinition defined_option ≝
 λT:Type.λo:option T.
  match o with
   [ None ⇒ False
   | Some _ ⇒ True
   ].

(* compila solo se l'intera istruzione+modalita'+argomenti ha riscontro nelle tabelle *)
ndefinition compile ≝
λmcu:mcu_type.λi:aux_im_type mcu.λop:aux_pseudo_type mcu.λarg:MA_check mcu i.
 match bytes_of_pseudo_instr_mode_param mcu op i arg
  return λres:option ?.defined_option ? res → ?
 with
  [ None ⇒ λp:defined_option ? (None ?).False_rect_Type0 ? p
  | Some x ⇒ λp:defined_option ? (Some ? x).x
  ].

(* detipatore del compilato: (t_byte8 m) → byte8 *)
nlet rec source_to_byte8_aux (m:mcu_type) (p2:list byte8) (p1:list (t_byte8 m))  on p1 ≝
 match p1 with
  [ nil ⇒ p2
  | cons hd tl ⇒ match hd with [ TByte b ⇒ source_to_byte8_aux m (p2@[b]) tl ]
  ].

ndefinition source_to_byte8 ≝ λm:mcu_type.source_to_byte8_aux m [].
