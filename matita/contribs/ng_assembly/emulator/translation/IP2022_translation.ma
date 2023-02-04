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

include "emulator/translation/translation_base.ma".

(* ******************************************************* *)
(* TRADUZIONE MCU+OPCODE+MODALITA'+ARGOMENTI → ESADECIMALE *)
(* ******************************************************* *)

(* introduzione di un tipo dipendente (dalla modalita') per gli argomenti *)
ninductive IP2022_MA_check : IP2022_instr_mode → Type ≝
  maINH       : IP2022_MA_check MODE_INH
| maIMM3      : ∀n.IP2022_MA_check (MODE_IMM3 n)
| maIMM8      : byte8 → IP2022_MA_check MODE_IMM8
| maIMM13     : ∀t.byte8 → IP2022_MA_check (MODE_IMM13 t)
| maFR0_and_W : byte8 → IP2022_MA_check MODE_FR0_and_W
| maFR1_and_W : byte8 → IP2022_MA_check MODE_FR1_and_W
| maW_and_FR0 : byte8 → IP2022_MA_check MODE_W_and_FR0
| maW_and_FR1 : byte8 → IP2022_MA_check MODE_W_and_FR1
| maFR0n      : ∀n.byte8 → IP2022_MA_check (MODE_FR0n n)
| maFR1n      : ∀n.byte8 → IP2022_MA_check (MODE_FR1n n)
.

(* picker: trasforma l'argomento necessario in input a bytes_of_pseudo_instr_mode_param:
   MA_check i → list (t_byte8 m) *)
ndefinition IP2022_args_picker ≝
λi:IP2022_instr_mode.λargs:IP2022_MA_check i.
 match args with
  [ maINH         ⇒ nil ?
  | maIMM3 _      ⇒ nil ?
  | maIMM8 b      ⇒ [ TByte IP2022 b ]
  | maIMM13 _ b   ⇒ [ TByte IP2022 b ]
  | maFR0_and_W b ⇒ [ TByte IP2022 b ]
  | maFR1_and_W b ⇒ [ TByte IP2022 b ]
  | maW_and_FR0 b ⇒ [ TByte IP2022 b ]
  | maW_and_FR1 b ⇒ [ TByte IP2022 b ]
  | maFR0n _ b    ⇒ [ TByte IP2022 b ]
  | maFR1n _ b    ⇒ [ TByte IP2022 b ]
  ].
