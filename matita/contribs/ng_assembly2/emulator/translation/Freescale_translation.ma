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
(* TRADUZIONE MCU+PSEUDO+MODALITA'+ARGOMENTI → ESADECIMALE *)
(* ******************************************************* *)

(* introduzione di un tipo dipendente (dalla modalita') per gli argomenti *)
ninductive Freescale_MA_check : Freescale_instr_mode → Type ≝
  maINH              : Freescale_MA_check MODE_INH
| maINHA             : Freescale_MA_check MODE_INHA
| maINHX             : Freescale_MA_check MODE_INHX
| maINHH             : Freescale_MA_check MODE_INHH
| maINHX0ADD         : Freescale_MA_check MODE_INHX0ADD
| maINHX1ADD         : byte8 → Freescale_MA_check MODE_INHX1ADD
| maINHX2ADD         : word16 → Freescale_MA_check MODE_INHX2ADD
| maIMM1             : byte8  → Freescale_MA_check MODE_IMM1
| maIMM1EXT          : byte8  → Freescale_MA_check MODE_IMM1EXT
| maIMM2             : word16 → Freescale_MA_check MODE_IMM2
| maDIR1             : byte8  → Freescale_MA_check MODE_DIR1
| maDIR2             : word16 → Freescale_MA_check MODE_DIR2
| maIX0              : Freescale_MA_check MODE_IX0
| maIX1              : byte8  → Freescale_MA_check MODE_IX1
| maIX2              : word16 → Freescale_MA_check MODE_IX2
| maSP1              : byte8  → Freescale_MA_check MODE_SP1
| maSP2              : word16 → Freescale_MA_check MODE_SP2
| maDIR1_to_DIR1     : byte8 → byte8 → Freescale_MA_check MODE_DIR1_to_DIR1
| maIMM1_to_DIR1     : byte8 → byte8 → Freescale_MA_check MODE_IMM1_to_DIR1
| maIX0p_to_DIR1     : byte8 → Freescale_MA_check MODE_IX0p_to_DIR1
| maDIR1_to_IX0p     : byte8 → Freescale_MA_check MODE_DIR1_to_IX0p
| maINHA_and_IMM1    : byte8 → Freescale_MA_check MODE_INHA_and_IMM1
| maINHX_and_IMM1    : byte8 → Freescale_MA_check MODE_INHX_and_IMM1
| maIMM1_and_IMM1    : byte8 → byte8 → Freescale_MA_check MODE_IMM1_and_IMM1
| maDIR1_and_IMM1    : byte8 → byte8 → Freescale_MA_check MODE_DIR1_and_IMM1
| maIX0_and_IMM1     : byte8 → Freescale_MA_check MODE_IX0_and_IMM1
| maIX0p_and_IMM1    : byte8 → Freescale_MA_check MODE_IX0p_and_IMM1
| maIX1_and_IMM1     : byte8 → byte8 → Freescale_MA_check MODE_IX1_and_IMM1
| maIX1p_and_IMM1    : byte8 → byte8 → Freescale_MA_check MODE_IX1p_and_IMM1
| maSP1_and_IMM1     : byte8 → byte8 → Freescale_MA_check MODE_SP1_and_IMM1
| maDIRn             : ∀n.byte8 → Freescale_MA_check (MODE_DIRn n)
| maDIRn_and_IMM1    : ∀n.byte8 → byte8 → Freescale_MA_check (MODE_DIRn_and_IMM1 n)
| maTNY              : ∀e.Freescale_MA_check (MODE_TNY e)
| maSRT              : ∀t.Freescale_MA_check (MODE_SRT t)
.

(* picker: trasforma l'argomento necessario in input a bytes_of_pseudo_instr_mode_param:
   MA_check i → list (t_byte8 m) *)
ndefinition Freescale_args_picker ≝
λm.λi:Freescale_instr_mode.λargs:Freescale_MA_check i.
 match args with
  (* inherent: legale se nessun operando *) 
  [ maINH    ⇒ nil ? 
  | maINHA   ⇒ nil ? 
  | maINHX   ⇒ nil ? 
  | maINHH   ⇒ nil ?
  (* inherent address: legale se nessun operando/1 byte/1 word *)
  | maINHX0ADD ⇒ nil ?
  | maINHX1ADD b ⇒ [ TByte m b ]
  | maINHX2ADD w ⇒ [ TByte m (cnH ? w); TByte m (cnL ? w) ] 
  (* _0/1/2: legale se nessun operando/1 byte/1 word *)
  | maIMM1 b ⇒ [ TByte m b ]
  | maIMM1EXT b ⇒ [ TByte m b ]
  | maIMM2 w ⇒ [ TByte m (cnH ? w); TByte m (cnL ? w) ]
  | maDIR1 b ⇒ [ TByte m b ]
  | maDIR2 w ⇒ [ TByte m (cnH ? w); TByte m (cnL ? w) ]
  | maIX0    ⇒ nil ?
  | maIX1 b  ⇒ [ TByte m b ]
  | maIX2 w  ⇒ [ TByte m (cnH ? w); TByte m (cnL ? w) ]
  | maSP1 b  ⇒ [ TByte m b ]
  | maSP2 w  ⇒ [ TByte m (cnH ? w); TByte m (cnL ? w) ]
  (* movimento: legale se 2 operandi byte *)
  | maDIR1_to_DIR1 b1 b2  ⇒ [ TByte m b1 ; TByte m b2 ]
  | maIMM1_to_DIR1 b1 b2  ⇒ [ TByte m b1 ; TByte m b2 ]
  | maIX0p_to_DIR1 b      ⇒ [ TByte m b]
  | maDIR1_to_IX0p b      ⇒ [ TByte m b]
  (* cbeq/dbnz: legale se 1/2 operandi byte *)
  | maINHA_and_IMM1 b     ⇒ [ TByte m b]
  | maINHX_and_IMM1 b     ⇒ [ TByte m b]
  | maIMM1_and_IMM1 b1 b2 ⇒ [ TByte m b1 ; TByte m b2 ]
  | maDIR1_and_IMM1 b1 b2 ⇒ [ TByte m b1 ; TByte m b2 ]
  | maIX0_and_IMM1  b     ⇒ [ TByte m b]
  | maIX0p_and_IMM1 b     ⇒ [ TByte m b]
  | maIX1_and_IMM1  b1 b2 ⇒ [ TByte m b1 ; TByte m b2 ]
  | maIX1p_and_IMM1 b1 b2 ⇒ [ TByte m b1 ; TByte m b2 ]
  | maSP1_and_IMM1  b1 b2 ⇒ [ TByte m b1 ; TByte m b2 ]
  (* DIRn: legale se 1 operando byte *)
  | maDIRn _ b ⇒ [ TByte m b]
  (* DIRn_and_IMM1: legale se 2 operandi byte *)
  | maDIRn_and_IMM1 _ b1 b2 ⇒ [ TByte m b1 ; TByte m b2 ]
  (* TNY: legale se nessun operando *)
  | maTNY _ ⇒ nil ?
  (* SRT: legale se nessun operando *)
  | maSRT _ ⇒ nil ?
  ].
