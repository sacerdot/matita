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

include "num/exadecim.ma".
include "num/bitrigesim.ma".

(* ********************************************** *)
(* MATTONI BASE PER DEFINIRE LE TABELLE DELLE MCU *)
(* ********************************************** *)

(* enumerazione delle modalita' di indirizzamento = caricamento degli operandi *)
ninductive Freescale_instr_mode: Type ≝
  (* INHERENT = nessun operando *)
  MODE_INH  : Freescale_instr_mode
  (* INHERENT = nessun operando (A implicito) *)
| MODE_INHA : Freescale_instr_mode
  (* INHERENT = nessun operando (X implicito) *)
| MODE_INHX : Freescale_instr_mode
  (* INHERENT = nessun operando (H implicito) *)
| MODE_INHH : Freescale_instr_mode

  (* INHERENT_ADDRESS = nessun operando (HX implicito) *)
| MODE_INHX0ADD : Freescale_instr_mode
  (* INHERENT_ADDRESS = nessun operando (HX implicito+0x00bb) *)
| MODE_INHX1ADD : Freescale_instr_mode
  (* INHERENT_ADDRESS = nessun operando (HX implicito+0xwwww) *)
| MODE_INHX2ADD : Freescale_instr_mode

  (* IMMEDIATE = operando valore immediato byte = 0xbb *)
| MODE_IMM1 : Freescale_instr_mode
  (* IMMEDIATE_EXT = operando valore immediato byte = 0xbb -> esteso a word *)
| MODE_IMM1EXT : Freescale_instr_mode
  (* IMMEDIATE = operando valore immediato word = 0xwwww *)
| MODE_IMM2 : Freescale_instr_mode
  (* DIRECT = operando offset byte = [0x00bb] *)
| MODE_DIR1 : Freescale_instr_mode
  (* DIRECT = operando offset word = [0xwwww] *)
| MODE_DIR2 : Freescale_instr_mode
  (* INDEXED = nessun operando (implicito [X] *)
| MODE_IX0  : Freescale_instr_mode
  (* INDEXED = operando offset relativo byte = [X+0x00bb] *)
| MODE_IX1  : Freescale_instr_mode
  (* INDEXED = operando offset relativo word = [X+0xwwww] *)
| MODE_IX2  : Freescale_instr_mode
  (* INDEXED = operando offset relativo byte = [SP+0x00bb] *)
| MODE_SP1  : Freescale_instr_mode
  (* INDEXED = operando offset relativo word = [SP+0xwwww] *)
| MODE_SP2  : Freescale_instr_mode

  (* DIRECT → DIRECT = carica da diretto/scrive su diretto *)
| MODE_DIR1_to_DIR1 : Freescale_instr_mode
  (* IMMEDIATE → DIRECT = carica da immediato/scrive su diretto *)
| MODE_IMM1_to_DIR1 : Freescale_instr_mode
  (* INDEXED++ → DIRECT = carica da [X]/scrive su diretto/H:X++ *)
| MODE_IX0p_to_DIR1 : Freescale_instr_mode
  (* DIRECT → INDEXED++ = carica da diretto/scrive su [X]/H:X++ *)
| MODE_DIR1_to_IX0p : Freescale_instr_mode

  (* INHERENT(A) + IMMEDIATE *)
| MODE_INHA_and_IMM1 : Freescale_instr_mode
  (* INHERENT(X) + IMMEDIATE *)
| MODE_INHX_and_IMM1 : Freescale_instr_mode
  (* IMMEDIATE + IMMEDIATE *)
| MODE_IMM1_and_IMM1 : Freescale_instr_mode
  (* DIRECT + IMMEDIATE *)
| MODE_DIR1_and_IMM1 : Freescale_instr_mode
  (* INDEXED + IMMEDIATE *)
| MODE_IX0_and_IMM1  : Freescale_instr_mode
  (* INDEXED++ + IMMEDIATE *)
| MODE_IX0p_and_IMM1 : Freescale_instr_mode
  (* INDEXED + IMMEDIATE *)
| MODE_IX1_and_IMM1  : Freescale_instr_mode
  (* INDEXED++ + IMMEDIATE *)
| MODE_IX1p_and_IMM1 : Freescale_instr_mode
  (* INDEXED + IMMEDIATE *)
| MODE_SP1_and_IMM1  : Freescale_instr_mode

  (* DIRECT(mTNY) = operando offset byte(maschera scrittura implicita 3 bit) *)
  (* ex: DIR3 e' carica b, scrivi b con n-simo bit modificato *)
| MODE_DIRn          : oct → Freescale_instr_mode
  (* DIRECT(mTNY) + IMMEDIATE = operando offset byte(maschera lettura implicita 3 bit) *)
  (*                            + operando valore immediato byte  *)
  (* ex: DIR2_and_IMM1 e' carica b, carica imm, restituisci n-simo bit di b + imm *)
| MODE_DIRn_and_IMM1 : oct → Freescale_instr_mode
  (* TINY = nessun operando (diretto implicito 4bit = [0x00000000:0000iiii]) *)
| MODE_TNY           : exadecim → Freescale_instr_mode
  (* SHORT = nessun operando (diretto implicito 5bit = [0x00000000:000iiiii]) *)
| MODE_SRT           : bitrigesim → Freescale_instr_mode
.

ndefinition eq_Freescale_im ≝
λi1,i2:Freescale_instr_mode.
 match i1 with
  [ MODE_INH ⇒ match i2 with [ MODE_INH ⇒ true | _ ⇒ false ]
  | MODE_INHA ⇒ match i2 with [ MODE_INHA ⇒ true | _ ⇒ false ]
  | MODE_INHX ⇒ match i2 with [ MODE_INHX ⇒ true | _ ⇒ false ]
  | MODE_INHH ⇒ match i2 with [ MODE_INHH ⇒ true | _ ⇒ false ]
  | MODE_INHX0ADD ⇒ match i2 with [ MODE_INHX0ADD ⇒ true | _ ⇒ false ]
  | MODE_INHX1ADD ⇒ match i2 with [ MODE_INHX1ADD ⇒ true | _ ⇒ false ]
  | MODE_INHX2ADD ⇒ match i2 with [ MODE_INHX2ADD ⇒ true | _ ⇒ false ]
  | MODE_IMM1 ⇒ match i2 with [ MODE_IMM1 ⇒ true | _ ⇒ false ]
  | MODE_IMM1EXT ⇒ match i2 with [ MODE_IMM1EXT ⇒ true | _ ⇒ false ]
  | MODE_IMM2 ⇒ match i2 with [ MODE_IMM2 ⇒ true | _ ⇒ false ]
  | MODE_DIR1 ⇒ match i2 with [ MODE_DIR1 ⇒ true | _ ⇒ false ]
  | MODE_DIR2 ⇒ match i2 with [ MODE_DIR2 ⇒ true | _ ⇒ false ]
  | MODE_IX0 ⇒ match i2 with [ MODE_IX0 ⇒ true | _ ⇒ false ]
  | MODE_IX1 ⇒ match i2 with [ MODE_IX1 ⇒ true | _ ⇒ false ]
  | MODE_IX2 ⇒ match i2 with [ MODE_IX2 ⇒ true | _ ⇒ false ]
  | MODE_SP1 ⇒ match i2 with [ MODE_SP1 ⇒ true | _ ⇒ false ]
  | MODE_SP2 ⇒ match i2 with [ MODE_SP2 ⇒ true | _ ⇒ false ]  
  | MODE_DIR1_to_DIR1 ⇒ match i2 with [ MODE_DIR1_to_DIR1 ⇒ true | _ ⇒ false ]
  | MODE_IMM1_to_DIR1 ⇒ match i2 with [ MODE_IMM1_to_DIR1 ⇒ true | _ ⇒ false ]
  | MODE_IX0p_to_DIR1 ⇒ match i2 with [ MODE_IX0p_to_DIR1 ⇒ true | _ ⇒ false ]
  | MODE_DIR1_to_IX0p ⇒ match i2 with [ MODE_DIR1_to_IX0p ⇒ true | _ ⇒ false ]
  | MODE_INHA_and_IMM1 ⇒ match i2 with [ MODE_INHA_and_IMM1 ⇒ true | _ ⇒ false ]
  | MODE_INHX_and_IMM1 ⇒ match i2 with [ MODE_INHX_and_IMM1 ⇒ true | _ ⇒ false ]
  | MODE_IMM1_and_IMM1 ⇒ match i2 with [ MODE_IMM1_and_IMM1 ⇒ true | _ ⇒ false ]  
  | MODE_DIR1_and_IMM1 ⇒ match i2 with [ MODE_DIR1_and_IMM1 ⇒ true | _ ⇒ false ]  
  | MODE_IX0_and_IMM1 ⇒ match i2 with [ MODE_IX0_and_IMM1 ⇒ true | _ ⇒ false ]  
  | MODE_IX0p_and_IMM1 ⇒ match i2 with [ MODE_IX0p_and_IMM1 ⇒ true | _ ⇒ false ]  
  | MODE_IX1_and_IMM1 ⇒ match i2 with [ MODE_IX1_and_IMM1 ⇒ true | _ ⇒ false ]  
  | MODE_IX1p_and_IMM1 ⇒ match i2 with [ MODE_IX1p_and_IMM1 ⇒ true | _ ⇒ false ]
  | MODE_SP1_and_IMM1 ⇒ match i2 with [ MODE_SP1_and_IMM1 ⇒ true | _ ⇒ false ]
  | MODE_DIRn n1 ⇒ match i2 with [ MODE_DIRn n2 ⇒ eqc ? n1 n2 | _ ⇒ false ]  
  | MODE_DIRn_and_IMM1 n1 ⇒ match i2 with [ MODE_DIRn_and_IMM1 n2  ⇒ eqc ? n1 n2 | _ ⇒ false ]
  | MODE_TNY e1 ⇒ match i2 with [ MODE_TNY e2 ⇒ eqc ? e1 e2 | _ ⇒ false ]  
  | MODE_SRT t1 ⇒ match i2 with [ MODE_SRT t2 ⇒ eqc ? t1 t2 | _ ⇒ false ]  
  ].     

ndefinition forall_Freescale_im ≝ λP:Freescale_instr_mode → bool.
  P MODE_INH
⊗ P MODE_INHA
⊗ P MODE_INHX
⊗ P MODE_INHH

⊗ P MODE_INHX0ADD
⊗ P MODE_INHX1ADD
⊗ P MODE_INHX2ADD

⊗ P MODE_IMM1
⊗ P MODE_IMM1EXT
⊗ P MODE_IMM2
⊗ P MODE_DIR1
⊗ P MODE_DIR2
⊗ P MODE_IX0
⊗ P MODE_IX1
⊗ P MODE_IX2
⊗ P MODE_SP1
⊗ P MODE_SP2

⊗ P MODE_DIR1_to_DIR1
⊗ P MODE_IMM1_to_DIR1
⊗ P MODE_IX0p_to_DIR1
⊗ P MODE_DIR1_to_IX0p

⊗ P MODE_INHA_and_IMM1
⊗ P MODE_INHX_and_IMM1
⊗ P MODE_IMM1_and_IMM1
⊗ P MODE_DIR1_and_IMM1
⊗ P MODE_IX0_and_IMM1
⊗ P MODE_IX0p_and_IMM1
⊗ P MODE_IX1_and_IMM1
⊗ P MODE_IX1p_and_IMM1
⊗ P MODE_SP1_and_IMM1

⊗ forallc ? (λo. P (MODE_DIRn o))
⊗ forallc ? (λo. P (MODE_DIRn_and_IMM1 o))
⊗ forallc ? (λe. P (MODE_TNY e))
⊗ forallc ? (λt. P (MODE_SRT t)).
