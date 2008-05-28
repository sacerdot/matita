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
(*                           Progetto FreeScale                           *)
(*                                                                        *)
(* Sviluppato da:                                                         *)
(*   Cosimo Oliboni, oliboni@cs.unibo.it                                  *)
(*                                                                        *)
(* Questo materiale fa parte della tesi:                                  *)
(*   "Formalizzazione Interattiva dei Microcontroller a 8bit FreeScale"   *)
(*                                                                        *)
(*                    data ultima modifica 15/11/2007                     *)
(* ********************************************************************** *)

include "freescale/opcode.ma".

(* ****************** *)
(* TABELLA DELL'HCS08 *)
(* ****************** *)

(* definizione come concatenazione finale di liste per velocizzare il parsing *)
(* ogni riga e' (any_opcode m) (instr_mode) (opcode esadecimale) (#cicli esecuzione) *)
(* NB: l'uso di any_opcode m + concatenazione finale tutte liste
       impedisce di introdurre opcode disomogenei (per mcu) *)

definition opcode_table_HCS08_1 ≝
[
  quadrupleT ???? (anyOP HCS08 ADC) MODE_IMM1 (Byte 〈xA,x9〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 ADC) MODE_DIR1 (Byte 〈xB,x9〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 ADC) MODE_DIR2 (Byte 〈xC,x9〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 ADC) MODE_IX2  (Byte 〈xD,x9〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 ADC) MODE_IX1  (Byte 〈xE,x9〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 ADC) MODE_IX0  (Byte 〈xF,x9〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 ADC) MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x9〉〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 ADC) MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x9〉〉) 〈x0,x4〉
].

definition opcode_table_HCS08_2 ≝
[
  quadrupleT ???? (anyOP HCS08 ADD) MODE_IMM1 (Byte 〈xA,xB〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 ADD) MODE_DIR1 (Byte 〈xB,xB〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 ADD) MODE_DIR2 (Byte 〈xC,xB〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 ADD) MODE_IX2  (Byte 〈xD,xB〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 ADD) MODE_IX1  (Byte 〈xE,xB〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 ADD) MODE_IX0  (Byte 〈xF,xB〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 ADD) MODE_SP2  (Word 〈〈x9,xE〉:〈xD,xB〉〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 ADD) MODE_SP1  (Word 〈〈x9,xE〉:〈xE,xB〉〉) 〈x0,x4〉
].

definition opcode_table_HCS08_3 ≝
[
  quadrupleT ???? (anyOP HCS08 AND) MODE_IMM1 (Byte 〈xA,x4〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 AND) MODE_DIR1 (Byte 〈xB,x4〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 AND) MODE_DIR2 (Byte 〈xC,x4〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 AND) MODE_IX2  (Byte 〈xD,x4〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 AND) MODE_IX1  (Byte 〈xE,x4〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 AND) MODE_IX0  (Byte 〈xF,x4〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 AND) MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x4〉〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 AND) MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x4〉〉) 〈x0,x4〉
].

definition opcode_table_HCS08_4 ≝
[
  quadrupleT ???? (anyOP HCS08 ASL) MODE_DIR1 (Byte 〈x3,x8〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 ASL) MODE_INHA (Byte 〈x4,x8〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 ASL) MODE_INHX (Byte 〈x5,x8〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 ASL) MODE_IX1  (Byte 〈x6,x8〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 ASL) MODE_IX0  (Byte 〈x7,x8〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 ASL) MODE_SP1  (Word 〈〈x9,xE〉:〈x6,x8〉〉) 〈x0,x6〉
].

definition opcode_table_HCS08_5 ≝
[
  quadrupleT ???? (anyOP HCS08 ASR) MODE_DIR1 (Byte 〈x3,x7〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 ASR) MODE_INHA (Byte 〈x4,x7〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 ASR) MODE_INHX (Byte 〈x5,x7〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 ASR) MODE_IX1  (Byte 〈x6,x7〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 ASR) MODE_IX0  (Byte 〈x7,x7〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 ASR) MODE_SP1  (Word 〈〈x9,xE〉:〈x6,x7〉〉) 〈x0,x6〉
].

definition opcode_table_HCS08_6 ≝
[
  quadrupleT ???? (anyOP HCS08 BRA ) MODE_IMM1 (Byte 〈x2,x0〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BRN ) MODE_IMM1 (Byte 〈x2,x1〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BHI ) MODE_IMM1 (Byte 〈x2,x2〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BLS ) MODE_IMM1 (Byte 〈x2,x3〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BCC ) MODE_IMM1 (Byte 〈x2,x4〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BCS ) MODE_IMM1 (Byte 〈x2,x5〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BNE ) MODE_IMM1 (Byte 〈x2,x6〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BEQ ) MODE_IMM1 (Byte 〈x2,x7〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BHCC) MODE_IMM1 (Byte 〈x2,x8〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BHCS) MODE_IMM1 (Byte 〈x2,x9〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BPL ) MODE_IMM1 (Byte 〈x2,xA〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BMI ) MODE_IMM1 (Byte 〈x2,xB〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BMC ) MODE_IMM1 (Byte 〈x2,xC〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BMS ) MODE_IMM1 (Byte 〈x2,xD〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BIL ) MODE_IMM1 (Byte 〈x2,xE〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BIH ) MODE_IMM1 (Byte 〈x2,xF〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BGE ) MODE_IMM1 (Byte 〈x9,x0〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BLT ) MODE_IMM1 (Byte 〈x9,x1〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BGT ) MODE_IMM1 (Byte 〈x9,x2〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BLE ) MODE_IMM1 (Byte 〈x9,x3〉) 〈x0,x3〉
].

definition opcode_table_HCS08_7 ≝
[
  quadrupleT ???? (anyOP HCS08 BSETn) (MODE_DIRn o0) (Byte 〈x1,x0〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BCLRn) (MODE_DIRn o0) (Byte 〈x1,x1〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BSETn) (MODE_DIRn o1) (Byte 〈x1,x2〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BCLRn) (MODE_DIRn o1) (Byte 〈x1,x3〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BSETn) (MODE_DIRn o2) (Byte 〈x1,x4〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BCLRn) (MODE_DIRn o2) (Byte 〈x1,x5〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BSETn) (MODE_DIRn o3) (Byte 〈x1,x6〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BCLRn) (MODE_DIRn o3) (Byte 〈x1,x7〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BSETn) (MODE_DIRn o4) (Byte 〈x1,x8〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BCLRn) (MODE_DIRn o4) (Byte 〈x1,x9〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BSETn) (MODE_DIRn o5) (Byte 〈x1,xA〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BCLRn) (MODE_DIRn o5) (Byte 〈x1,xB〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BSETn) (MODE_DIRn o6) (Byte 〈x1,xC〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BCLRn) (MODE_DIRn o6) (Byte 〈x1,xD〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BSETn) (MODE_DIRn o7) (Byte 〈x1,xE〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BCLRn) (MODE_DIRn o7) (Byte 〈x1,xF〉) 〈x0,x5〉
].

definition opcode_table_HCS08_8 ≝
[
  quadrupleT ???? (anyOP HCS08 BRSETn) (MODE_DIRn_and_IMM1 o0) (Byte 〈x0,x0〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BRCLRn) (MODE_DIRn_and_IMM1 o0) (Byte 〈x0,x1〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BRSETn) (MODE_DIRn_and_IMM1 o1) (Byte 〈x0,x2〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BRCLRn) (MODE_DIRn_and_IMM1 o1) (Byte 〈x0,x3〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BRSETn) (MODE_DIRn_and_IMM1 o2) (Byte 〈x0,x4〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BRCLRn) (MODE_DIRn_and_IMM1 o2) (Byte 〈x0,x5〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BRSETn) (MODE_DIRn_and_IMM1 o3) (Byte 〈x0,x6〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BRCLRn) (MODE_DIRn_and_IMM1 o3) (Byte 〈x0,x7〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BRSETn) (MODE_DIRn_and_IMM1 o4) (Byte 〈x0,x8〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BRCLRn) (MODE_DIRn_and_IMM1 o4) (Byte 〈x0,x9〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BRSETn) (MODE_DIRn_and_IMM1 o5) (Byte 〈x0,xA〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BRCLRn) (MODE_DIRn_and_IMM1 o5) (Byte 〈x0,xB〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BRSETn) (MODE_DIRn_and_IMM1 o6) (Byte 〈x0,xC〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BRCLRn) (MODE_DIRn_and_IMM1 o6) (Byte 〈x0,xD〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BRSETn) (MODE_DIRn_and_IMM1 o7) (Byte 〈x0,xE〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BRCLRn) (MODE_DIRn_and_IMM1 o7) (Byte 〈x0,xF〉) 〈x0,x5〉
].

definition opcode_table_HCS08_9 ≝
[
  quadrupleT ???? (anyOP HCS08 BIT) MODE_IMM1 (Byte 〈xA,x5〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 BIT) MODE_DIR1 (Byte 〈xB,x5〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BIT) MODE_DIR2 (Byte 〈xC,x5〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 BIT) MODE_IX2  (Byte 〈xD,x5〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 BIT) MODE_IX1  (Byte 〈xE,x5〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BIT) MODE_IX0  (Byte 〈xF,x5〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 BIT) MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x5〉〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 BIT) MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x5〉〉) 〈x0,x4〉
].

definition opcode_table_HCS08_10 ≝
[
  quadrupleT ???? (anyOP HCS08 MUL ) MODE_INH  (Byte 〈x4,x2〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 DIV ) MODE_INH  (Byte 〈x5,x2〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HCS08 NSA ) MODE_INH  (Byte 〈x6,x2〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 DAA ) MODE_INH  (Byte 〈x7,x2〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 RTI ) MODE_INH  (Byte 〈x8,x0〉) 〈x0,x9〉
; quadrupleT ???? (anyOP HCS08 RTS ) MODE_INH  (Byte 〈x8,x1〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HCS08 SWI ) MODE_INH  (Byte 〈x8,x3〉) 〈x0,xB〉
; quadrupleT ???? (anyOP HCS08 BGND) MODE_INH  (Byte 〈x8,x2〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 TAP ) MODE_INH  (Byte 〈x8,x4〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 TPA ) MODE_INH  (Byte 〈x8,x5〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 PULA) MODE_INH  (Byte 〈x8,x6〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 PSHA) MODE_INH  (Byte 〈x8,x7〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 PULX) MODE_INH  (Byte 〈x8,x8〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 PSHX) MODE_INH  (Byte 〈x8,x9〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 PULH) MODE_INH  (Byte 〈x8,xA〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 PSHH) MODE_INH  (Byte 〈x8,xB〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 STOP) MODE_INH  (Byte 〈x8,xE〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 WAIT) MODE_INH  (Byte 〈x8,xF〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 TXS ) MODE_INH  (Byte 〈x9,x4〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 TSX ) MODE_INH  (Byte 〈x9,x5〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 TAX ) MODE_INH  (Byte 〈x9,x7〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 CLC ) MODE_INH  (Byte 〈x9,x8〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 SEC ) MODE_INH  (Byte 〈x9,x9〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 CLI ) MODE_INH  (Byte 〈x9,xA〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 SEI ) MODE_INH  (Byte 〈x9,xB〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 RSP ) MODE_INH  (Byte 〈x9,xC〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 NOP ) MODE_INH  (Byte 〈x9,xD〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 TXA ) MODE_INH  (Byte 〈x9,xF〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 AIS ) MODE_IMM1 (Byte 〈xA,x7〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 AIX ) MODE_IMM1 (Byte 〈xA,xF〉) 〈x0,x2〉
].

definition opcode_table_HCS08_11 ≝
[
  quadrupleT ???? (anyOP HCS08 CBEQA) MODE_DIR1_and_IMM1 (Byte 〈x3,x1〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 CBEQA) MODE_IMM1_and_IMM1 (Byte 〈x4,x1〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 CBEQX) MODE_IMM1_and_IMM1 (Byte 〈x5,x1〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 CBEQA) MODE_IX1p_and_IMM1 (Byte 〈x6,x1〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 CBEQA) MODE_IX0p_and_IMM1 (Byte 〈x7,x1〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 CBEQA) MODE_SP1_and_IMM1  (Word 〈〈x9,xE〉:〈x6,x1〉〉) 〈x0,x6〉
].

definition opcode_table_HCS08_12 ≝
[
  quadrupleT ???? (anyOP HCS08 CLR) MODE_DIR1 (Byte 〈x3,xF〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 CLR) MODE_INHA (Byte 〈x4,xF〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 CLR) MODE_INHX (Byte 〈x5,xF〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 CLR) MODE_IX1  (Byte 〈x6,xF〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 CLR) MODE_IX0  (Byte 〈x7,xF〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 CLR) MODE_INHH (Byte 〈x8,xC〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 CLR) MODE_SP1  (Word 〈〈x9,xE〉:〈x6,xF〉〉) 〈x0,x6〉
].

definition opcode_table_HCS08_13 ≝
[
  quadrupleT ???? (anyOP HCS08 CMP) MODE_IMM1 (Byte 〈xA,x1〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 CMP) MODE_DIR1 (Byte 〈xB,x1〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 CMP) MODE_DIR2 (Byte 〈xC,x1〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 CMP) MODE_IX2  (Byte 〈xD,x1〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 CMP) MODE_IX1  (Byte 〈xE,x1〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 CMP) MODE_IX0  (Byte 〈xF,x1〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 CMP) MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x1〉〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 CMP) MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x1〉〉) 〈x0,x4〉
].

definition opcode_table_HCS08_14 ≝
[
  quadrupleT ???? (anyOP HCS08 COM) MODE_DIR1 (Byte 〈x3,x3〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 COM) MODE_INHA (Byte 〈x4,x3〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 COM) MODE_INHX (Byte 〈x5,x3〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 COM) MODE_IX1  (Byte 〈x6,x3〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 COM) MODE_IX0  (Byte 〈x7,x3〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 COM) MODE_SP1  (Word 〈〈x9,xE〉:〈x6,x3〉〉) 〈x0,x6〉
].

definition opcode_table_HCS08_15 ≝
[
  quadrupleT ???? (anyOP HCS08 CPHX) MODE_DIR2 (Byte 〈x3,xE〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HCS08 CPHX) MODE_IMM2 (Byte 〈x6,x5〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 CPHX) MODE_DIR1 (Byte 〈x7,x5〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 CPHX) MODE_SP1  (Word 〈〈x9,xE〉:〈xF,x3〉〉) 〈x0,x6〉

; quadrupleT ???? (anyOP HCS08 LDHX) MODE_DIR2 (Byte 〈x3,x2〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 LDHX) MODE_IMM2 (Byte 〈x4,x5〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 LDHX) MODE_DIR1 (Byte 〈x5,x5〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 LDHX) MODE_IX0  (Word 〈〈x9,xE〉:〈xA,xE〉〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 LDHX) MODE_IX2  (Word 〈〈x9,xE〉:〈xB,xE〉〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HCS08 LDHX) MODE_IX1  (Word 〈〈x9,xE〉:〈xC,xE〉〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 LDHX) MODE_SP1  (Word 〈〈x9,xE〉:〈xF,xE〉〉) 〈x0,x5〉

; quadrupleT ???? (anyOP HCS08 STHX) MODE_DIR1 (Byte 〈x3,x5〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 STHX) MODE_DIR2 (Byte 〈x9,x6〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 STHX) MODE_SP1  (Word 〈〈x9,xE〉:〈xF,xF〉〉) 〈x0,x5〉
].

definition opcode_table_HCS08_16 ≝
[
  quadrupleT ???? (anyOP HCS08 CPX) MODE_IMM1 (Byte 〈xA,x3〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 CPX) MODE_DIR1 (Byte 〈xB,x3〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 CPX) MODE_DIR2 (Byte 〈xC,x3〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 CPX) MODE_IX2  (Byte 〈xD,x3〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 CPX) MODE_IX1  (Byte 〈xE,x3〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 CPX) MODE_IX0  (Byte 〈xF,x3〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 CPX) MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x3〉〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 CPX) MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x3〉〉) 〈x0,x4〉
].

definition opcode_table_HCS08_17 ≝
[
  quadrupleT ???? (anyOP HCS08 DBNZ) MODE_DIR1_and_IMM1 (Byte 〈x3,xB〉) 〈x0,x7〉
; quadrupleT ???? (anyOP HCS08 DBNZ) MODE_INHA_and_IMM1 (Byte 〈x4,xB〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 DBNZ) MODE_INHX_and_IMM1 (Byte 〈x5,xB〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 DBNZ) MODE_IX1_and_IMM1  (Byte 〈x6,xB〉) 〈x0,x7〉
; quadrupleT ???? (anyOP HCS08 DBNZ) MODE_IX0_and_IMM1  (Byte 〈x7,xB〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HCS08 DBNZ) MODE_SP1_and_IMM1  (Word 〈〈x9,xE〉:〈x6,xB〉〉) 〈x0,x8〉
].

definition opcode_table_HCS08_18 ≝
[
  quadrupleT ???? (anyOP HCS08 DEC) MODE_DIR1 (Byte 〈x3,xA〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 DEC) MODE_INHA (Byte 〈x4,xA〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 DEC) MODE_INHX (Byte 〈x5,xA〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 DEC) MODE_IX1  (Byte 〈x6,xA〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 DEC) MODE_IX0  (Byte 〈x7,xA〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 DEC) MODE_SP1  (Word 〈〈x9,xE〉:〈x6,xA〉〉) 〈x0,x6〉
].

definition opcode_table_HCS08_19 ≝
[
  quadrupleT ???? (anyOP HCS08 EOR) MODE_IMM1 (Byte 〈xA,x8〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 EOR) MODE_DIR1 (Byte 〈xB,x8〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 EOR) MODE_DIR2 (Byte 〈xC,x8〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 EOR) MODE_IX2  (Byte 〈xD,x8〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 EOR) MODE_IX1  (Byte 〈xE,x8〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 EOR) MODE_IX0  (Byte 〈xF,x8〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 EOR) MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x8〉〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 EOR) MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x8〉〉) 〈x0,x4〉
].

definition opcode_table_HCS08_20 ≝
[
  quadrupleT ???? (anyOP HCS08 INC) MODE_DIR1 (Byte 〈x3,xC〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 INC) MODE_INHA (Byte 〈x4,xC〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 INC) MODE_INHX (Byte 〈x5,xC〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 INC) MODE_IX1  (Byte 〈x6,xC〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 INC) MODE_IX0  (Byte 〈x7,xC〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 INC) MODE_SP1  (Word 〈〈x9,xE〉:〈x6,xC〉〉) 〈x0,x6〉
].

definition opcode_table_HCS08_21 ≝
[
  quadrupleT ???? (anyOP HCS08 JMP) MODE_IMM1EXT  (Byte 〈xB,xC〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 JMP) MODE_IMM2     (Byte 〈xC,xC〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 JMP) MODE_INHX2ADD (Byte 〈xD,xC〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 JMP) MODE_INHX1ADD (Byte 〈xE,xC〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 JMP) MODE_INHX0ADD (Byte 〈xF,xC〉) 〈x0,x3〉
].

definition opcode_table_HCS08_22 ≝
[
  quadrupleT ???? (anyOP HCS08 BSR) MODE_IMM1     (Byte 〈xA,xD〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 JSR) MODE_IMM1EXT  (Byte 〈xB,xD〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 JSR) MODE_IMM2     (Byte 〈xC,xD〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HCS08 JSR) MODE_INHX2ADD (Byte 〈xD,xD〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HCS08 JSR) MODE_INHX1ADD (Byte 〈xE,xD〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 JSR) MODE_INHX0ADD (Byte 〈xF,xD〉) 〈x0,x5〉
].

definition opcode_table_HCS08_23 ≝
[
  quadrupleT ???? (anyOP HCS08 LDA) MODE_IMM1 (Byte 〈xA,x6〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 LDA) MODE_DIR1 (Byte 〈xB,x6〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 LDA) MODE_DIR2 (Byte 〈xC,x6〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 LDA) MODE_IX2  (Byte 〈xD,x6〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 LDA) MODE_IX1  (Byte 〈xE,x6〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 LDA) MODE_IX0  (Byte 〈xF,x6〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 LDA) MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x6〉〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 LDA) MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x6〉〉) 〈x0,x4〉
].

definition opcode_table_HCS08_24 ≝
[
  quadrupleT ???? (anyOP HCS08 LDX) MODE_IMM1 (Byte 〈xA,xE〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 LDX) MODE_DIR1 (Byte 〈xB,xE〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 LDX) MODE_DIR2 (Byte 〈xC,xE〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 LDX) MODE_IX2  (Byte 〈xD,xE〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 LDX) MODE_IX1  (Byte 〈xE,xE〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 LDX) MODE_IX0  (Byte 〈xF,xE〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 LDX) MODE_SP2  (Word 〈〈x9,xE〉:〈xD,xE〉〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 LDX) MODE_SP1  (Word 〈〈x9,xE〉:〈xE,xE〉〉) 〈x0,x4〉
].

definition opcode_table_HCS08_25 ≝
[
  quadrupleT ???? (anyOP HCS08 LSR) MODE_DIR1 (Byte 〈x3,x4〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 LSR) MODE_INHA (Byte 〈x4,x4〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 LSR) MODE_INHX (Byte 〈x5,x4〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 LSR) MODE_IX1  (Byte 〈x6,x4〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 LSR) MODE_IX0  (Byte 〈x7,x4〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 LSR) MODE_SP1  (Word 〈〈x9,xE〉:〈x6,x4〉〉) 〈x0,x6〉
].

definition opcode_table_HCS08_26 ≝
[
  quadrupleT ???? (anyOP HCS08 MOV) MODE_DIR1_to_DIR1 (Byte 〈x4,xE〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 MOV) MODE_DIR1_to_IX0p (Byte 〈x5,xE〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 MOV) MODE_IMM1_to_DIR1 (Byte 〈x6,xE〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 MOV) MODE_IX0p_to_DIR1 (Byte 〈x7,xE〉) 〈x0,x5〉
].

definition opcode_table_HCS08_27 ≝
[
  quadrupleT ???? (anyOP HCS08 NEG) MODE_DIR1 (Byte 〈x3,x0〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 NEG) MODE_INHA (Byte 〈x4,x0〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 NEG) MODE_INHX (Byte 〈x5,x0〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 NEG) MODE_IX1  (Byte 〈x6,x0〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 NEG) MODE_IX0  (Byte 〈x7,x0〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 NEG) MODE_SP1  (Word 〈〈x9,xE〉:〈x6,x0〉〉) 〈x0,x6〉
].

definition opcode_table_HCS08_28 ≝
[
  quadrupleT ???? (anyOP HCS08 ORA) MODE_IMM1 (Byte 〈xA,xA〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 ORA) MODE_DIR1 (Byte 〈xB,xA〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 ORA) MODE_DIR2 (Byte 〈xC,xA〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 ORA) MODE_IX2  (Byte 〈xD,xA〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 ORA) MODE_IX1  (Byte 〈xE,xA〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 ORA) MODE_IX0  (Byte 〈xF,xA〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 ORA) MODE_SP2  (Word 〈〈x9,xE〉:〈xD,xA〉〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 ORA) MODE_SP1  (Word 〈〈x9,xE〉:〈xE,xA〉〉) 〈x0,x4〉
].

definition opcode_table_HCS08_29 ≝
[
  quadrupleT ???? (anyOP HCS08 ROL) MODE_DIR1 (Byte 〈x3,x9〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 ROL) MODE_INHA (Byte 〈x4,x9〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 ROL) MODE_INHX (Byte 〈x5,x9〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 ROL) MODE_IX1  (Byte 〈x6,x9〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 ROL) MODE_IX0  (Byte 〈x7,x9〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 ROL) MODE_SP1  (Word 〈〈x9,xE〉:〈x6,x9〉〉) 〈x0,x6〉
].

definition opcode_table_HCS08_30 ≝
[
  quadrupleT ???? (anyOP HCS08 ROR) MODE_DIR1 (Byte 〈x3,x6〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 ROR) MODE_INHA (Byte 〈x4,x6〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 ROR) MODE_INHX (Byte 〈x5,x6〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 ROR) MODE_IX1  (Byte 〈x6,x6〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 ROR) MODE_IX0  (Byte 〈x7,x6〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 ROR) MODE_SP1  (Word 〈〈x9,xE〉:〈x6,x6〉〉) 〈x0,x6〉
].

definition opcode_table_HCS08_31 ≝
[
  quadrupleT ???? (anyOP HCS08 SBC) MODE_IMM1 (Byte 〈xA,x2〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 SBC) MODE_DIR1 (Byte 〈xB,x2〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 SBC) MODE_DIR2 (Byte 〈xC,x2〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 SBC) MODE_IX2  (Byte 〈xD,x2〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 SBC) MODE_IX1  (Byte 〈xE,x2〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 SBC) MODE_IX0  (Byte 〈xF,x2〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 SBC) MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x2〉〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 SBC) MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x2〉〉) 〈x0,x4〉
].

definition opcode_table_HCS08_32 ≝
[
  quadrupleT ???? (anyOP HCS08 STA) MODE_DIR1 (Byte 〈xB,x7〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 STA) MODE_DIR2 (Byte 〈xC,x7〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 STA) MODE_IX2  (Byte 〈xD,x7〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 STA) MODE_IX1  (Byte 〈xE,x7〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 STA) MODE_IX0  (Byte 〈xF,x7〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 STA) MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x7〉〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 STA) MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x7〉〉) 〈x0,x4〉
].

definition opcode_table_HCS08_33 ≝
[
  quadrupleT ???? (anyOP HCS08 STX) MODE_DIR1 (Byte 〈xB,xF〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 STX) MODE_DIR2 (Byte 〈xC,xF〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 STX) MODE_IX2  (Byte 〈xD,xF〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 STX) MODE_IX1  (Byte 〈xE,xF〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 STX) MODE_IX0  (Byte 〈xF,xF〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 STX) MODE_SP2  (Word 〈〈x9,xE〉:〈xD,xF〉〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 STX) MODE_SP1  (Word 〈〈x9,xE〉:〈xE,xF〉〉) 〈x0,x4〉
].

definition opcode_table_HCS08_34 ≝
[
  quadrupleT ???? (anyOP HCS08 SUB) MODE_IMM1 (Byte 〈xA,x0〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HCS08 SUB) MODE_DIR1 (Byte 〈xB,x0〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 SUB) MODE_DIR2 (Byte 〈xC,x0〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 SUB) MODE_IX2  (Byte 〈xD,x0〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 SUB) MODE_IX1  (Byte 〈xE,x0〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 SUB) MODE_IX0  (Byte 〈xF,x0〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 SUB) MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x0〉〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HCS08 SUB) MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x0〉〉) 〈x0,x4〉
].

definition opcode_table_HCS08_35 ≝
[
  quadrupleT ???? (anyOP HCS08 TST) MODE_DIR1 (Byte 〈x3,xD〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 TST) MODE_INHA (Byte 〈x4,xD〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 TST) MODE_INHX (Byte 〈x5,xD〉) 〈x0,x1〉
; quadrupleT ???? (anyOP HCS08 TST) MODE_IX1  (Byte 〈x6,xD〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HCS08 TST) MODE_IX0  (Byte 〈x7,xD〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HCS08 TST) MODE_SP1  (Word 〈〈x9,xE〉:〈x6,xD〉〉) 〈x0,x5〉
].

definition opcode_table_HCS08 ≝
opcode_table_HCS08_1  @ opcode_table_HCS08_2  @ opcode_table_HCS08_3  @ opcode_table_HCS08_4  @
opcode_table_HCS08_5  @ opcode_table_HCS08_6  @ opcode_table_HCS08_7  @ opcode_table_HCS08_8  @
opcode_table_HCS08_9  @ opcode_table_HCS08_10 @ opcode_table_HCS08_11 @ opcode_table_HCS08_12 @
opcode_table_HCS08_13 @ opcode_table_HCS08_14 @ opcode_table_HCS08_15 @ opcode_table_HCS08_16 @
opcode_table_HCS08_17 @ opcode_table_HCS08_18 @ opcode_table_HCS08_19 @ opcode_table_HCS08_20 @
opcode_table_HCS08_21 @ opcode_table_HCS08_22 @ opcode_table_HCS08_23 @ opcode_table_HCS08_24 @
opcode_table_HCS08_25 @ opcode_table_HCS08_26 @ opcode_table_HCS08_27 @ opcode_table_HCS08_28 @
opcode_table_HCS08_29 @ opcode_table_HCS08_30 @ opcode_table_HCS08_31 @ opcode_table_HCS08_32 @
opcode_table_HCS08_33 @ opcode_table_HCS08_34 @ opcode_table_HCS08_35.
