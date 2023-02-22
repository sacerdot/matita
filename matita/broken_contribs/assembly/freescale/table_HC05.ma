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

(* ***************** *)
(* TABELLA DELL'HC05 *)
(* ***************** *)

(* definizione come concatenazione finale di liste per velocizzare il parsing *)
(* ogni riga e' (any_opcode m) (instr_mode) (opcode esadecimale) (#cicli esecuzione) *)
(* NB: l'uso di any_opcode m + concatenazione finale tutte liste
       impedisce di introdurre opcode disomogenei (per mcu) *)

definition opcode_table_HC05_1 ≝
[
  quadrupleT ???? (anyOP HC05 ADC) MODE_IMM1 (Byte 〈xA,x9〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 ADC) MODE_DIR1 (Byte 〈xB,x9〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 ADC) MODE_DIR2 (Byte 〈xC,x9〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 ADC) MODE_IX2  (Byte 〈xD,x9〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 ADC) MODE_IX1  (Byte 〈xE,x9〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 ADC) MODE_IX0  (Byte 〈xF,x9〉) 〈x0,x4〉
].

definition opcode_table_HC05_2 ≝
[
  quadrupleT ???? (anyOP HC05 ADD) MODE_IMM1 (Byte 〈xA,xB〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 ADD) MODE_DIR1 (Byte 〈xB,xB〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 ADD) MODE_DIR2 (Byte 〈xC,xB〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 ADD) MODE_IX2  (Byte 〈xD,xB〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 ADD) MODE_IX1  (Byte 〈xE,xB〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 ADD) MODE_IX0  (Byte 〈xF,xB〉) 〈x0,x3〉
].

definition opcode_table_HC05_3 ≝
[
  quadrupleT ???? (anyOP HC05 AND) MODE_IMM1 (Byte 〈xA,x4〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 AND) MODE_DIR1 (Byte 〈xB,x4〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 AND) MODE_DIR2 (Byte 〈xC,x4〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 AND) MODE_IX2  (Byte 〈xD,x4〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 AND) MODE_IX1  (Byte 〈xE,x4〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 AND) MODE_IX0  (Byte 〈xF,x4〉) 〈x0,x3〉
].

definition opcode_table_HC05_4 ≝
[
  quadrupleT ???? (anyOP HC05 ASL) MODE_DIR1 (Byte 〈x3,x8〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 ASL) MODE_INHA (Byte 〈x4,x8〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 ASL) MODE_INHX (Byte 〈x5,x8〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 ASL) MODE_IX1  (Byte 〈x6,x8〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HC05 ASL) MODE_IX0  (Byte 〈x7,x8〉) 〈x0,x5〉
].

definition opcode_table_HC05_5 ≝
[
  quadrupleT ???? (anyOP HC05 ASR) MODE_DIR1 (Byte 〈x3,x7〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 ASR) MODE_INHA (Byte 〈x4,x7〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 ASR) MODE_INHX (Byte 〈x5,x7〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 ASR) MODE_IX1  (Byte 〈x6,x7〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HC05 ASR) MODE_IX0  (Byte 〈x7,x7〉) 〈x0,x5〉
].

definition opcode_table_HC05_6 ≝
[
  quadrupleT ???? (anyOP HC05 BRA ) MODE_IMM1 (Byte 〈x2,x0〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 BRN ) MODE_IMM1 (Byte 〈x2,x1〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 BHI ) MODE_IMM1 (Byte 〈x2,x2〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 BLS ) MODE_IMM1 (Byte 〈x2,x3〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 BCC ) MODE_IMM1 (Byte 〈x2,x4〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 BCS ) MODE_IMM1 (Byte 〈x2,x5〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 BNE ) MODE_IMM1 (Byte 〈x2,x6〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 BEQ ) MODE_IMM1 (Byte 〈x2,x7〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 BHCC) MODE_IMM1 (Byte 〈x2,x8〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 BHCS) MODE_IMM1 (Byte 〈x2,x9〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 BPL ) MODE_IMM1 (Byte 〈x2,xA〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 BMI ) MODE_IMM1 (Byte 〈x2,xB〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 BMC ) MODE_IMM1 (Byte 〈x2,xC〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 BMS ) MODE_IMM1 (Byte 〈x2,xD〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 BIL ) MODE_IMM1 (Byte 〈x2,xE〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 BIH ) MODE_IMM1 (Byte 〈x2,xF〉) 〈x0,x3〉
].

definition opcode_table_HC05_7 ≝
[
  quadrupleT ???? (anyOP HC05 BSETn) (MODE_DIRn o0) (Byte 〈x1,x0〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BCLRn) (MODE_DIRn o0) (Byte 〈x1,x1〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BSETn) (MODE_DIRn o1) (Byte 〈x1,x2〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BCLRn) (MODE_DIRn o1) (Byte 〈x1,x3〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BSETn) (MODE_DIRn o2) (Byte 〈x1,x4〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BCLRn) (MODE_DIRn o2) (Byte 〈x1,x5〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BSETn) (MODE_DIRn o3) (Byte 〈x1,x6〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BCLRn) (MODE_DIRn o3) (Byte 〈x1,x7〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BSETn) (MODE_DIRn o4) (Byte 〈x1,x8〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BCLRn) (MODE_DIRn o4) (Byte 〈x1,x9〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BSETn) (MODE_DIRn o5) (Byte 〈x1,xA〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BCLRn) (MODE_DIRn o5) (Byte 〈x1,xB〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BSETn) (MODE_DIRn o6) (Byte 〈x1,xC〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BCLRn) (MODE_DIRn o6) (Byte 〈x1,xD〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BSETn) (MODE_DIRn o7) (Byte 〈x1,xE〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BCLRn) (MODE_DIRn o7) (Byte 〈x1,xF〉) 〈x0,x5〉
].

definition opcode_table_HC05_8 ≝
[
  quadrupleT ???? (anyOP HC05 BRSETn) (MODE_DIRn_and_IMM1 o0) (Byte 〈x0,x0〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BRCLRn) (MODE_DIRn_and_IMM1 o0) (Byte 〈x0,x1〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BRSETn) (MODE_DIRn_and_IMM1 o1) (Byte 〈x0,x2〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BRCLRn) (MODE_DIRn_and_IMM1 o1) (Byte 〈x0,x3〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BRSETn) (MODE_DIRn_and_IMM1 o2) (Byte 〈x0,x4〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BRCLRn) (MODE_DIRn_and_IMM1 o2) (Byte 〈x0,x5〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BRSETn) (MODE_DIRn_and_IMM1 o3) (Byte 〈x0,x6〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BRCLRn) (MODE_DIRn_and_IMM1 o3) (Byte 〈x0,x7〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BRSETn) (MODE_DIRn_and_IMM1 o4) (Byte 〈x0,x8〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BRCLRn) (MODE_DIRn_and_IMM1 o4) (Byte 〈x0,x9〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BRSETn) (MODE_DIRn_and_IMM1 o5) (Byte 〈x0,xA〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BRCLRn) (MODE_DIRn_and_IMM1 o5) (Byte 〈x0,xB〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BRSETn) (MODE_DIRn_and_IMM1 o6) (Byte 〈x0,xC〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BRCLRn) (MODE_DIRn_and_IMM1 o6) (Byte 〈x0,xD〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BRSETn) (MODE_DIRn_and_IMM1 o7) (Byte 〈x0,xE〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BRCLRn) (MODE_DIRn_and_IMM1 o7) (Byte 〈x0,xF〉) 〈x0,x5〉
].

definition opcode_table_HC05_9 ≝
[
  quadrupleT ???? (anyOP HC05 BIT) MODE_IMM1 (Byte 〈xA,x5〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 BIT) MODE_DIR1 (Byte 〈xB,x5〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 BIT) MODE_DIR2 (Byte 〈xC,x5〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 BIT) MODE_IX2  (Byte 〈xD,x5〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 BIT) MODE_IX1  (Byte 〈xE,x5〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 BIT) MODE_IX0  (Byte 〈xF,x5〉) 〈x0,x3〉
].

definition opcode_table_HC05_10 ≝
[
  quadrupleT ???? (anyOP HC05 MUL ) MODE_INH (Byte 〈x4,x2〉) 〈x0,xB〉
; quadrupleT ???? (anyOP HC05 RTI ) MODE_INH (Byte 〈x8,x0〉) 〈x0,x9〉
; quadrupleT ???? (anyOP HC05 RTS ) MODE_INH (Byte 〈x8,x1〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HC05 SWI ) MODE_INH (Byte 〈x8,x3〉) 〈x0,xA〉
; quadrupleT ???? (anyOP HC05 STOP) MODE_INH (Byte 〈x8,xE〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 WAIT) MODE_INH (Byte 〈x8,xF〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 TAX ) MODE_INH (Byte 〈x9,x7〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 CLC ) MODE_INH (Byte 〈x9,x8〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 SEC ) MODE_INH (Byte 〈x9,x9〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 CLI ) MODE_INH (Byte 〈x9,xA〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 SEI ) MODE_INH (Byte 〈x9,xB〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 RSP ) MODE_INH (Byte 〈x9,xC〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 NOP ) MODE_INH (Byte 〈x9,xD〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 TXA ) MODE_INH (Byte 〈x9,xF〉) 〈x0,x2〉
].

definition opcode_table_HC05_11 ≝
[
  quadrupleT ???? (anyOP HC05 CLR) MODE_DIR1 (Byte 〈x3,xF〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 CLR) MODE_INHA (Byte 〈x4,xF〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 CLR) MODE_INHX (Byte 〈x5,xF〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 CLR) MODE_IX1  (Byte 〈x6,xF〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HC05 CLR) MODE_IX0  (Byte 〈x7,xF〉) 〈x0,x5〉
].

definition opcode_table_HC05_12 ≝
[
  quadrupleT ???? (anyOP HC05 CMP) MODE_IMM1 (Byte 〈xA,x1〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 CMP) MODE_DIR1 (Byte 〈xB,x1〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 CMP) MODE_DIR2 (Byte 〈xC,x1〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 CMP) MODE_IX2  (Byte 〈xD,x1〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 CMP) MODE_IX1  (Byte 〈xE,x1〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 CMP) MODE_IX0  (Byte 〈xF,x1〉) 〈x0,x3〉
].

definition opcode_table_HC05_13 ≝
[
  quadrupleT ???? (anyOP HC05 COM) MODE_DIR1 (Byte 〈x3,x3〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 COM) MODE_INHA (Byte 〈x4,x3〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 COM) MODE_INHX (Byte 〈x5,x3〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 COM) MODE_IX1  (Byte 〈x6,x3〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HC05 COM) MODE_IX0  (Byte 〈x7,x3〉) 〈x0,x5〉
].

definition opcode_table_HC05_14 ≝
[
  quadrupleT ???? (anyOP HC05 CPX) MODE_IMM1 (Byte 〈xA,x3〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 CPX) MODE_DIR1 (Byte 〈xB,x3〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 CPX) MODE_DIR2 (Byte 〈xC,x3〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 CPX) MODE_IX2  (Byte 〈xD,x3〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 CPX) MODE_IX1  (Byte 〈xE,x3〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 CPX) MODE_IX0  (Byte 〈xF,x3〉) 〈x0,x3〉
].

definition opcode_table_HC05_15 ≝
[
  quadrupleT ???? (anyOP HC05 DEC) MODE_DIR1 (Byte 〈x3,xA〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 DEC) MODE_INHA (Byte 〈x4,xA〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 DEC) MODE_INHX (Byte 〈x5,xA〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 DEC) MODE_IX1  (Byte 〈x6,xA〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HC05 DEC) MODE_IX0  (Byte 〈x7,xA〉) 〈x0,x5〉
].

definition opcode_table_HC05_16 ≝
[
  quadrupleT ???? (anyOP HC05 EOR) MODE_IMM1 (Byte 〈xA,x8〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 EOR) MODE_DIR1 (Byte 〈xB,x8〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 EOR) MODE_DIR2 (Byte 〈xC,x8〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 EOR) MODE_IX2  (Byte 〈xD,x8〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 EOR) MODE_IX1  (Byte 〈xE,x8〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 EOR) MODE_IX0  (Byte 〈xF,x8〉) 〈x0,x3〉
].

definition opcode_table_HC05_17 ≝
[
  quadrupleT ???? (anyOP HC05 INC) MODE_DIR1 (Byte 〈x3,xC〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 INC) MODE_INHA (Byte 〈x4,xC〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 INC) MODE_INHX (Byte 〈x5,xC〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 INC) MODE_IX1  (Byte 〈x6,xC〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HC05 INC) MODE_IX0  (Byte 〈x7,xC〉) 〈x0,x5〉
].

definition opcode_table_HC05_18 ≝
[
  quadrupleT ???? (anyOP HC05 JMP) MODE_IMM1EXT  (Byte 〈xB,xC〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 JMP) MODE_IMM2     (Byte 〈xC,xC〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 JMP) MODE_INHX2ADD (Byte 〈xD,xC〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 JMP) MODE_INHX1ADD (Byte 〈xE,xC〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 JMP) MODE_INHX0ADD (Byte 〈xF,xC〉) 〈x0,x2〉
].

definition opcode_table_HC05_19 ≝
[
  quadrupleT ???? (anyOP HC05 BSR) MODE_IMM1     (Byte 〈xA,xD〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HC05 JSR) MODE_IMM1EXT  (Byte 〈xB,xD〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 JSR) MODE_IMM2     (Byte 〈xC,xD〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HC05 JSR) MODE_INHX2ADD (Byte 〈xD,xD〉) 〈x0,x7〉
; quadrupleT ???? (anyOP HC05 JSR) MODE_INHX1ADD (Byte 〈xE,xD〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HC05 JSR) MODE_INHX0ADD (Byte 〈xF,xD〉) 〈x0,x5〉
].

definition opcode_table_HC05_20 ≝
[
  quadrupleT ???? (anyOP HC05 LDA) MODE_IMM1 (Byte 〈xA,x6〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 LDA) MODE_DIR1 (Byte 〈xB,x6〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 LDA) MODE_DIR2 (Byte 〈xC,x6〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 LDA) MODE_IX2  (Byte 〈xD,x6〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 LDA) MODE_IX1  (Byte 〈xE,x6〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 LDA) MODE_IX0  (Byte 〈xF,x6〉) 〈x0,x3〉
].

definition opcode_table_HC05_21 ≝
[
  quadrupleT ???? (anyOP HC05 LDX) MODE_IMM1 (Byte 〈xA,xE〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 LDX) MODE_DIR1 (Byte 〈xB,xE〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 LDX) MODE_DIR2 (Byte 〈xC,xE〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 LDX) MODE_IX2  (Byte 〈xD,xE〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 LDX) MODE_IX1  (Byte 〈xE,xE〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 LDX) MODE_IX0  (Byte 〈xF,xE〉) 〈x0,x3〉
].

definition opcode_table_HC05_22 ≝
[
  quadrupleT ???? (anyOP HC05 LSR) MODE_DIR1 (Byte 〈x3,x4〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 LSR) MODE_INHA (Byte 〈x4,x4〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 LSR) MODE_INHX (Byte 〈x5,x4〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 LSR) MODE_IX1  (Byte 〈x6,x4〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HC05 LSR) MODE_IX0  (Byte 〈x7,x4〉) 〈x0,x5〉
].

definition opcode_table_HC05_23 ≝
[
  quadrupleT ???? (anyOP HC05 NEG) MODE_DIR1 (Byte 〈x3,x0〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 NEG) MODE_INHA (Byte 〈x4,x0〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 NEG) MODE_INHX (Byte 〈x5,x0〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 NEG) MODE_IX1  (Byte 〈x6,x0〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HC05 NEG) MODE_IX0  (Byte 〈x7,x0〉) 〈x0,x5〉
].

definition opcode_table_HC05_24 ≝
[
  quadrupleT ???? (anyOP HC05 ORA) MODE_IMM1 (Byte 〈xA,xA〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 ORA) MODE_DIR1 (Byte 〈xB,xA〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 ORA) MODE_DIR2 (Byte 〈xC,xA〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 ORA) MODE_IX2  (Byte 〈xD,xA〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 ORA) MODE_IX1  (Byte 〈xE,xA〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 ORA) MODE_IX0  (Byte 〈xF,xA〉) 〈x0,x3〉
].

definition opcode_table_HC05_25 ≝
[
  quadrupleT ???? (anyOP HC05 ROL) MODE_DIR1 (Byte 〈x3,x9〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 ROL) MODE_INHA (Byte 〈x4,x9〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 ROL) MODE_INHX (Byte 〈x5,x9〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 ROL) MODE_IX1  (Byte 〈x6,x9〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HC05 ROL) MODE_IX0  (Byte 〈x7,x9〉) 〈x0,x5〉
].

definition opcode_table_HC05_26 ≝
[
  quadrupleT ???? (anyOP HC05 ROR) MODE_DIR1 (Byte 〈x3,x6〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 ROR) MODE_INHA (Byte 〈x4,x6〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 ROR) MODE_INHX (Byte 〈x5,x6〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 ROR) MODE_IX1  (Byte 〈x6,x6〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HC05 ROR) MODE_IX0  (Byte 〈x7,x6〉) 〈x0,x5〉
].

definition opcode_table_HC05_27 ≝
[
  quadrupleT ???? (anyOP HC05 SBC) MODE_IMM1 (Byte 〈xA,x2〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 SBC) MODE_DIR1 (Byte 〈xB,x2〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 SBC) MODE_DIR2 (Byte 〈xC,x2〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 SBC) MODE_IX2  (Byte 〈xD,x2〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 SBC) MODE_IX1  (Byte 〈xE,x2〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 SBC) MODE_IX0  (Byte 〈xF,x2〉) 〈x0,x3〉
].

definition opcode_table_HC05_28 ≝
[
  quadrupleT ???? (anyOP HC05 STA) MODE_DIR1 (Byte 〈xB,x7〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 STA) MODE_DIR2 (Byte 〈xC,x7〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 STA) MODE_IX2  (Byte 〈xD,x7〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HC05 STA) MODE_IX1  (Byte 〈xE,x7〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 STA) MODE_IX0  (Byte 〈xF,x7〉) 〈x0,x4〉
].

definition opcode_table_HC05_29 ≝
[
  quadrupleT ???? (anyOP HC05 STX) MODE_DIR1 (Byte 〈xB,xF〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 STX) MODE_DIR2 (Byte 〈xC,xF〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 STX) MODE_IX2  (Byte 〈xD,xF〉) 〈x0,x6〉
; quadrupleT ???? (anyOP HC05 STX) MODE_IX1  (Byte 〈xE,xF〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 STX) MODE_IX0  (Byte 〈xF,xF〉) 〈x0,x4〉
].

definition opcode_table_HC05_30 ≝
[
  quadrupleT ???? (anyOP HC05 SUB) MODE_IMM1 (Byte 〈xA,x0〉) 〈x0,x2〉
; quadrupleT ???? (anyOP HC05 SUB) MODE_DIR1 (Byte 〈xB,x0〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 SUB) MODE_DIR2 (Byte 〈xC,x0〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 SUB) MODE_IX2  (Byte 〈xD,x0〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 SUB) MODE_IX1  (Byte 〈xE,x0〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 SUB) MODE_IX0  (Byte 〈xF,x0〉) 〈x0,x3〉
].

definition opcode_table_HC05_31 ≝
[
  quadrupleT ???? (anyOP HC05 TST) MODE_DIR1 (Byte 〈x3,xD〉) 〈x0,x4〉
; quadrupleT ???? (anyOP HC05 TST) MODE_INHA (Byte 〈x4,xD〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 TST) MODE_INHX (Byte 〈x5,xD〉) 〈x0,x3〉
; quadrupleT ???? (anyOP HC05 TST) MODE_IX1  (Byte 〈x6,xD〉) 〈x0,x5〉
; quadrupleT ???? (anyOP HC05 TST) MODE_IX0  (Byte 〈x7,xD〉) 〈x0,x4〉
].

definition opcode_table_HC05 ≝
 opcode_table_HC05_1  @ opcode_table_HC05_2  @ opcode_table_HC05_3  @ opcode_table_HC05_4  @
 opcode_table_HC05_5  @ opcode_table_HC05_6  @ opcode_table_HC05_7  @ opcode_table_HC05_8  @
 opcode_table_HC05_9  @ opcode_table_HC05_10 @ opcode_table_HC05_11 @ opcode_table_HC05_12 @
 opcode_table_HC05_13 @ opcode_table_HC05_14 @ opcode_table_HC05_15 @ opcode_table_HC05_16 @
 opcode_table_HC05_17 @ opcode_table_HC05_18 @ opcode_table_HC05_19 @ opcode_table_HC05_20 @
 opcode_table_HC05_21 @ opcode_table_HC05_22 @ opcode_table_HC05_23 @ opcode_table_HC05_24 @
 opcode_table_HC05_25 @ opcode_table_HC05_26 @ opcode_table_HC05_27 @ opcode_table_HC05_28 @
 opcode_table_HC05_29 @ opcode_table_HC05_30 @ opcode_table_HC05_31.
