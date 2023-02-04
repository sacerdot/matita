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
include "emulator/opcodes/byte_or_word.ma".
include "common/list.ma".

(* ***************** *)
(* TABELLA DELL'HC05 *)
(* ***************** *)

(* definizione come concatenazione finale di liste per velocizzare il parsing *)
(* ogni riga e' [pseudo] [modalita' indirizzamento] [opcode esadecimale] [#cicli esecuzione] *)

ndefinition opcode_table_HC05_1 ≝
[
  quadruple … ADC MODE_IMM1 (Byte 〈xA,x9〉) nat2
; quadruple … ADC MODE_DIR1 (Byte 〈xB,x9〉) nat3
; quadruple … ADC MODE_DIR2 (Byte 〈xC,x9〉) nat4
; quadruple … ADC MODE_IX2  (Byte 〈xD,x9〉) nat5
; quadruple … ADC MODE_IX1  (Byte 〈xE,x9〉) nat4
; quadruple … ADC MODE_IX0  (Byte 〈xF,x9〉) nat4
].

ndefinition opcode_table_HC05_2 ≝
[
  quadruple … ADD MODE_IMM1 (Byte 〈xA,xB〉) nat2
; quadruple … ADD MODE_DIR1 (Byte 〈xB,xB〉) nat3
; quadruple … ADD MODE_DIR2 (Byte 〈xC,xB〉) nat4
; quadruple … ADD MODE_IX2  (Byte 〈xD,xB〉) nat5
; quadruple … ADD MODE_IX1  (Byte 〈xE,xB〉) nat4
; quadruple … ADD MODE_IX0  (Byte 〈xF,xB〉) nat3
].

ndefinition opcode_table_HC05_3 ≝
[
  quadruple … AND MODE_IMM1 (Byte 〈xA,x4〉) nat2
; quadruple … AND MODE_DIR1 (Byte 〈xB,x4〉) nat3
; quadruple … AND MODE_DIR2 (Byte 〈xC,x4〉) nat4
; quadruple … AND MODE_IX2  (Byte 〈xD,x4〉) nat5
; quadruple … AND MODE_IX1  (Byte 〈xE,x4〉) nat4
; quadruple … AND MODE_IX0  (Byte 〈xF,x4〉) nat3
].

ndefinition opcode_table_HC05_4 ≝
[
  quadruple … ASL MODE_DIR1 (Byte 〈x3,x8〉) nat5
; quadruple … ASL MODE_INHA (Byte 〈x4,x8〉) nat3
; quadruple … ASL MODE_INHX (Byte 〈x5,x8〉) nat3
; quadruple … ASL MODE_IX1  (Byte 〈x6,x8〉) nat6
; quadruple … ASL MODE_IX0  (Byte 〈x7,x8〉) nat5
].

ndefinition opcode_table_HC05_5 ≝
[
  quadruple … ASR MODE_DIR1 (Byte 〈x3,x7〉) nat5
; quadruple … ASR MODE_INHA (Byte 〈x4,x7〉) nat3
; quadruple … ASR MODE_INHX (Byte 〈x5,x7〉) nat3
; quadruple … ASR MODE_IX1  (Byte 〈x6,x7〉) nat6
; quadruple … ASR MODE_IX0  (Byte 〈x7,x7〉) nat5
].

ndefinition opcode_table_HC05_6 ≝
[
  quadruple … BRA  MODE_IMM1 (Byte 〈x2,x0〉) nat3
; quadruple … BRN  MODE_IMM1 (Byte 〈x2,x1〉) nat3
; quadruple … BHI  MODE_IMM1 (Byte 〈x2,x2〉) nat3
; quadruple … BLS  MODE_IMM1 (Byte 〈x2,x3〉) nat3
; quadruple … BCC  MODE_IMM1 (Byte 〈x2,x4〉) nat3
; quadruple … BCS  MODE_IMM1 (Byte 〈x2,x5〉) nat3
; quadruple … BNE  MODE_IMM1 (Byte 〈x2,x6〉) nat3
; quadruple … BEQ  MODE_IMM1 (Byte 〈x2,x7〉) nat3
; quadruple … BHCC MODE_IMM1 (Byte 〈x2,x8〉) nat3
; quadruple … BHCS MODE_IMM1 (Byte 〈x2,x9〉) nat3
; quadruple … BPL  MODE_IMM1 (Byte 〈x2,xA〉) nat3
; quadruple … BMI  MODE_IMM1 (Byte 〈x2,xB〉) nat3
; quadruple … BMC  MODE_IMM1 (Byte 〈x2,xC〉) nat3
; quadruple … BMS  MODE_IMM1 (Byte 〈x2,xD〉) nat3
; quadruple … BIL  MODE_IMM1 (Byte 〈x2,xE〉) nat3
; quadruple … BIH  MODE_IMM1 (Byte 〈x2,xF〉) nat3
].

ndefinition opcode_table_HC05_7 ≝
[
  quadruple … BSETn (MODE_DIRn o0) (Byte 〈x1,x0〉) nat5
; quadruple … BCLRn (MODE_DIRn o0) (Byte 〈x1,x1〉) nat5
; quadruple … BSETn (MODE_DIRn o1) (Byte 〈x1,x2〉) nat5
; quadruple … BCLRn (MODE_DIRn o1) (Byte 〈x1,x3〉) nat5
; quadruple … BSETn (MODE_DIRn o2) (Byte 〈x1,x4〉) nat5
; quadruple … BCLRn (MODE_DIRn o2) (Byte 〈x1,x5〉) nat5
; quadruple … BSETn (MODE_DIRn o3) (Byte 〈x1,x6〉) nat5
; quadruple … BCLRn (MODE_DIRn o3) (Byte 〈x1,x7〉) nat5
; quadruple … BSETn (MODE_DIRn o4) (Byte 〈x1,x8〉) nat5
; quadruple … BCLRn (MODE_DIRn o4) (Byte 〈x1,x9〉) nat5
; quadruple … BSETn (MODE_DIRn o5) (Byte 〈x1,xA〉) nat5
; quadruple … BCLRn (MODE_DIRn o5) (Byte 〈x1,xB〉) nat5
; quadruple … BSETn (MODE_DIRn o6) (Byte 〈x1,xC〉) nat5
; quadruple … BCLRn (MODE_DIRn o6) (Byte 〈x1,xD〉) nat5
; quadruple … BSETn (MODE_DIRn o7) (Byte 〈x1,xE〉) nat5
; quadruple … BCLRn (MODE_DIRn o7) (Byte 〈x1,xF〉) nat5
].

ndefinition opcode_table_HC05_8 ≝
[
  quadruple … BRSETn (MODE_DIRn_and_IMM1 o0) (Byte 〈x0,x0〉) nat5
; quadruple … BRCLRn (MODE_DIRn_and_IMM1 o0) (Byte 〈x0,x1〉) nat5
; quadruple … BRSETn (MODE_DIRn_and_IMM1 o1) (Byte 〈x0,x2〉) nat5
; quadruple … BRCLRn (MODE_DIRn_and_IMM1 o1) (Byte 〈x0,x3〉) nat5
; quadruple … BRSETn (MODE_DIRn_and_IMM1 o2) (Byte 〈x0,x4〉) nat5
; quadruple … BRCLRn (MODE_DIRn_and_IMM1 o2) (Byte 〈x0,x5〉) nat5
; quadruple … BRSETn (MODE_DIRn_and_IMM1 o3) (Byte 〈x0,x6〉) nat5
; quadruple … BRCLRn (MODE_DIRn_and_IMM1 o3) (Byte 〈x0,x7〉) nat5
; quadruple … BRSETn (MODE_DIRn_and_IMM1 o4) (Byte 〈x0,x8〉) nat5
; quadruple … BRCLRn (MODE_DIRn_and_IMM1 o4) (Byte 〈x0,x9〉) nat5
; quadruple … BRSETn (MODE_DIRn_and_IMM1 o5) (Byte 〈x0,xA〉) nat5
; quadruple … BRCLRn (MODE_DIRn_and_IMM1 o5) (Byte 〈x0,xB〉) nat5
; quadruple … BRSETn (MODE_DIRn_and_IMM1 o6) (Byte 〈x0,xC〉) nat5
; quadruple … BRCLRn (MODE_DIRn_and_IMM1 o6) (Byte 〈x0,xD〉) nat5
; quadruple … BRSETn (MODE_DIRn_and_IMM1 o7) (Byte 〈x0,xE〉) nat5
; quadruple … BRCLRn (MODE_DIRn_and_IMM1 o7) (Byte 〈x0,xF〉) nat5
].

ndefinition opcode_table_HC05_9 ≝
[
  quadruple … BIT MODE_IMM1 (Byte 〈xA,x5〉) nat2
; quadruple … BIT MODE_DIR1 (Byte 〈xB,x5〉) nat3
; quadruple … BIT MODE_DIR2 (Byte 〈xC,x5〉) nat4
; quadruple … BIT MODE_IX2  (Byte 〈xD,x5〉) nat5
; quadruple … BIT MODE_IX1  (Byte 〈xE,x5〉) nat4
; quadruple … BIT MODE_IX0  (Byte 〈xF,x5〉) nat3
].

ndefinition opcode_table_HC05_10 ≝
[
  quadruple … MUL  MODE_INH (Byte 〈x4,x2〉) nat11
; quadruple … RTI  MODE_INH (Byte 〈x8,x0〉) nat9
; quadruple … RTS  MODE_INH (Byte 〈x8,x1〉) nat6
; quadruple … SWI  MODE_INH (Byte 〈x8,x3〉) nat10
; quadruple … STOP MODE_INH (Byte 〈x8,xE〉) nat2
; quadruple … WAIT MODE_INH (Byte 〈x8,xF〉) nat2
; quadruple … TAX  MODE_INH (Byte 〈x9,x7〉) nat2
; quadruple … CLC  MODE_INH (Byte 〈x9,x8〉) nat2
; quadruple … SEC  MODE_INH (Byte 〈x9,x9〉) nat2
; quadruple … CLI  MODE_INH (Byte 〈x9,xA〉) nat2
; quadruple … SEI  MODE_INH (Byte 〈x9,xB〉) nat2
; quadruple … RSP  MODE_INH (Byte 〈x9,xC〉) nat2
; quadruple … NOP  MODE_INH (Byte 〈x9,xD〉) nat2
; quadruple … TXA  MODE_INH (Byte 〈x9,xF〉) nat2
].

ndefinition opcode_table_HC05_11 ≝
[
  quadruple … CLR MODE_DIR1 (Byte 〈x3,xF〉) nat5
; quadruple … CLR MODE_INHA (Byte 〈x4,xF〉) nat3
; quadruple … CLR MODE_INHX (Byte 〈x5,xF〉) nat3
; quadruple … CLR MODE_IX1  (Byte 〈x6,xF〉) nat6
; quadruple … CLR MODE_IX0  (Byte 〈x7,xF〉) nat5
].

ndefinition opcode_table_HC05_12 ≝
[
  quadruple … CMP MODE_IMM1 (Byte 〈xA,x1〉) nat2
; quadruple … CMP MODE_DIR1 (Byte 〈xB,x1〉) nat3
; quadruple … CMP MODE_DIR2 (Byte 〈xC,x1〉) nat4
; quadruple … CMP MODE_IX2  (Byte 〈xD,x1〉) nat5
; quadruple … CMP MODE_IX1  (Byte 〈xE,x1〉) nat4
; quadruple … CMP MODE_IX0  (Byte 〈xF,x1〉) nat3
].

ndefinition opcode_table_HC05_13 ≝
[
  quadruple … COM MODE_DIR1 (Byte 〈x3,x3〉) nat5
; quadruple … COM MODE_INHA (Byte 〈x4,x3〉) nat3
; quadruple … COM MODE_INHX (Byte 〈x5,x3〉) nat3
; quadruple … COM MODE_IX1  (Byte 〈x6,x3〉) nat6
; quadruple … COM MODE_IX0  (Byte 〈x7,x3〉) nat5
].

ndefinition opcode_table_HC05_14 ≝
[
  quadruple … CPX MODE_IMM1 (Byte 〈xA,x3〉) nat2
; quadruple … CPX MODE_DIR1 (Byte 〈xB,x3〉) nat3
; quadruple … CPX MODE_DIR2 (Byte 〈xC,x3〉) nat4
; quadruple … CPX MODE_IX2  (Byte 〈xD,x3〉) nat5
; quadruple … CPX MODE_IX1  (Byte 〈xE,x3〉) nat4
; quadruple … CPX MODE_IX0  (Byte 〈xF,x3〉) nat3
].

ndefinition opcode_table_HC05_15 ≝
[
  quadruple … DEC MODE_DIR1 (Byte 〈x3,xA〉) nat5
; quadruple … DEC MODE_INHA (Byte 〈x4,xA〉) nat3
; quadruple … DEC MODE_INHX (Byte 〈x5,xA〉) nat3
; quadruple … DEC MODE_IX1  (Byte 〈x6,xA〉) nat6
; quadruple … DEC MODE_IX0  (Byte 〈x7,xA〉) nat5
].

ndefinition opcode_table_HC05_16 ≝
[
  quadruple … EOR MODE_IMM1 (Byte 〈xA,x8〉) nat2
; quadruple … EOR MODE_DIR1 (Byte 〈xB,x8〉) nat3
; quadruple … EOR MODE_DIR2 (Byte 〈xC,x8〉) nat4
; quadruple … EOR MODE_IX2  (Byte 〈xD,x8〉) nat5
; quadruple … EOR MODE_IX1  (Byte 〈xE,x8〉) nat4
; quadruple … EOR MODE_IX0  (Byte 〈xF,x8〉) nat3
].

ndefinition opcode_table_HC05_17 ≝
[
  quadruple … INC MODE_DIR1 (Byte 〈x3,xC〉) nat5
; quadruple … INC MODE_INHA (Byte 〈x4,xC〉) nat3
; quadruple … INC MODE_INHX (Byte 〈x5,xC〉) nat3
; quadruple … INC MODE_IX1  (Byte 〈x6,xC〉) nat6
; quadruple … INC MODE_IX0  (Byte 〈x7,xC〉) nat5
].

ndefinition opcode_table_HC05_18 ≝
[
  quadruple … JMP MODE_IMM1EXT  (Byte 〈xB,xC〉) nat2
; quadruple … JMP MODE_IMM2     (Byte 〈xC,xC〉) nat3
; quadruple … JMP MODE_INHX2ADD (Byte 〈xD,xC〉) nat4
; quadruple … JMP MODE_INHX1ADD (Byte 〈xE,xC〉) nat3
; quadruple … JMP MODE_INHX0ADD (Byte 〈xF,xC〉) nat2
].

ndefinition opcode_table_HC05_19 ≝
[
  quadruple … BSR MODE_IMM1     (Byte 〈xA,xD〉) nat6
; quadruple … JSR MODE_IMM1EXT  (Byte 〈xB,xD〉) nat5
; quadruple … JSR MODE_IMM2     (Byte 〈xC,xD〉) nat6
; quadruple … JSR MODE_INHX2ADD (Byte 〈xD,xD〉) nat7
; quadruple … JSR MODE_INHX1ADD (Byte 〈xE,xD〉) nat6
; quadruple … JSR MODE_INHX0ADD (Byte 〈xF,xD〉) nat5
].

ndefinition opcode_table_HC05_20 ≝
[
  quadruple … LDA MODE_IMM1 (Byte 〈xA,x6〉) nat2
; quadruple … LDA MODE_DIR1 (Byte 〈xB,x6〉) nat3
; quadruple … LDA MODE_DIR2 (Byte 〈xC,x6〉) nat4
; quadruple … LDA MODE_IX2  (Byte 〈xD,x6〉) nat5
; quadruple … LDA MODE_IX1  (Byte 〈xE,x6〉) nat4
; quadruple … LDA MODE_IX0  (Byte 〈xF,x6〉) nat3
].

ndefinition opcode_table_HC05_21 ≝
[
  quadruple … LDX MODE_IMM1 (Byte 〈xA,xE〉) nat2
; quadruple … LDX MODE_DIR1 (Byte 〈xB,xE〉) nat3
; quadruple … LDX MODE_DIR2 (Byte 〈xC,xE〉) nat4
; quadruple … LDX MODE_IX2  (Byte 〈xD,xE〉) nat5
; quadruple … LDX MODE_IX1  (Byte 〈xE,xE〉) nat4
; quadruple … LDX MODE_IX0  (Byte 〈xF,xE〉) nat3
].

ndefinition opcode_table_HC05_22 ≝
[
  quadruple … LSR MODE_DIR1 (Byte 〈x3,x4〉) nat5
; quadruple … LSR MODE_INHA (Byte 〈x4,x4〉) nat3
; quadruple … LSR MODE_INHX (Byte 〈x5,x4〉) nat3
; quadruple … LSR MODE_IX1  (Byte 〈x6,x4〉) nat6
; quadruple … LSR MODE_IX0  (Byte 〈x7,x4〉) nat5
].

ndefinition opcode_table_HC05_23 ≝
[
  quadruple … NEG MODE_DIR1 (Byte 〈x3,x0〉) nat5
; quadruple … NEG MODE_INHA (Byte 〈x4,x0〉) nat3
; quadruple … NEG MODE_INHX (Byte 〈x5,x0〉) nat3
; quadruple … NEG MODE_IX1  (Byte 〈x6,x0〉) nat6
; quadruple … NEG MODE_IX0  (Byte 〈x7,x0〉) nat5
].

ndefinition opcode_table_HC05_24 ≝
[
  quadruple … ORA MODE_IMM1 (Byte 〈xA,xA〉) nat2
; quadruple … ORA MODE_DIR1 (Byte 〈xB,xA〉) nat3
; quadruple … ORA MODE_DIR2 (Byte 〈xC,xA〉) nat4
; quadruple … ORA MODE_IX2  (Byte 〈xD,xA〉) nat5
; quadruple … ORA MODE_IX1  (Byte 〈xE,xA〉) nat4
; quadruple … ORA MODE_IX0  (Byte 〈xF,xA〉) nat3
].

ndefinition opcode_table_HC05_25 ≝
[
  quadruple … ROL MODE_DIR1 (Byte 〈x3,x9〉) nat5
; quadruple … ROL MODE_INHA (Byte 〈x4,x9〉) nat3
; quadruple … ROL MODE_INHX (Byte 〈x5,x9〉) nat3
; quadruple … ROL MODE_IX1  (Byte 〈x6,x9〉) nat6
; quadruple … ROL MODE_IX0  (Byte 〈x7,x9〉) nat5
].

ndefinition opcode_table_HC05_26 ≝
[
  quadruple … ROR MODE_DIR1 (Byte 〈x3,x6〉) nat5
; quadruple … ROR MODE_INHA (Byte 〈x4,x6〉) nat3
; quadruple … ROR MODE_INHX (Byte 〈x5,x6〉) nat3
; quadruple … ROR MODE_IX1  (Byte 〈x6,x6〉) nat6
; quadruple … ROR MODE_IX0  (Byte 〈x7,x6〉) nat5
].

ndefinition opcode_table_HC05_27 ≝
[
  quadruple … SBC MODE_IMM1 (Byte 〈xA,x2〉) nat2
; quadruple … SBC MODE_DIR1 (Byte 〈xB,x2〉) nat3
; quadruple … SBC MODE_DIR2 (Byte 〈xC,x2〉) nat4
; quadruple … SBC MODE_IX2  (Byte 〈xD,x2〉) nat5
; quadruple … SBC MODE_IX1  (Byte 〈xE,x2〉) nat4
; quadruple … SBC MODE_IX0  (Byte 〈xF,x2〉) nat3
].

ndefinition opcode_table_HC05_28 ≝
[
  quadruple … STA MODE_DIR1 (Byte 〈xB,x7〉) nat4
; quadruple … STA MODE_DIR2 (Byte 〈xC,x7〉) nat5
; quadruple … STA MODE_IX2  (Byte 〈xD,x7〉) nat6
; quadruple … STA MODE_IX1  (Byte 〈xE,x7〉) nat5
; quadruple … STA MODE_IX0  (Byte 〈xF,x7〉) nat4
].

ndefinition opcode_table_HC05_29 ≝
[
  quadruple … STX MODE_DIR1 (Byte 〈xB,xF〉) nat4
; quadruple … STX MODE_DIR2 (Byte 〈xC,xF〉) nat5
; quadruple … STX MODE_IX2  (Byte 〈xD,xF〉) nat6
; quadruple … STX MODE_IX1  (Byte 〈xE,xF〉) nat5
; quadruple … STX MODE_IX0  (Byte 〈xF,xF〉) nat4
].

ndefinition opcode_table_HC05_30 ≝
[
  quadruple … SUB MODE_IMM1 (Byte 〈xA,x0〉) nat2
; quadruple … SUB MODE_DIR1 (Byte 〈xB,x0〉) nat3
; quadruple … SUB MODE_DIR2 (Byte 〈xC,x0〉) nat4
; quadruple … SUB MODE_IX2  (Byte 〈xD,x0〉) nat5
; quadruple … SUB MODE_IX1  (Byte 〈xE,x0〉) nat4
; quadruple … SUB MODE_IX0  (Byte 〈xF,x0〉) nat3
].

ndefinition opcode_table_HC05_31 ≝
[
  quadruple … TST MODE_DIR1 (Byte 〈x3,xD〉) nat4
; quadruple … TST MODE_INHA (Byte 〈x4,xD〉) nat3
; quadruple … TST MODE_INHX (Byte 〈x5,xD〉) nat3
; quadruple … TST MODE_IX1  (Byte 〈x6,xD〉) nat5
; quadruple … TST MODE_IX0  (Byte 〈x7,xD〉) nat4
].

ndefinition opcode_table_HC05 ≝
 opcode_table_HC05_1  @ opcode_table_HC05_2  @ opcode_table_HC05_3  @ opcode_table_HC05_4  @
 opcode_table_HC05_5  @ opcode_table_HC05_6  @ opcode_table_HC05_7  @ opcode_table_HC05_8  @
 opcode_table_HC05_9  @ opcode_table_HC05_10 @ opcode_table_HC05_11 @ opcode_table_HC05_12 @
 opcode_table_HC05_13 @ opcode_table_HC05_14 @ opcode_table_HC05_15 @ opcode_table_HC05_16 @
 opcode_table_HC05_17 @ opcode_table_HC05_18 @ opcode_table_HC05_19 @ opcode_table_HC05_20 @
 opcode_table_HC05_21 @ opcode_table_HC05_22 @ opcode_table_HC05_23 @ opcode_table_HC05_24 @
 opcode_table_HC05_25 @ opcode_table_HC05_26 @ opcode_table_HC05_27 @ opcode_table_HC05_28 @
 opcode_table_HC05_29 @ opcode_table_HC05_30 @ opcode_table_HC05_31.
