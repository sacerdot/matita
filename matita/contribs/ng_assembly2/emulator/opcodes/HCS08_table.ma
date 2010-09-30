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

(* ****************** *)
(* TABELLA DELL'HCS08 *)
(* ****************** *)

(* definizione come concatenazione finale di liste per velocizzare il parsing *)
(* ogni riga e' [pseudo] [modalita' indirizzamento] [opcode esadecimale] [#cicli esecuzione] *)

ndefinition opcode_table_HCS08_1 ≝
[
  quadruple … ADC MODE_IMM1 (Byte 〈xA,x9〉) nat2
; quadruple … ADC MODE_DIR1 (Byte 〈xB,x9〉) nat3
; quadruple … ADC MODE_DIR2 (Byte 〈xC,x9〉) nat4
; quadruple … ADC MODE_IX2  (Byte 〈xD,x9〉) nat4
; quadruple … ADC MODE_IX1  (Byte 〈xE,x9〉) nat3
; quadruple … ADC MODE_IX0  (Byte 〈xF,x9〉) nat3
; quadruple … ADC MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x9〉〉) nat5
; quadruple … ADC MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x9〉〉) nat4
].

ndefinition opcode_table_HCS08_2 ≝
[
  quadruple … ADD MODE_IMM1 (Byte 〈xA,xB〉) nat2
; quadruple … ADD MODE_DIR1 (Byte 〈xB,xB〉) nat3
; quadruple … ADD MODE_DIR2 (Byte 〈xC,xB〉) nat4
; quadruple … ADD MODE_IX2  (Byte 〈xD,xB〉) nat4
; quadruple … ADD MODE_IX1  (Byte 〈xE,xB〉) nat3
; quadruple … ADD MODE_IX0  (Byte 〈xF,xB〉) nat3
; quadruple … ADD MODE_SP2  (Word 〈〈x9,xE〉:〈xD,xB〉〉) nat5
; quadruple … ADD MODE_SP1  (Word 〈〈x9,xE〉:〈xE,xB〉〉) nat4
].

ndefinition opcode_table_HCS08_3 ≝
[
  quadruple … AND MODE_IMM1 (Byte 〈xA,x4〉) nat2
; quadruple … AND MODE_DIR1 (Byte 〈xB,x4〉) nat3
; quadruple … AND MODE_DIR2 (Byte 〈xC,x4〉) nat4
; quadruple … AND MODE_IX2  (Byte 〈xD,x4〉) nat4
; quadruple … AND MODE_IX1  (Byte 〈xE,x4〉) nat3
; quadruple … AND MODE_IX0  (Byte 〈xF,x4〉) nat3
; quadruple … AND MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x4〉〉) nat5
; quadruple … AND MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x4〉〉) nat4
].

ndefinition opcode_table_HCS08_4 ≝
[
  quadruple … ASL MODE_DIR1 (Byte 〈x3,x8〉) nat5
; quadruple … ASL MODE_INHA (Byte 〈x4,x8〉) nat1
; quadruple … ASL MODE_INHX (Byte 〈x5,x8〉) nat1
; quadruple … ASL MODE_IX1  (Byte 〈x6,x8〉) nat5
; quadruple … ASL MODE_IX0  (Byte 〈x7,x8〉) nat4
; quadruple … ASL MODE_SP1  (Word 〈〈x9,xE〉:〈x6,x8〉〉) nat6
].

ndefinition opcode_table_HCS08_5 ≝
[
  quadruple … ASR MODE_DIR1 (Byte 〈x3,x7〉) nat5
; quadruple … ASR MODE_INHA (Byte 〈x4,x7〉) nat1
; quadruple … ASR MODE_INHX (Byte 〈x5,x7〉) nat1
; quadruple … ASR MODE_IX1  (Byte 〈x6,x7〉) nat5
; quadruple … ASR MODE_IX0  (Byte 〈x7,x7〉) nat4
; quadruple … ASR MODE_SP1  (Word 〈〈x9,xE〉:〈x6,x7〉〉) nat6
].

ndefinition opcode_table_HCS08_6 ≝
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
; quadruple … BGE  MODE_IMM1 (Byte 〈x9,x0〉) nat3
; quadruple … BLT  MODE_IMM1 (Byte 〈x9,x1〉) nat3
; quadruple … BGT  MODE_IMM1 (Byte 〈x9,x2〉) nat3
; quadruple … BLE  MODE_IMM1 (Byte 〈x9,x3〉) nat3
].

ndefinition opcode_table_HCS08_7 ≝
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

ndefinition opcode_table_HCS08_8 ≝
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

ndefinition opcode_table_HCS08_9 ≝
[
  quadruple … BIT MODE_IMM1 (Byte 〈xA,x5〉) nat2
; quadruple … BIT MODE_DIR1 (Byte 〈xB,x5〉) nat3
; quadruple … BIT MODE_DIR2 (Byte 〈xC,x5〉) nat4
; quadruple … BIT MODE_IX2  (Byte 〈xD,x5〉) nat4
; quadruple … BIT MODE_IX1  (Byte 〈xE,x5〉) nat3
; quadruple … BIT MODE_IX0  (Byte 〈xF,x5〉) nat3
; quadruple … BIT MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x5〉〉) nat5
; quadruple … BIT MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x5〉〉) nat4
].

ndefinition opcode_table_HCS08_10 ≝
[
  quadruple … MUL  MODE_INH  (Byte 〈x4,x2〉) nat5
; quadruple … DIV  MODE_INH  (Byte 〈x5,x2〉) nat6
; quadruple … NSA  MODE_INH  (Byte 〈x6,x2〉) nat1
; quadruple … DAA  MODE_INH  (Byte 〈x7,x2〉) nat1
; quadruple … RTI  MODE_INH  (Byte 〈x8,x0〉) nat9
; quadruple … RTS  MODE_INH  (Byte 〈x8,x1〉) nat6
; quadruple … SWI  MODE_INH  (Byte 〈x8,x3〉) nat11
; quadruple … BGND MODE_INH  (Byte 〈x8,x2〉) nat5
; quadruple … TAP  MODE_INH  (Byte 〈x8,x4〉) nat1
; quadruple … TPA  MODE_INH  (Byte 〈x8,x5〉) nat1
; quadruple … PULA MODE_INH  (Byte 〈x8,x6〉) nat3
; quadruple … PSHA MODE_INH  (Byte 〈x8,x7〉) nat2
; quadruple … PULX MODE_INH  (Byte 〈x8,x8〉) nat3
; quadruple … PSHX MODE_INH  (Byte 〈x8,x9〉) nat2
; quadruple … PULH MODE_INH  (Byte 〈x8,xA〉) nat3
; quadruple … PSHH MODE_INH  (Byte 〈x8,xB〉) nat2
; quadruple … STOP MODE_INH  (Byte 〈x8,xE〉) nat2
; quadruple … WAIT MODE_INH  (Byte 〈x8,xF〉) nat2
; quadruple … TXS  MODE_INH  (Byte 〈x9,x4〉) nat2
; quadruple … TSX  MODE_INH  (Byte 〈x9,x5〉) nat2
; quadruple … TAX  MODE_INH  (Byte 〈x9,x7〉) nat1
; quadruple … CLC  MODE_INH  (Byte 〈x9,x8〉) nat1
; quadruple … SEC  MODE_INH  (Byte 〈x9,x9〉) nat1
; quadruple … CLI  MODE_INH  (Byte 〈x9,xA〉) nat1
; quadruple … SEI  MODE_INH  (Byte 〈x9,xB〉) nat1
; quadruple … RSP  MODE_INH  (Byte 〈x9,xC〉) nat1
; quadruple … NOP  MODE_INH  (Byte 〈x9,xD〉) nat1
; quadruple … TXA  MODE_INH  (Byte 〈x9,xF〉) nat1
; quadruple … AIS  MODE_IMM1 (Byte 〈xA,x7〉) nat2
; quadruple … AIX  MODE_IMM1 (Byte 〈xA,xF〉) nat2
].

ndefinition opcode_table_HCS08_11 ≝
[
  quadruple … CBEQA MODE_DIR1_and_IMM1 (Byte 〈x3,x1〉) nat5
; quadruple … CBEQA MODE_IMM1_and_IMM1 (Byte 〈x4,x1〉) nat4
; quadruple … CBEQX MODE_IMM1_and_IMM1 (Byte 〈x5,x1〉) nat4
; quadruple … CBEQA MODE_IX1p_and_IMM1 (Byte 〈x6,x1〉) nat5
; quadruple … CBEQA MODE_IX0p_and_IMM1 (Byte 〈x7,x1〉) nat5
; quadruple … CBEQA MODE_SP1_and_IMM1  (Word 〈〈x9,xE〉:〈x6,x1〉〉) nat6
].

ndefinition opcode_table_HCS08_12 ≝
[
  quadruple … CLR MODE_DIR1 (Byte 〈x3,xF〉) nat5
; quadruple … CLR MODE_INHA (Byte 〈x4,xF〉) nat1
; quadruple … CLR MODE_INHX (Byte 〈x5,xF〉) nat1
; quadruple … CLR MODE_IX1  (Byte 〈x6,xF〉) nat5
; quadruple … CLR MODE_IX0  (Byte 〈x7,xF〉) nat4
; quadruple … CLR MODE_INHH (Byte 〈x8,xC〉) nat1
; quadruple … CLR MODE_SP1  (Word 〈〈x9,xE〉:〈x6,xF〉〉) nat6
].

ndefinition opcode_table_HCS08_13 ≝
[
  quadruple … CMP MODE_IMM1 (Byte 〈xA,x1〉) nat2
; quadruple … CMP MODE_DIR1 (Byte 〈xB,x1〉) nat3
; quadruple … CMP MODE_DIR2 (Byte 〈xC,x1〉) nat4
; quadruple … CMP MODE_IX2  (Byte 〈xD,x1〉) nat4
; quadruple … CMP MODE_IX1  (Byte 〈xE,x1〉) nat3
; quadruple … CMP MODE_IX0  (Byte 〈xF,x1〉) nat3
; quadruple … CMP MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x1〉〉) nat5
; quadruple … CMP MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x1〉〉) nat4
].

ndefinition opcode_table_HCS08_14 ≝
[
  quadruple … COM MODE_DIR1 (Byte 〈x3,x3〉) nat5
; quadruple … COM MODE_INHA (Byte 〈x4,x3〉) nat1
; quadruple … COM MODE_INHX (Byte 〈x5,x3〉) nat1
; quadruple … COM MODE_IX1  (Byte 〈x6,x3〉) nat5
; quadruple … COM MODE_IX0  (Byte 〈x7,x3〉) nat4
; quadruple … COM MODE_SP1  (Word 〈〈x9,xE〉:〈x6,x3〉〉) nat6
].

ndefinition opcode_table_HCS08_15 ≝
[
  quadruple … CPHX MODE_DIR2 (Byte 〈x3,xE〉) nat6
; quadruple … CPHX MODE_IMM2 (Byte 〈x6,x5〉) nat3
; quadruple … CPHX MODE_DIR1 (Byte 〈x7,x5〉) nat5
; quadruple … CPHX MODE_SP1  (Word 〈〈x9,xE〉:〈xF,x3〉〉) nat6

; quadruple … LDHX MODE_DIR2 (Byte 〈x3,x2〉) nat5
; quadruple … LDHX MODE_IMM2 (Byte 〈x4,x5〉) nat3
; quadruple … LDHX MODE_DIR1 (Byte 〈x5,x5〉) nat4
; quadruple … LDHX MODE_IX0  (Word 〈〈x9,xE〉:〈xA,xE〉〉) nat5
; quadruple … LDHX MODE_IX2  (Word 〈〈x9,xE〉:〈xB,xE〉〉) nat6
; quadruple … LDHX MODE_IX1  (Word 〈〈x9,xE〉:〈xC,xE〉〉) nat5
; quadruple … LDHX MODE_SP1  (Word 〈〈x9,xE〉:〈xF,xE〉〉) nat5

; quadruple … STHX MODE_DIR1 (Byte 〈x3,x5〉) nat4
; quadruple … STHX MODE_DIR2 (Byte 〈x9,x6〉) nat5
; quadruple … STHX MODE_SP1  (Word 〈〈x9,xE〉:〈xF,xF〉〉) nat5
].

ndefinition opcode_table_HCS08_16 ≝
[
  quadruple … CPX MODE_IMM1 (Byte 〈xA,x3〉) nat2
; quadruple … CPX MODE_DIR1 (Byte 〈xB,x3〉) nat3
; quadruple … CPX MODE_DIR2 (Byte 〈xC,x3〉) nat4
; quadruple … CPX MODE_IX2  (Byte 〈xD,x3〉) nat4
; quadruple … CPX MODE_IX1  (Byte 〈xE,x3〉) nat3
; quadruple … CPX MODE_IX0  (Byte 〈xF,x3〉) nat3
; quadruple … CPX MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x3〉〉) nat5
; quadruple … CPX MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x3〉〉) nat4
].

ndefinition opcode_table_HCS08_17 ≝
[
  quadruple … DBNZ MODE_DIR1_and_IMM1 (Byte 〈x3,xB〉) nat7
; quadruple … DBNZ MODE_INHA_and_IMM1 (Byte 〈x4,xB〉) nat4
; quadruple … DBNZ MODE_INHX_and_IMM1 (Byte 〈x5,xB〉) nat4
; quadruple … DBNZ MODE_IX1_and_IMM1  (Byte 〈x6,xB〉) nat7
; quadruple … DBNZ MODE_IX0_and_IMM1  (Byte 〈x7,xB〉) nat6
; quadruple … DBNZ MODE_SP1_and_IMM1  (Word 〈〈x9,xE〉:〈x6,xB〉〉) nat8
].

ndefinition opcode_table_HCS08_18 ≝
[
  quadruple … DEC MODE_DIR1 (Byte 〈x3,xA〉) nat5
; quadruple … DEC MODE_INHA (Byte 〈x4,xA〉) nat1
; quadruple … DEC MODE_INHX (Byte 〈x5,xA〉) nat1
; quadruple … DEC MODE_IX1  (Byte 〈x6,xA〉) nat5
; quadruple … DEC MODE_IX0  (Byte 〈x7,xA〉) nat4
; quadruple … DEC MODE_SP1  (Word 〈〈x9,xE〉:〈x6,xA〉〉) nat6
].

ndefinition opcode_table_HCS08_19 ≝
[
  quadruple … EOR MODE_IMM1 (Byte 〈xA,x8〉) nat2
; quadruple … EOR MODE_DIR1 (Byte 〈xB,x8〉) nat3
; quadruple … EOR MODE_DIR2 (Byte 〈xC,x8〉) nat4
; quadruple … EOR MODE_IX2  (Byte 〈xD,x8〉) nat4
; quadruple … EOR MODE_IX1  (Byte 〈xE,x8〉) nat3
; quadruple … EOR MODE_IX0  (Byte 〈xF,x8〉) nat3
; quadruple … EOR MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x8〉〉) nat5
; quadruple … EOR MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x8〉〉) nat4
].

ndefinition opcode_table_HCS08_20 ≝
[
  quadruple … INC MODE_DIR1 (Byte 〈x3,xC〉) nat5
; quadruple … INC MODE_INHA (Byte 〈x4,xC〉) nat1
; quadruple … INC MODE_INHX (Byte 〈x5,xC〉) nat1
; quadruple … INC MODE_IX1  (Byte 〈x6,xC〉) nat5
; quadruple … INC MODE_IX0  (Byte 〈x7,xC〉) nat4
; quadruple … INC MODE_SP1  (Word 〈〈x9,xE〉:〈x6,xC〉〉) nat6
].

ndefinition opcode_table_HCS08_21 ≝
[
  quadruple … JMP MODE_IMM1EXT  (Byte 〈xB,xC〉) nat3
; quadruple … JMP MODE_IMM2     (Byte 〈xC,xC〉) nat4
; quadruple … JMP MODE_INHX2ADD (Byte 〈xD,xC〉) nat4
; quadruple … JMP MODE_INHX1ADD (Byte 〈xE,xC〉) nat3
; quadruple … JMP MODE_INHX0ADD (Byte 〈xF,xC〉) nat3
].

ndefinition opcode_table_HCS08_22 ≝
[
  quadruple … BSR MODE_IMM1     (Byte 〈xA,xD〉) nat5
; quadruple … JSR MODE_IMM1EXT  (Byte 〈xB,xD〉) nat5
; quadruple … JSR MODE_IMM2     (Byte 〈xC,xD〉) nat6
; quadruple … JSR MODE_INHX2ADD (Byte 〈xD,xD〉) nat6
; quadruple … JSR MODE_INHX1ADD (Byte 〈xE,xD〉) nat5
; quadruple … JSR MODE_INHX0ADD (Byte 〈xF,xD〉) nat5
].

ndefinition opcode_table_HCS08_23 ≝
[
  quadruple … LDA MODE_IMM1 (Byte 〈xA,x6〉) nat2
; quadruple … LDA MODE_DIR1 (Byte 〈xB,x6〉) nat3
; quadruple … LDA MODE_DIR2 (Byte 〈xC,x6〉) nat4
; quadruple … LDA MODE_IX2  (Byte 〈xD,x6〉) nat4
; quadruple … LDA MODE_IX1  (Byte 〈xE,x6〉) nat3
; quadruple … LDA MODE_IX0  (Byte 〈xF,x6〉) nat3
; quadruple … LDA MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x6〉〉) nat5
; quadruple … LDA MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x6〉〉) nat4
].

ndefinition opcode_table_HCS08_24 ≝
[
  quadruple … LDX MODE_IMM1 (Byte 〈xA,xE〉) nat2
; quadruple … LDX MODE_DIR1 (Byte 〈xB,xE〉) nat3
; quadruple … LDX MODE_DIR2 (Byte 〈xC,xE〉) nat4
; quadruple … LDX MODE_IX2  (Byte 〈xD,xE〉) nat4
; quadruple … LDX MODE_IX1  (Byte 〈xE,xE〉) nat3
; quadruple … LDX MODE_IX0  (Byte 〈xF,xE〉) nat3
; quadruple … LDX MODE_SP2  (Word 〈〈x9,xE〉:〈xD,xE〉〉) nat5
; quadruple … LDX MODE_SP1  (Word 〈〈x9,xE〉:〈xE,xE〉〉) nat4
].

ndefinition opcode_table_HCS08_25 ≝
[
  quadruple … LSR MODE_DIR1 (Byte 〈x3,x4〉) nat5
; quadruple … LSR MODE_INHA (Byte 〈x4,x4〉) nat1
; quadruple … LSR MODE_INHX (Byte 〈x5,x4〉) nat1
; quadruple … LSR MODE_IX1  (Byte 〈x6,x4〉) nat5
; quadruple … LSR MODE_IX0  (Byte 〈x7,x4〉) nat4
; quadruple … LSR MODE_SP1  (Word 〈〈x9,xE〉:〈x6,x4〉〉) nat6
].

ndefinition opcode_table_HCS08_26 ≝
[
  quadruple … MOV MODE_DIR1_to_DIR1 (Byte 〈x4,xE〉) nat5
; quadruple … MOV MODE_DIR1_to_IX0p (Byte 〈x5,xE〉) nat5
; quadruple … MOV MODE_IMM1_to_DIR1 (Byte 〈x6,xE〉) nat4
; quadruple … MOV MODE_IX0p_to_DIR1 (Byte 〈x7,xE〉) nat5
].

ndefinition opcode_table_HCS08_27 ≝
[
  quadruple … NEG MODE_DIR1 (Byte 〈x3,x0〉) nat5
; quadruple … NEG MODE_INHA (Byte 〈x4,x0〉) nat1
; quadruple … NEG MODE_INHX (Byte 〈x5,x0〉) nat1
; quadruple … NEG MODE_IX1  (Byte 〈x6,x0〉) nat5
; quadruple … NEG MODE_IX0  (Byte 〈x7,x0〉) nat4
; quadruple … NEG MODE_SP1  (Word 〈〈x9,xE〉:〈x6,x0〉〉) nat6
].

ndefinition opcode_table_HCS08_28 ≝
[
  quadruple … ORA MODE_IMM1 (Byte 〈xA,xA〉) nat2
; quadruple … ORA MODE_DIR1 (Byte 〈xB,xA〉) nat3
; quadruple … ORA MODE_DIR2 (Byte 〈xC,xA〉) nat4
; quadruple … ORA MODE_IX2  (Byte 〈xD,xA〉) nat4
; quadruple … ORA MODE_IX1  (Byte 〈xE,xA〉) nat3
; quadruple … ORA MODE_IX0  (Byte 〈xF,xA〉) nat3
; quadruple … ORA MODE_SP2  (Word 〈〈x9,xE〉:〈xD,xA〉〉) nat5
; quadruple … ORA MODE_SP1  (Word 〈〈x9,xE〉:〈xE,xA〉〉) nat4
].

ndefinition opcode_table_HCS08_29 ≝
[
  quadruple … ROL MODE_DIR1 (Byte 〈x3,x9〉) nat5
; quadruple … ROL MODE_INHA (Byte 〈x4,x9〉) nat1
; quadruple … ROL MODE_INHX (Byte 〈x5,x9〉) nat1
; quadruple … ROL MODE_IX1  (Byte 〈x6,x9〉) nat5
; quadruple … ROL MODE_IX0  (Byte 〈x7,x9〉) nat4
; quadruple … ROL MODE_SP1  (Word 〈〈x9,xE〉:〈x6,x9〉〉) nat6
].

ndefinition opcode_table_HCS08_30 ≝
[
  quadruple … ROR MODE_DIR1 (Byte 〈x3,x6〉) nat5
; quadruple … ROR MODE_INHA (Byte 〈x4,x6〉) nat1
; quadruple … ROR MODE_INHX (Byte 〈x5,x6〉) nat1
; quadruple … ROR MODE_IX1  (Byte 〈x6,x6〉) nat5
; quadruple … ROR MODE_IX0  (Byte 〈x7,x6〉) nat4
; quadruple … ROR MODE_SP1  (Word 〈〈x9,xE〉:〈x6,x6〉〉) nat6
].

ndefinition opcode_table_HCS08_31 ≝
[
  quadruple … SBC MODE_IMM1 (Byte 〈xA,x2〉) nat2
; quadruple … SBC MODE_DIR1 (Byte 〈xB,x2〉) nat3
; quadruple … SBC MODE_DIR2 (Byte 〈xC,x2〉) nat4
; quadruple … SBC MODE_IX2  (Byte 〈xD,x2〉) nat4
; quadruple … SBC MODE_IX1  (Byte 〈xE,x2〉) nat3
; quadruple … SBC MODE_IX0  (Byte 〈xF,x2〉) nat3
; quadruple … SBC MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x2〉〉) nat5
; quadruple … SBC MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x2〉〉) nat4
].

ndefinition opcode_table_HCS08_32 ≝
[
  quadruple … STA MODE_DIR1 (Byte 〈xB,x7〉) nat3
; quadruple … STA MODE_DIR2 (Byte 〈xC,x7〉) nat4
; quadruple … STA MODE_IX2  (Byte 〈xD,x7〉) nat4
; quadruple … STA MODE_IX1  (Byte 〈xE,x7〉) nat3
; quadruple … STA MODE_IX0  (Byte 〈xF,x7〉) nat2
; quadruple … STA MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x7〉〉) nat5
; quadruple … STA MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x7〉〉) nat4
].

ndefinition opcode_table_HCS08_33 ≝
[
  quadruple … STX MODE_DIR1 (Byte 〈xB,xF〉) nat3
; quadruple … STX MODE_DIR2 (Byte 〈xC,xF〉) nat4
; quadruple … STX MODE_IX2  (Byte 〈xD,xF〉) nat4
; quadruple … STX MODE_IX1  (Byte 〈xE,xF〉) nat3
; quadruple … STX MODE_IX0  (Byte 〈xF,xF〉) nat2
; quadruple … STX MODE_SP2  (Word 〈〈x9,xE〉:〈xD,xF〉〉) nat5
; quadruple … STX MODE_SP1  (Word 〈〈x9,xE〉:〈xE,xF〉〉) nat4
].

ndefinition opcode_table_HCS08_34 ≝
[
  quadruple … SUB MODE_IMM1 (Byte 〈xA,x0〉) nat2
; quadruple … SUB MODE_DIR1 (Byte 〈xB,x0〉) nat3
; quadruple … SUB MODE_DIR2 (Byte 〈xC,x0〉) nat4
; quadruple … SUB MODE_IX2  (Byte 〈xD,x0〉) nat4
; quadruple … SUB MODE_IX1  (Byte 〈xE,x0〉) nat3
; quadruple … SUB MODE_IX0  (Byte 〈xF,x0〉) nat3
; quadruple … SUB MODE_SP2  (Word 〈〈x9,xE〉:〈xD,x0〉〉) nat5
; quadruple … SUB MODE_SP1  (Word 〈〈x9,xE〉:〈xE,x0〉〉) nat4
].

ndefinition opcode_table_HCS08_35 ≝
[
  quadruple … TST MODE_DIR1 (Byte 〈x3,xD〉) nat4
; quadruple … TST MODE_INHA (Byte 〈x4,xD〉) nat1
; quadruple … TST MODE_INHX (Byte 〈x5,xD〉) nat1
; quadruple … TST MODE_IX1  (Byte 〈x6,xD〉) nat4
; quadruple … TST MODE_IX0  (Byte 〈x7,xD〉) nat3
; quadruple … TST MODE_SP1  (Word 〈〈x9,xE〉:〈x6,xD〉〉) nat5
].

ndefinition opcode_table_HCS08 ≝
opcode_table_HCS08_1  @ opcode_table_HCS08_2  @ opcode_table_HCS08_3  @ opcode_table_HCS08_4  @
opcode_table_HCS08_5  @ opcode_table_HCS08_6  @ opcode_table_HCS08_7  @ opcode_table_HCS08_8  @
opcode_table_HCS08_9  @ opcode_table_HCS08_10 @ opcode_table_HCS08_11 @ opcode_table_HCS08_12 @
opcode_table_HCS08_13 @ opcode_table_HCS08_14 @ opcode_table_HCS08_15 @ opcode_table_HCS08_16 @
opcode_table_HCS08_17 @ opcode_table_HCS08_18 @ opcode_table_HCS08_19 @ opcode_table_HCS08_20 @
opcode_table_HCS08_21 @ opcode_table_HCS08_22 @ opcode_table_HCS08_23 @ opcode_table_HCS08_24 @
opcode_table_HCS08_25 @ opcode_table_HCS08_26 @ opcode_table_HCS08_27 @ opcode_table_HCS08_28 @
opcode_table_HCS08_29 @ opcode_table_HCS08_30 @ opcode_table_HCS08_31 @ opcode_table_HCS08_32 @
opcode_table_HCS08_33 @ opcode_table_HCS08_34 @ opcode_table_HCS08_35.
