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
(* TABELLA DELL'RS08 *)
(* ***************** *)

(* definizione come concatenazione finale di liste per velocizzare il parsing *)
(* ogni riga e' [pseudo] [modalita' indirizzamento] [opcode esadecimale] [#cicli esecuzione] *)

ndefinition opcode_table_RS08_1 ≝
[ 
  quadruple … ADC MODE_IMM1 (Byte 〈xA,x9〉) 〈x0,x2〉
; quadruple … ADC MODE_DIR1 (Byte 〈xB,x9〉) 〈x0,x3〉
].

ndefinition opcode_table_RS08_2 ≝
[ 
  quadruple … ADD MODE_IMM1     (Byte 〈xA,xB〉) 〈x0,x2〉
; quadruple … ADD MODE_DIR1     (Byte 〈xB,xB〉) 〈x0,x3〉
; quadruple … ADD (MODE_TNY x0) (Byte 〈x6,x0〉) 〈x0,x3〉
; quadruple … ADD (MODE_TNY x1) (Byte 〈x6,x1〉) 〈x0,x3〉
; quadruple … ADD (MODE_TNY x2) (Byte 〈x6,x2〉) 〈x0,x3〉
; quadruple … ADD (MODE_TNY x3) (Byte 〈x6,x3〉) 〈x0,x3〉
; quadruple … ADD (MODE_TNY x4) (Byte 〈x6,x4〉) 〈x0,x3〉
; quadruple … ADD (MODE_TNY x5) (Byte 〈x6,x5〉) 〈x0,x3〉
; quadruple … ADD (MODE_TNY x6) (Byte 〈x6,x6〉) 〈x0,x3〉
; quadruple … ADD (MODE_TNY x7) (Byte 〈x6,x7〉) 〈x0,x3〉
; quadruple … ADD (MODE_TNY x8) (Byte 〈x6,x8〉) 〈x0,x3〉
; quadruple … ADD (MODE_TNY x9) (Byte 〈x6,x9〉) 〈x0,x3〉
; quadruple … ADD (MODE_TNY xA) (Byte 〈x6,xA〉) 〈x0,x3〉
; quadruple … ADD (MODE_TNY xB) (Byte 〈x6,xB〉) 〈x0,x3〉
; quadruple … ADD (MODE_TNY xC) (Byte 〈x6,xC〉) 〈x0,x3〉
; quadruple … ADD (MODE_TNY xD) (Byte 〈x6,xD〉) 〈x0,x3〉
; quadruple … ADD (MODE_TNY xE) (Byte 〈x6,xE〉) 〈x0,x3〉
; quadruple … ADD (MODE_TNY xF) (Byte 〈x6,xF〉) 〈x0,x3〉
].

ndefinition opcode_table_RS08_3 ≝
[ 
  quadruple … AND MODE_IMM1 (Byte 〈xA,x4〉) 〈x0,x2〉
; quadruple … AND MODE_DIR1 (Byte 〈xB,x4〉) 〈x0,x3〉
].

ndefinition opcode_table_RS08_4 ≝
[
  quadruple … ASL MODE_INHA (Byte 〈x4,x8〉) 〈x0,x1〉
].

ndefinition opcode_table_RS08_5 ≝
[
  quadruple … BRA MODE_IMM1 (Byte 〈x3,x0〉) 〈x0,x3〉
; quadruple … BCC MODE_IMM1 (Byte 〈x3,x4〉) 〈x0,x3〉
; quadruple … BCS MODE_IMM1 (Byte 〈x3,x5〉) 〈x0,x3〉
; quadruple … BNE MODE_IMM1 (Byte 〈x3,x6〉) 〈x0,x3〉
; quadruple … BEQ MODE_IMM1 (Byte 〈x3,x7〉) 〈x0,x3〉
].

ndefinition opcode_table_RS08_6 ≝
[
  quadruple … BSETn (MODE_DIRn o0) (Byte 〈x1,x0〉) 〈x0,x5〉
; quadruple … BCLRn (MODE_DIRn o0) (Byte 〈x1,x1〉) 〈x0,x5〉
; quadruple … BSETn (MODE_DIRn o1) (Byte 〈x1,x2〉) 〈x0,x5〉
; quadruple … BCLRn (MODE_DIRn o1) (Byte 〈x1,x3〉) 〈x0,x5〉
; quadruple … BSETn (MODE_DIRn o2) (Byte 〈x1,x4〉) 〈x0,x5〉
; quadruple … BCLRn (MODE_DIRn o2) (Byte 〈x1,x5〉) 〈x0,x5〉
; quadruple … BSETn (MODE_DIRn o3) (Byte 〈x1,x6〉) 〈x0,x5〉
; quadruple … BCLRn (MODE_DIRn o3) (Byte 〈x1,x7〉) 〈x0,x5〉
; quadruple … BSETn (MODE_DIRn o4) (Byte 〈x1,x8〉) 〈x0,x5〉
; quadruple … BCLRn (MODE_DIRn o4) (Byte 〈x1,x9〉) 〈x0,x5〉
; quadruple … BSETn (MODE_DIRn o5) (Byte 〈x1,xA〉) 〈x0,x5〉
; quadruple … BCLRn (MODE_DIRn o5) (Byte 〈x1,xB〉) 〈x0,x5〉
; quadruple … BSETn (MODE_DIRn o6) (Byte 〈x1,xC〉) 〈x0,x5〉
; quadruple … BCLRn (MODE_DIRn o6) (Byte 〈x1,xD〉) 〈x0,x5〉
; quadruple … BSETn (MODE_DIRn o7) (Byte 〈x1,xE〉) 〈x0,x5〉
; quadruple … BCLRn (MODE_DIRn o7) (Byte 〈x1,xF〉) 〈x0,x5〉
].

ndefinition opcode_table_RS08_7 ≝
[
  quadruple … BRSETn (MODE_DIRn_and_IMM1 o0) (Byte 〈x0,x0〉) 〈x0,x5〉
; quadruple … BRCLRn (MODE_DIRn_and_IMM1 o0) (Byte 〈x0,x1〉) 〈x0,x5〉
; quadruple … BRSETn (MODE_DIRn_and_IMM1 o1) (Byte 〈x0,x2〉) 〈x0,x5〉
; quadruple … BRCLRn (MODE_DIRn_and_IMM1 o1) (Byte 〈x0,x3〉) 〈x0,x5〉
; quadruple … BRSETn (MODE_DIRn_and_IMM1 o2) (Byte 〈x0,x4〉) 〈x0,x5〉
; quadruple … BRCLRn (MODE_DIRn_and_IMM1 o2) (Byte 〈x0,x5〉) 〈x0,x5〉
; quadruple … BRSETn (MODE_DIRn_and_IMM1 o3) (Byte 〈x0,x6〉) 〈x0,x5〉
; quadruple … BRCLRn (MODE_DIRn_and_IMM1 o3) (Byte 〈x0,x7〉) 〈x0,x5〉
; quadruple … BRSETn (MODE_DIRn_and_IMM1 o4) (Byte 〈x0,x8〉) 〈x0,x5〉
; quadruple … BRCLRn (MODE_DIRn_and_IMM1 o4) (Byte 〈x0,x9〉) 〈x0,x5〉
; quadruple … BRSETn (MODE_DIRn_and_IMM1 o5) (Byte 〈x0,xA〉) 〈x0,x5〉
; quadruple … BRCLRn (MODE_DIRn_and_IMM1 o5) (Byte 〈x0,xB〉) 〈x0,x5〉
; quadruple … BRSETn (MODE_DIRn_and_IMM1 o6) (Byte 〈x0,xC〉) 〈x0,x5〉
; quadruple … BRCLRn (MODE_DIRn_and_IMM1 o6) (Byte 〈x0,xD〉) 〈x0,x5〉
; quadruple … BRSETn (MODE_DIRn_and_IMM1 o7) (Byte 〈x0,xE〉) 〈x0,x5〉
; quadruple … BRCLRn (MODE_DIRn_and_IMM1 o7) (Byte 〈x0,xF〉) 〈x0,x5〉
].

ndefinition opcode_table_RS08_8 ≝
[
  quadruple … CLC  MODE_INH (Byte 〈x3,x8〉) 〈x0,x1〉
; quadruple … SEC  MODE_INH (Byte 〈x3,x9〉) 〈x0,x1〉
; quadruple … SLA  MODE_INH (Byte 〈x4,x2〉) 〈x0,x1〉
; quadruple … SHA  MODE_INH (Byte 〈x4,x5〉) 〈x0,x1〉
; quadruple … NOP  MODE_INH (Byte 〈xA,xC〉) 〈x0,x1〉
; quadruple … STOP MODE_INH (Byte 〈xA,xE〉) 〈x0,x2〉
; quadruple … WAIT MODE_INH (Byte 〈xA,xF〉) 〈x0,x2〉
; quadruple … RTS  MODE_INH (Byte 〈xB,xE〉) 〈x0,x3〉
; quadruple … BGND MODE_INH (Byte 〈xB,xF〉) 〈x0,x5〉
].

ndefinition opcode_table_RS08_9 ≝
[
  quadruple … CBEQA MODE_DIR1_and_IMM1 (Byte 〈x3,x1〉) 〈x0,x5〉
; quadruple … CBEQA MODE_IMM1_and_IMM1 (Byte 〈x4,x1〉) 〈x0,x4〉
].

ndefinition opcode_table_RS08_10 ≝
[
  quadruple … CLR MODE_DIR1      (Byte 〈x3,xF〉) 〈x0,x3〉
; quadruple … CLR MODE_INHA      (Byte 〈x4,xF〉) 〈x0,x1〉
; quadruple … CLR (MODE_SRT t00) (Byte 〈x8,x0〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t01) (Byte 〈x8,x1〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t02) (Byte 〈x8,x2〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t03) (Byte 〈x8,x3〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t04) (Byte 〈x8,x4〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t05) (Byte 〈x8,x5〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t06) (Byte 〈x8,x6〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t07) (Byte 〈x8,x7〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t08) (Byte 〈x8,x8〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t09) (Byte 〈x8,x9〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t0A) (Byte 〈x8,xA〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t0B) (Byte 〈x8,xB〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t0C) (Byte 〈x8,xC〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t0D) (Byte 〈x8,xD〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t0E) (Byte 〈x8,xE〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t0F) (Byte 〈x8,xF〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t10) (Byte 〈x9,x0〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t11) (Byte 〈x9,x1〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t12) (Byte 〈x9,x2〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t13) (Byte 〈x9,x3〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t14) (Byte 〈x9,x4〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t15) (Byte 〈x9,x5〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t16) (Byte 〈x9,x6〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t17) (Byte 〈x9,x7〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t18) (Byte 〈x9,x8〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t19) (Byte 〈x9,x9〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t1A) (Byte 〈x9,xA〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t1B) (Byte 〈x9,xB〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t1C) (Byte 〈x9,xC〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t1D) (Byte 〈x9,xD〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t1E) (Byte 〈x9,xE〉) 〈x0,x2〉
; quadruple … CLR (MODE_SRT t1F) (Byte 〈x9,xF〉) 〈x0,x2〉
].

ndefinition opcode_table_RS08_11 ≝
[
  quadruple … CMP MODE_IMM1 (Byte 〈xA,x1〉) 〈x0,x2〉
; quadruple … CMP MODE_DIR1 (Byte 〈xB,x1〉) 〈x0,x3〉
].

ndefinition opcode_table_RS08_12 ≝
[
  quadruple … COM MODE_INHA (Byte 〈x4,x3〉) 〈x0,x1〉
].

ndefinition opcode_table_RS08_13 ≝
[
  quadruple … DBNZ MODE_DIR1_and_IMM1 (Byte 〈x3,xB〉) 〈x0,x7〉
; quadruple … DBNZ MODE_INHA_and_IMM1 (Byte 〈x4,xB〉) 〈x0,x4〉
].

ndefinition opcode_table_RS08_14 ≝
[
  quadruple … DEC MODE_DIR1     (Byte 〈x3,xA〉) 〈x0,x5〉
; quadruple … DEC MODE_INHA     (Byte 〈x4,xA〉) 〈x0,x1〉
; quadruple … DEC (MODE_TNY x0) (Byte 〈x5,x0〉) 〈x0,x4〉
; quadruple … DEC (MODE_TNY x1) (Byte 〈x5,x1〉) 〈x0,x4〉
; quadruple … DEC (MODE_TNY x2) (Byte 〈x5,x2〉) 〈x0,x4〉
; quadruple … DEC (MODE_TNY x3) (Byte 〈x5,x3〉) 〈x0,x4〉
; quadruple … DEC (MODE_TNY x4) (Byte 〈x5,x4〉) 〈x0,x4〉
; quadruple … DEC (MODE_TNY x5) (Byte 〈x5,x5〉) 〈x0,x4〉
; quadruple … DEC (MODE_TNY x6) (Byte 〈x5,x6〉) 〈x0,x4〉
; quadruple … DEC (MODE_TNY x7) (Byte 〈x5,x7〉) 〈x0,x4〉
; quadruple … DEC (MODE_TNY x8) (Byte 〈x5,x8〉) 〈x0,x4〉
; quadruple … DEC (MODE_TNY x9) (Byte 〈x5,x9〉) 〈x0,x4〉
; quadruple … DEC (MODE_TNY xA) (Byte 〈x5,xA〉) 〈x0,x4〉
; quadruple … DEC (MODE_TNY xB) (Byte 〈x5,xB〉) 〈x0,x4〉
; quadruple … DEC (MODE_TNY xC) (Byte 〈x5,xC〉) 〈x0,x4〉
; quadruple … DEC (MODE_TNY xD) (Byte 〈x5,xD〉) 〈x0,x4〉
; quadruple … DEC (MODE_TNY xE) (Byte 〈x5,xE〉) 〈x0,x4〉
; quadruple … DEC (MODE_TNY xF) (Byte 〈x5,xF〉) 〈x0,x4〉
].

ndefinition opcode_table_RS08_15 ≝
[ 
  quadruple … EOR MODE_IMM1 (Byte 〈xA,x8〉) 〈x0,x2〉
; quadruple … EOR MODE_DIR1 (Byte 〈xB,x8〉) 〈x0,x3〉
].

ndefinition opcode_table_RS08_16 ≝
[
  quadruple … INC MODE_DIR1     (Byte 〈x3,xC〉) 〈x0,x5〉
; quadruple … INC MODE_INHA     (Byte 〈x4,xC〉) 〈x0,x1〉
; quadruple … INC (MODE_TNY x0) (Byte 〈x2,x0〉) 〈x0,x4〉
; quadruple … INC (MODE_TNY x1) (Byte 〈x2,x1〉) 〈x0,x4〉
; quadruple … INC (MODE_TNY x2) (Byte 〈x2,x2〉) 〈x0,x4〉
; quadruple … INC (MODE_TNY x3) (Byte 〈x2,x3〉) 〈x0,x4〉
; quadruple … INC (MODE_TNY x4) (Byte 〈x2,x4〉) 〈x0,x4〉
; quadruple … INC (MODE_TNY x5) (Byte 〈x2,x5〉) 〈x0,x4〉
; quadruple … INC (MODE_TNY x6) (Byte 〈x2,x6〉) 〈x0,x4〉
; quadruple … INC (MODE_TNY x7) (Byte 〈x2,x7〉) 〈x0,x4〉
; quadruple … INC (MODE_TNY x8) (Byte 〈x2,x8〉) 〈x0,x4〉
; quadruple … INC (MODE_TNY x9) (Byte 〈x2,x9〉) 〈x0,x4〉
; quadruple … INC (MODE_TNY xA) (Byte 〈x2,xA〉) 〈x0,x4〉
; quadruple … INC (MODE_TNY xB) (Byte 〈x2,xB〉) 〈x0,x4〉
; quadruple … INC (MODE_TNY xC) (Byte 〈x2,xC〉) 〈x0,x4〉
; quadruple … INC (MODE_TNY xD) (Byte 〈x2,xD〉) 〈x0,x4〉
; quadruple … INC (MODE_TNY xE) (Byte 〈x2,xE〉) 〈x0,x4〉
; quadruple … INC (MODE_TNY xF) (Byte 〈x2,xF〉) 〈x0,x4〉
].

ndefinition opcode_table_RS08_17 ≝
[
  quadruple … JMP MODE_IMM2 (Byte 〈xB,xC〉) 〈x0,x4〉
].

ndefinition opcode_table_RS08_18 ≝
[
  quadruple … BSR MODE_IMM1 (Byte 〈xA,xD〉) 〈x0,x3〉
; quadruple … JSR MODE_IMM2 (Byte 〈xB,xD〉) 〈x0,x4〉
].

ndefinition opcode_table_RS08_19 ≝
[
  quadruple … LDA MODE_IMM1      (Byte 〈xA,x6〉) 〈x0,x2〉
; quadruple … LDA MODE_DIR1      (Byte 〈xB,x6〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t00) (Byte 〈xC,x0〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t01) (Byte 〈xC,x1〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t02) (Byte 〈xC,x2〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t03) (Byte 〈xC,x3〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t04) (Byte 〈xC,x4〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t05) (Byte 〈xC,x5〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t06) (Byte 〈xC,x6〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t07) (Byte 〈xC,x7〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t08) (Byte 〈xC,x8〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t09) (Byte 〈xC,x9〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t0A) (Byte 〈xC,xA〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t0B) (Byte 〈xC,xB〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t0C) (Byte 〈xC,xC〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t0D) (Byte 〈xC,xD〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t0E) (Byte 〈xC,xE〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t0F) (Byte 〈xC,xF〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t10) (Byte 〈xD,x0〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t11) (Byte 〈xD,x1〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t12) (Byte 〈xD,x2〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t13) (Byte 〈xD,x3〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t14) (Byte 〈xD,x4〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t15) (Byte 〈xD,x5〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t16) (Byte 〈xD,x6〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t17) (Byte 〈xD,x7〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t18) (Byte 〈xD,x8〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t19) (Byte 〈xD,x9〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t1A) (Byte 〈xD,xA〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t1B) (Byte 〈xD,xB〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t1C) (Byte 〈xD,xC〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t1D) (Byte 〈xD,xD〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t1E) (Byte 〈xD,xE〉) 〈x0,x3〉
; quadruple … LDA (MODE_SRT t1F) (Byte 〈xD,xF〉) 〈x0,x3〉
].

ndefinition opcode_table_RS08_20 ≝
[
  quadruple … LSR MODE_INHA (Byte 〈x4,x4〉) 〈x0,x1〉
].

ndefinition opcode_table_RS08_21 ≝
[
  quadruple … MOV MODE_IMM1_to_DIR1 (Byte 〈x3,xE〉) 〈x0,x4〉
; quadruple … MOV MODE_DIR1_to_DIR1 (Byte 〈x4,xE〉) 〈x0,x5〉
].

ndefinition opcode_table_RS08_22 ≝
[ 
  quadruple … ORA MODE_IMM1 (Byte 〈xA,xA〉) 〈x0,x2〉
; quadruple … ORA MODE_DIR1 (Byte 〈xB,xA〉) 〈x0,x3〉
].

ndefinition opcode_table_RS08_23 ≝
[
  quadruple … ROL MODE_INHA (Byte 〈x4,x9〉) 〈x0,x1〉
].

ndefinition opcode_table_RS08_24 ≝
[
  quadruple … ROR MODE_INHA (Byte 〈x4,x6〉) 〈x0,x1〉
].

ndefinition opcode_table_RS08_25 ≝
[
  quadruple … SBC MODE_IMM1 (Byte 〈xA,x2〉) 〈x0,x2〉
; quadruple … SBC MODE_DIR1 (Byte 〈xB,x2〉) 〈x0,x3〉
].

ndefinition opcode_table_RS08_26 ≝
[
  quadruple … STA MODE_DIR1      (Byte 〈xB,x7〉) 〈x0,x3〉
; quadruple … STA (MODE_SRT t00) (Byte 〈xE,x0〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t01) (Byte 〈xE,x1〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t02) (Byte 〈xE,x2〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t03) (Byte 〈xE,x3〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t04) (Byte 〈xE,x4〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t05) (Byte 〈xE,x5〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t06) (Byte 〈xE,x6〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t07) (Byte 〈xE,x7〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t08) (Byte 〈xE,x8〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t09) (Byte 〈xE,x9〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t0A) (Byte 〈xE,xA〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t0B) (Byte 〈xE,xB〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t0C) (Byte 〈xE,xC〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t0D) (Byte 〈xE,xD〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t0E) (Byte 〈xE,xE〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t0F) (Byte 〈xE,xF〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t10) (Byte 〈xF,x0〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t11) (Byte 〈xF,x1〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t12) (Byte 〈xF,x2〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t13) (Byte 〈xF,x3〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t14) (Byte 〈xF,x4〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t15) (Byte 〈xF,x5〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t16) (Byte 〈xF,x6〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t17) (Byte 〈xF,x7〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t18) (Byte 〈xF,x8〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t19) (Byte 〈xF,x9〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t1A) (Byte 〈xF,xA〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t1B) (Byte 〈xF,xB〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t1C) (Byte 〈xF,xC〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t1D) (Byte 〈xF,xD〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t1E) (Byte 〈xF,xE〉) 〈x0,x2〉
; quadruple … STA (MODE_SRT t1F) (Byte 〈xF,xF〉) 〈x0,x2〉
].

ndefinition opcode_table_RS08_27 ≝
[ 
  quadruple … SUB MODE_IMM1     (Byte 〈xA,x0〉) 〈x0,x2〉
; quadruple … SUB MODE_DIR1     (Byte 〈xB,x0〉) 〈x0,x3〉
; quadruple … SUB (MODE_TNY x0) (Byte 〈x7,x0〉) 〈x0,x3〉
; quadruple … SUB (MODE_TNY x1) (Byte 〈x7,x1〉) 〈x0,x3〉
; quadruple … SUB (MODE_TNY x2) (Byte 〈x7,x2〉) 〈x0,x3〉
; quadruple … SUB (MODE_TNY x3) (Byte 〈x7,x3〉) 〈x0,x3〉
; quadruple … SUB (MODE_TNY x4) (Byte 〈x7,x4〉) 〈x0,x3〉
; quadruple … SUB (MODE_TNY x5) (Byte 〈x7,x5〉) 〈x0,x3〉
; quadruple … SUB (MODE_TNY x6) (Byte 〈x7,x6〉) 〈x0,x3〉
; quadruple … SUB (MODE_TNY x7) (Byte 〈x7,x7〉) 〈x0,x3〉
; quadruple … SUB (MODE_TNY x8) (Byte 〈x7,x8〉) 〈x0,x3〉
; quadruple … SUB (MODE_TNY x9) (Byte 〈x7,x9〉) 〈x0,x3〉
; quadruple … SUB (MODE_TNY xA) (Byte 〈x7,xA〉) 〈x0,x3〉
; quadruple … SUB (MODE_TNY xB) (Byte 〈x7,xB〉) 〈x0,x3〉
; quadruple … SUB (MODE_TNY xC) (Byte 〈x7,xC〉) 〈x0,x3〉
; quadruple … SUB (MODE_TNY xD) (Byte 〈x7,xD〉) 〈x0,x3〉
; quadruple … SUB (MODE_TNY xE) (Byte 〈x7,xE〉) 〈x0,x3〉
; quadruple … SUB (MODE_TNY xF) (Byte 〈x7,xF〉) 〈x0,x3〉
].

ndefinition opcode_table_RS08 ≝
opcode_table_RS08_1  @ opcode_table_RS08_2  @ opcode_table_RS08_3  @ opcode_table_RS08_4  @
opcode_table_RS08_5  @ opcode_table_RS08_6  @ opcode_table_RS08_7  @ opcode_table_RS08_8  @
opcode_table_RS08_9  @ opcode_table_RS08_10 @ opcode_table_RS08_11 @ opcode_table_RS08_12 @
opcode_table_RS08_13 @ opcode_table_RS08_14 @ opcode_table_RS08_15 @ opcode_table_RS08_16 @
opcode_table_RS08_17 @ opcode_table_RS08_18 @ opcode_table_RS08_19 @ opcode_table_RS08_20 @
opcode_table_RS08_21 @ opcode_table_RS08_22 @ opcode_table_RS08_23 @ opcode_table_RS08_24 @
opcode_table_RS08_25 @ opcode_table_RS08_26 @ opcode_table_RS08_27.
