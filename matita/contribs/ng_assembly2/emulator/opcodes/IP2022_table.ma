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

include "emulator/opcodes/IP2022_pseudo.ma".
include "emulator/opcodes/IP2022_instr_mode.ma".
include "emulator/opcodes/byte_or_word.ma".
include "common/list.ma".

(* ******************* *)
(* TABELLA DELL'IP2022 *)
(* ******************* *)

(* definizione come concatenazione finale di liste per velocizzare il parsing *)
(* ogni riga e' [pseudo] [modalita' indirizzamento] [opcode esadecimale] [#cicli esecuzione] *)

ndefinition opcode_table_IP2022_1 ≝
[
  quadruple … ADD MODE_FR0_and_W (Byte 〈x1,xE〉) nat1
; quadruple … ADD MODE_FR1_and_W (Byte 〈x1,xF〉) nat1
; quadruple … ADD MODE_W_and_FR0 (Byte 〈x1,xC〉) nat1
; quadruple … ADD MODE_W_and_FR1 (Byte 〈x1,xD〉) nat1
; quadruple … ADD MODE_IMM8      (Byte 〈x7,xB〉) nat1
].

ndefinition opcode_table_IP2022_2 ≝
[
  quadruple … ADDC MODE_FR0_and_W (Byte 〈x5,xE〉) nat1
; quadruple … ADDC MODE_FR1_and_W (Byte 〈x5,xF〉) nat1
; quadruple … ADDC MODE_W_and_FR0 (Byte 〈x5,xC〉) nat1
; quadruple … ADDC MODE_W_and_FR1 (Byte 〈x5,xD〉) nat1
].

ndefinition opcode_table_IP2022_3 ≝
[
  quadruple … AND MODE_FR0_and_W (Byte 〈x1,x6〉) nat1
; quadruple … AND MODE_FR1_and_W (Byte 〈x1,x7〉) nat1
; quadruple … AND MODE_W_and_FR0 (Byte 〈x1,x4〉) nat1
; quadruple … AND MODE_W_and_FR1 (Byte 〈x1,x5〉) nat1
; quadruple … AND MODE_IMM8      (Byte 〈x7,xE〉) nat1
].

ndefinition opcode_table_IP2022_4 ≝
[
  quadruple … BREAK  MODE_INH       (Word 〈〈x0,x0〉:〈x0,x1〉〉) nat1
; quadruple … BREAKX MODE_INH       (Word 〈〈x0,x0〉:〈x0,x5〉〉) nat1
; quadruple … CWDT   MODE_INH       (Word 〈〈x0,x0〉:〈x0,x4〉〉) nat1
; quadruple … FERASE MODE_INH       (Word 〈〈x0,x0〉:〈x0,x3〉〉) nat1
; quadruple … FREAD  MODE_INH       (Word 〈〈x0,x0〉:〈x1,xB〉〉) nat1
; quadruple … FWRITE MODE_INH       (Word 〈〈x0,x0〉:〈x1,xA〉〉) nat1
; quadruple … INT    MODE_INH       (Word 〈〈x0,x0〉:〈x0,x6〉〉) nat3
; quadruple … IREAD  MODE_INHADDR   (Word 〈〈x0,x0〉:〈x1,x9〉〉) nat4 (* only blocking implemented *)
; quadruple … IREAD  MODE_INHADDRpp (Word 〈〈x0,x0〉:〈x1,xD〉〉) nat4 (* only blocking implemented *)
; quadruple … IWRITE MODE_INHADDR   (Word 〈〈x0,x0〉:〈x1,x8〉〉) nat4 (* only blocking implemented *)
; quadruple … IWRITE MODE_INHADDRpp (Word 〈〈x0,x0〉:〈x1,xC〉〉) nat4 (* only blocking implemented *)
; quadruple … NOP    MODE_INH       (Word 〈〈x0,x0〉:〈x0,x0〉〉) nat1
; quadruple … RET    MODE_INH       (Word 〈〈x0,x0〉:〈x0,x7〉〉) nat3
; quadruple … RETNP  MODE_INH       (Word 〈〈x0,x0〉:〈x0,x2〉〉) nat3
].

ndefinition opcode_table_IP2022_5 ≝
[
  quadruple … CALL (MODE_IMM13 t00) (Byte 〈xC,x0〉) nat3
; quadruple … CALL (MODE_IMM13 t01) (Byte 〈xC,x1〉) nat3
; quadruple … CALL (MODE_IMM13 t02) (Byte 〈xC,x2〉) nat3
; quadruple … CALL (MODE_IMM13 t03) (Byte 〈xC,x3〉) nat3
; quadruple … CALL (MODE_IMM13 t04) (Byte 〈xC,x4〉) nat3
; quadruple … CALL (MODE_IMM13 t05) (Byte 〈xC,x5〉) nat3
; quadruple … CALL (MODE_IMM13 t06) (Byte 〈xC,x6〉) nat3
; quadruple … CALL (MODE_IMM13 t07) (Byte 〈xC,x7〉) nat3
; quadruple … CALL (MODE_IMM13 t08) (Byte 〈xC,x8〉) nat3
; quadruple … CALL (MODE_IMM13 t09) (Byte 〈xC,x9〉) nat3
; quadruple … CALL (MODE_IMM13 t0A) (Byte 〈xC,xA〉) nat3
; quadruple … CALL (MODE_IMM13 t0B) (Byte 〈xC,xB〉) nat3
; quadruple … CALL (MODE_IMM13 t0C) (Byte 〈xC,xC〉) nat3
; quadruple … CALL (MODE_IMM13 t0D) (Byte 〈xC,xD〉) nat3
; quadruple … CALL (MODE_IMM13 t0E) (Byte 〈xC,xE〉) nat3
; quadruple … CALL (MODE_IMM13 t0F) (Byte 〈xC,xF〉) nat3
; quadruple … CALL (MODE_IMM13 t10) (Byte 〈xD,x0〉) nat3
; quadruple … CALL (MODE_IMM13 t11) (Byte 〈xD,x1〉) nat3
; quadruple … CALL (MODE_IMM13 t12) (Byte 〈xD,x2〉) nat3
; quadruple … CALL (MODE_IMM13 t13) (Byte 〈xD,x3〉) nat3
; quadruple … CALL (MODE_IMM13 t14) (Byte 〈xD,x4〉) nat3
; quadruple … CALL (MODE_IMM13 t15) (Byte 〈xD,x5〉) nat3
; quadruple … CALL (MODE_IMM13 t16) (Byte 〈xD,x6〉) nat3
; quadruple … CALL (MODE_IMM13 t17) (Byte 〈xD,x7〉) nat3
; quadruple … CALL (MODE_IMM13 t18) (Byte 〈xD,x8〉) nat3
; quadruple … CALL (MODE_IMM13 t19) (Byte 〈xD,x9〉) nat3
; quadruple … CALL (MODE_IMM13 t1A) (Byte 〈xD,xA〉) nat3
; quadruple … CALL (MODE_IMM13 t1B) (Byte 〈xD,xB〉) nat3
; quadruple … CALL (MODE_IMM13 t1C) (Byte 〈xD,xC〉) nat3
; quadruple … CALL (MODE_IMM13 t1D) (Byte 〈xD,xD〉) nat3
; quadruple … CALL (MODE_IMM13 t1E) (Byte 〈xD,xE〉) nat3
; quadruple … CALL (MODE_IMM13 t1F) (Byte 〈xD,xF〉) nat3
].

ndefinition opcode_table_IP2022_6 ≝
[
  quadruple … CLR MODE_FR0_and_W (Byte 〈x0,x6〉) nat1
; quadruple … CLR MODE_FR1_and_W (Byte 〈x0,x7〉) nat1
].

ndefinition opcode_table_IP2022_7 ≝
[
  quadruple … CLRB (MODE_FR0n o0) (Byte 〈x8,x0〉) nat1
; quadruple … CLRB (MODE_FR1n o0) (Byte 〈x8,x1〉) nat1
; quadruple … CLRB (MODE_FR0n o1) (Byte 〈x8,x2〉) nat1
; quadruple … CLRB (MODE_FR1n o1) (Byte 〈x8,x3〉) nat1
; quadruple … CLRB (MODE_FR0n o2) (Byte 〈x8,x4〉) nat1
; quadruple … CLRB (MODE_FR1n o2) (Byte 〈x8,x5〉) nat1
; quadruple … CLRB (MODE_FR0n o3) (Byte 〈x8,x6〉) nat1
; quadruple … CLRB (MODE_FR1n o3) (Byte 〈x8,x7〉) nat1
; quadruple … CLRB (MODE_FR0n o4) (Byte 〈x8,x8〉) nat1
; quadruple … CLRB (MODE_FR1n o4) (Byte 〈x8,x9〉) nat1
; quadruple … CLRB (MODE_FR0n o5) (Byte 〈x8,xA〉) nat1
; quadruple … CLRB (MODE_FR1n o5) (Byte 〈x8,xB〉) nat1
; quadruple … CLRB (MODE_FR0n o6) (Byte 〈x8,xC〉) nat1
; quadruple … CLRB (MODE_FR1n o6) (Byte 〈x8,xD〉) nat1
; quadruple … CLRB (MODE_FR0n o7) (Byte 〈x8,xE〉) nat1
; quadruple … CLRB (MODE_FR1n o7) (Byte 〈x8,xF〉) nat1
].

ndefinition opcode_table_IP2022_8 ≝
[
  quadruple … CMP MODE_W_and_FR0 (Byte 〈x0,x4〉) nat1
; quadruple … CMP MODE_W_and_FR1 (Byte 〈x0,x5〉) nat1
; quadruple … CMP MODE_IMM8      (Byte 〈x7,x9〉) nat1
].

ndefinition opcode_table_IP2022_9 ≝
[
  quadruple … CSE MODE_W_and_FR0 (Byte 〈x4,x2〉) nat1
; quadruple … CSE MODE_W_and_FR1 (Byte 〈x4,x3〉) nat1
; quadruple … CSE MODE_IMM8      (Byte 〈x7,x7〉) nat1
].

ndefinition opcode_table_IP2022_10 ≝
[
  quadruple … CSNE MODE_W_and_FR0 (Byte 〈x4,x0〉) nat1
; quadruple … CSNE MODE_W_and_FR1 (Byte 〈x4,x1〉) nat1
; quadruple … CSNE MODE_IMM8      (Byte 〈x7,x6〉) nat1
].

ndefinition opcode_table_IP2022_11 ≝
[
  quadruple … DEC MODE_FR0_and_W (Byte 〈x0,xE〉) nat1
; quadruple … DEC MODE_FR1_and_W (Byte 〈x0,xF〉) nat1
; quadruple … DEC MODE_W_and_FR0 (Byte 〈x0,xC〉) nat1
; quadruple … DEC MODE_W_and_FR1 (Byte 〈x0,xD〉) nat1
].

ndefinition opcode_table_IP2022_12 ≝
[
  quadruple … DECSNZ MODE_FR0_and_W (Byte 〈x4,xE〉) nat1
; quadruple … DECSNZ MODE_FR1_and_W (Byte 〈x4,xF〉) nat1
; quadruple … DECSNZ MODE_W_and_FR0 (Byte 〈x4,xC〉) nat1
; quadruple … DECSNZ MODE_W_and_FR1 (Byte 〈x4,xD〉) nat1
].

ndefinition opcode_table_IP2022_13 ≝
[
  quadruple … DECSZ MODE_FR0_and_W (Byte 〈x2,xE〉) nat1
; quadruple … DECSZ MODE_FR1_and_W (Byte 〈x2,xF〉) nat1
; quadruple … DECSZ MODE_W_and_FR0 (Byte 〈x2,xC〉) nat1
; quadruple … DECSZ MODE_W_and_FR1 (Byte 〈x2,xD〉) nat1
].

ndefinition opcode_table_IP2022_14 ≝
[
  quadruple … INC MODE_FR0_and_W (Byte 〈x2,xA〉) nat1
; quadruple … INC MODE_FR1_and_W (Byte 〈x2,xB〉) nat1
; quadruple … INC MODE_W_and_FR0 (Byte 〈x2,x8〉) nat1
; quadruple … INC MODE_W_and_FR1 (Byte 〈x2,x9〉) nat1
].

ndefinition opcode_table_IP2022_15 ≝
[
  quadruple … INCSNZ MODE_FR0_and_W (Byte 〈x5,xA〉) nat1
; quadruple … INCSNZ MODE_FR1_and_W (Byte 〈x5,xB〉) nat1
; quadruple … INCSNZ MODE_W_and_FR0 (Byte 〈x5,x8〉) nat1
; quadruple … INCSNZ MODE_W_and_FR1 (Byte 〈x5,x9〉) nat1
].

ndefinition opcode_table_IP2022_16 ≝
[
  quadruple … INCSZ MODE_FR0_and_W (Byte 〈x3,xE〉) nat1
; quadruple … INCSZ MODE_FR1_and_W (Byte 〈x3,xF〉) nat1
; quadruple … INCSZ MODE_W_and_FR0 (Byte 〈x3,xC〉) nat1
; quadruple … INCSZ MODE_W_and_FR1 (Byte 〈x3,xD〉) nat1
].

ndefinition opcode_table_IP2022_17 ≝
[
  quadruple … JMP (MODE_IMM13 t00) (Byte 〈xE,x0〉) nat3
; quadruple … JMP (MODE_IMM13 t01) (Byte 〈xE,x1〉) nat3
; quadruple … JMP (MODE_IMM13 t02) (Byte 〈xE,x2〉) nat3
; quadruple … JMP (MODE_IMM13 t03) (Byte 〈xE,x3〉) nat3
; quadruple … JMP (MODE_IMM13 t04) (Byte 〈xE,x4〉) nat3
; quadruple … JMP (MODE_IMM13 t05) (Byte 〈xE,x5〉) nat3
; quadruple … JMP (MODE_IMM13 t06) (Byte 〈xE,x6〉) nat3
; quadruple … JMP (MODE_IMM13 t07) (Byte 〈xE,x7〉) nat3
; quadruple … JMP (MODE_IMM13 t08) (Byte 〈xE,x8〉) nat3
; quadruple … JMP (MODE_IMM13 t09) (Byte 〈xE,x9〉) nat3
; quadruple … JMP (MODE_IMM13 t0A) (Byte 〈xE,xA〉) nat3
; quadruple … JMP (MODE_IMM13 t0B) (Byte 〈xE,xB〉) nat3
; quadruple … JMP (MODE_IMM13 t0C) (Byte 〈xE,xC〉) nat3
; quadruple … JMP (MODE_IMM13 t0D) (Byte 〈xE,xD〉) nat3
; quadruple … JMP (MODE_IMM13 t0E) (Byte 〈xE,xE〉) nat3
; quadruple … JMP (MODE_IMM13 t0F) (Byte 〈xE,xF〉) nat3
; quadruple … JMP (MODE_IMM13 t10) (Byte 〈xF,x0〉) nat3
; quadruple … JMP (MODE_IMM13 t11) (Byte 〈xF,x1〉) nat3
; quadruple … JMP (MODE_IMM13 t12) (Byte 〈xF,x2〉) nat3
; quadruple … JMP (MODE_IMM13 t13) (Byte 〈xF,x3〉) nat3
; quadruple … JMP (MODE_IMM13 t14) (Byte 〈xF,x4〉) nat3
; quadruple … JMP (MODE_IMM13 t15) (Byte 〈xF,x5〉) nat3
; quadruple … JMP (MODE_IMM13 t16) (Byte 〈xF,x6〉) nat3
; quadruple … JMP (MODE_IMM13 t17) (Byte 〈xF,x7〉) nat3
; quadruple … JMP (MODE_IMM13 t18) (Byte 〈xF,x8〉) nat3
; quadruple … JMP (MODE_IMM13 t19) (Byte 〈xF,x9〉) nat3
; quadruple … JMP (MODE_IMM13 t1A) (Byte 〈xF,xA〉) nat3
; quadruple … JMP (MODE_IMM13 t1B) (Byte 〈xF,xB〉) nat3
; quadruple … JMP (MODE_IMM13 t1C) (Byte 〈xF,xC〉) nat3
; quadruple … JMP (MODE_IMM13 t1D) (Byte 〈xF,xD〉) nat3
; quadruple … JMP (MODE_IMM13 t1E) (Byte 〈xF,xE〉) nat3
; quadruple … JMP (MODE_IMM13 t1F) (Byte 〈xF,xF〉) nat3
].

ndefinition opcode_table_IP2022_18 ≝
[
  quadruple … LOADH MODE_IMM8 (Byte 〈x7,x0〉) nat1
; quadruple … LOADL MODE_IMM8 (Byte 〈x7,x1〉) nat1
].

ndefinition opcode_table_IP2022_19 ≝
[
  quadruple … MOV MODE_FR0_and_W (Byte 〈x0,x2〉) nat1
; quadruple … MOV MODE_FR1_and_W (Byte 〈x0,x3〉) nat1
; quadruple … MOV MODE_W_and_FR0 (Byte 〈x2,x0〉) nat1
; quadruple … MOV MODE_W_and_FR1 (Byte 〈x2,x1〉) nat1
; quadruple … MOV MODE_IMM8      (Byte 〈x7,xC〉) nat1
].

ndefinition opcode_table_IP2022_20 ≝
[
  quadruple … MULS MODE_W_and_FR0 (Byte 〈x5,x4〉) nat1
; quadruple … MULS MODE_W_and_FR1 (Byte 〈x5,x5〉) nat1
; quadruple … MULS MODE_IMM8      (Byte 〈x7,x3〉) nat1
].

ndefinition opcode_table_IP2022_21 ≝
[
  quadruple … MULU MODE_W_and_FR0 (Byte 〈x5,x0〉) nat1
; quadruple … MULU MODE_W_and_FR1 (Byte 〈x5,x1〉) nat1
; quadruple … MULU MODE_IMM8      (Byte 〈x7,x2〉) nat1
].

ndefinition opcode_table_IP2022_22 ≝
[
  quadruple … NOT MODE_FR0_and_W (Byte 〈x2,x6〉) nat1
; quadruple … NOT MODE_FR1_and_W (Byte 〈x2,x7〉) nat1
; quadruple … NOT MODE_W_and_FR0 (Byte 〈x2,x4〉) nat1
; quadruple … NOT MODE_W_and_FR1 (Byte 〈x2,x5〉) nat1
].

ndefinition opcode_table_IP2022_23 ≝
[
  quadruple … OR MODE_FR0_and_W (Byte 〈x1,x2〉) nat1
; quadruple … OR MODE_FR1_and_W (Byte 〈x1,x3〉) nat1
; quadruple … OR MODE_W_and_FR0 (Byte 〈x1,x0〉) nat1
; quadruple … OR MODE_W_and_FR1 (Byte 〈x1,x1〉) nat1
; quadruple … OR MODE_IMM8      (Byte 〈x7,xD〉) nat1
].

ndefinition opcode_table_IP2022_24 ≝
[
  quadruple … PAGE (MODE_IMM3 o0) (Word 〈〈x0,x0〉:〈x1,x0〉〉) nat1
; quadruple … PAGE (MODE_IMM3 o1) (Word 〈〈x0,x0〉:〈x1,x1〉〉) nat1
; quadruple … PAGE (MODE_IMM3 o2) (Word 〈〈x0,x0〉:〈x1,x2〉〉) nat1
; quadruple … PAGE (MODE_IMM3 o3) (Word 〈〈x0,x0〉:〈x1,x3〉〉) nat1
; quadruple … PAGE (MODE_IMM3 o4) (Word 〈〈x0,x0〉:〈x1,x4〉〉) nat1
; quadruple … PAGE (MODE_IMM3 o5) (Word 〈〈x0,x0〉:〈x1,x5〉〉) nat1
; quadruple … PAGE (MODE_IMM3 o6) (Word 〈〈x0,x0〉:〈x1,x6〉〉) nat1
; quadruple … PAGE (MODE_IMM3 o7) (Word 〈〈x0,x0〉:〈x1,x7〉〉) nat1
].

ndefinition opcode_table_IP2022_25 ≝
[
  quadruple … POP  MODE_FR0_and_W (Byte 〈x4,x6〉) nat1
; quadruple … POP  MODE_FR1_and_W (Byte 〈x4,x7〉) nat1
; quadruple … PUSH MODE_W_and_FR0 (Byte 〈x4,x4〉) nat1
; quadruple … PUSH MODE_W_and_FR1 (Byte 〈x4,x5〉) nat1
; quadruple … PUSH MODE_IMM8      (Byte 〈x7,x4〉) nat1
].

ndefinition opcode_table_IP2022_26 ≝
[
  quadruple … RETI (MODE_IMM3 o0) (Word 〈〈x0,x0〉:〈x0,x8〉〉) nat3
; quadruple … RETI (MODE_IMM3 o1) (Word 〈〈x0,x0〉:〈x0,x9〉〉) nat3
; quadruple … RETI (MODE_IMM3 o2) (Word 〈〈x0,x0〉:〈x0,xA〉〉) nat3
; quadruple … RETI (MODE_IMM3 o3) (Word 〈〈x0,x0〉:〈x0,xB〉〉) nat3
; quadruple … RETI (MODE_IMM3 o4) (Word 〈〈x0,x0〉:〈x0,xC〉〉) nat3
; quadruple … RETI (MODE_IMM3 o5) (Word 〈〈x0,x0〉:〈x0,xD〉〉) nat3
; quadruple … RETI (MODE_IMM3 o6) (Word 〈〈x0,x0〉:〈x0,xE〉〉) nat3
; quadruple … RETI (MODE_IMM3 o7) (Word 〈〈x0,x0〉:〈x0,xF〉〉) nat3
].

ndefinition opcode_table_IP2022_27 ≝
[ quadruple … RETW MODE_IMM8 (Byte 〈x7,x8〉) nat3 ].

ndefinition opcode_table_IP2022_28 ≝
[
  quadruple … RL MODE_FR0_and_W (Byte 〈x3,x6〉) nat1
; quadruple … RL MODE_FR1_and_W (Byte 〈x3,x7〉) nat1
; quadruple … RL MODE_W_and_FR0 (Byte 〈x3,x4〉) nat1
; quadruple … RL MODE_W_and_FR1 (Byte 〈x3,x5〉) nat1
].

ndefinition opcode_table_IP2022_29 ≝
[
  quadruple … RR MODE_FR0_and_W (Byte 〈x3,x2〉) nat1
; quadruple … RR MODE_FR1_and_W (Byte 〈x3,x3〉) nat1
; quadruple … RR MODE_W_and_FR0 (Byte 〈x3,x0〉) nat1
; quadruple … RR MODE_W_and_FR1 (Byte 〈x3,x1〉) nat1
].

ndefinition opcode_table_IP2022_30 ≝
[
  quadruple … SB (MODE_FR0n o0) (Byte 〈xB,x0〉) nat1
; quadruple … SB (MODE_FR1n o0) (Byte 〈xB,x1〉) nat1
; quadruple … SB (MODE_FR0n o1) (Byte 〈xB,x2〉) nat1
; quadruple … SB (MODE_FR1n o1) (Byte 〈xB,x3〉) nat1
; quadruple … SB (MODE_FR0n o2) (Byte 〈xB,x4〉) nat1
; quadruple … SB (MODE_FR1n o2) (Byte 〈xB,x5〉) nat1
; quadruple … SB (MODE_FR0n o3) (Byte 〈xB,x6〉) nat1
; quadruple … SB (MODE_FR1n o3) (Byte 〈xB,x7〉) nat1
; quadruple … SB (MODE_FR0n o4) (Byte 〈xB,x8〉) nat1
; quadruple … SB (MODE_FR1n o4) (Byte 〈xB,x9〉) nat1
; quadruple … SB (MODE_FR0n o5) (Byte 〈xB,xA〉) nat1
; quadruple … SB (MODE_FR1n o5) (Byte 〈xB,xB〉) nat1
; quadruple … SB (MODE_FR0n o6) (Byte 〈xB,xC〉) nat1
; quadruple … SB (MODE_FR1n o6) (Byte 〈xB,xD〉) nat1
; quadruple … SB (MODE_FR0n o7) (Byte 〈xB,xE〉) nat1
; quadruple … SB (MODE_FR1n o7) (Byte 〈xB,xF〉) nat1
].

ndefinition opcode_table_IP2022_31 ≝
[
  quadruple … SETB (MODE_FR0n o0) (Byte 〈x9,x0〉) nat1
; quadruple … SETB (MODE_FR1n o0) (Byte 〈x9,x1〉) nat1
; quadruple … SETB (MODE_FR0n o1) (Byte 〈x9,x2〉) nat1
; quadruple … SETB (MODE_FR1n o1) (Byte 〈x9,x3〉) nat1
; quadruple … SETB (MODE_FR0n o2) (Byte 〈x9,x4〉) nat1
; quadruple … SETB (MODE_FR1n o2) (Byte 〈x9,x5〉) nat1
; quadruple … SETB (MODE_FR0n o3) (Byte 〈x9,x6〉) nat1
; quadruple … SETB (MODE_FR1n o3) (Byte 〈x9,x7〉) nat1
; quadruple … SETB (MODE_FR0n o4) (Byte 〈x9,x8〉) nat1
; quadruple … SETB (MODE_FR1n o4) (Byte 〈x9,x9〉) nat1
; quadruple … SETB (MODE_FR0n o5) (Byte 〈x9,xA〉) nat1
; quadruple … SETB (MODE_FR1n o5) (Byte 〈x9,xB〉) nat1
; quadruple … SETB (MODE_FR0n o6) (Byte 〈x9,xC〉) nat1
; quadruple … SETB (MODE_FR1n o6) (Byte 〈x9,xD〉) nat1
; quadruple … SETB (MODE_FR0n o7) (Byte 〈x9,xE〉) nat1
; quadruple … SETB (MODE_FR1n o7) (Byte 〈x9,xF〉) nat1
].

ndefinition opcode_table_IP2022_32 ≝
[
  quadruple … SNB (MODE_FR0n o0) (Byte 〈xA,x0〉) nat1
; quadruple … SNB (MODE_FR1n o0) (Byte 〈xA,x1〉) nat1
; quadruple … SNB (MODE_FR0n o1) (Byte 〈xA,x2〉) nat1
; quadruple … SNB (MODE_FR1n o1) (Byte 〈xA,x3〉) nat1
; quadruple … SNB (MODE_FR0n o2) (Byte 〈xA,x4〉) nat1
; quadruple … SNB (MODE_FR1n o2) (Byte 〈xA,x5〉) nat1
; quadruple … SNB (MODE_FR0n o3) (Byte 〈xA,x6〉) nat1
; quadruple … SNB (MODE_FR1n o3) (Byte 〈xA,x7〉) nat1
; quadruple … SNB (MODE_FR0n o4) (Byte 〈xA,x8〉) nat1
; quadruple … SNB (MODE_FR1n o4) (Byte 〈xA,x9〉) nat1
; quadruple … SNB (MODE_FR0n o5) (Byte 〈xA,xA〉) nat1
; quadruple … SNB (MODE_FR1n o5) (Byte 〈xA,xB〉) nat1
; quadruple … SNB (MODE_FR0n o6) (Byte 〈xA,xC〉) nat1
; quadruple … SNB (MODE_FR1n o6) (Byte 〈xA,xD〉) nat1
; quadruple … SNB (MODE_FR0n o7) (Byte 〈xA,xE〉) nat1
; quadruple … SNB (MODE_FR1n o7) (Byte 〈xA,xF〉) nat1
].

ndefinition opcode_table_IP2022_33 ≝
[ quadruple … SPEED MODE_IMM8 (Byte 〈x0,x1〉) nat1 ].

ndefinition opcode_table_IP2022_34 ≝
[
  quadruple … SUB MODE_FR0_and_W (Byte 〈x0,xA〉) nat1
; quadruple … SUB MODE_FR1_and_W (Byte 〈x0,xB〉) nat1
; quadruple … SUB MODE_W_and_FR0 (Byte 〈x0,x8〉) nat1
; quadruple … SUB MODE_W_and_FR1 (Byte 〈x0,x9〉) nat1
; quadruple … SUB MODE_IMM8      (Byte 〈x7,xA〉) nat1
].

ndefinition opcode_table_IP2022_35 ≝
[
  quadruple … SUBC MODE_FR0_and_W (Byte 〈x4,xA〉) nat1
; quadruple … SUBC MODE_FR1_and_W (Byte 〈x4,xB〉) nat1
; quadruple … SUBC MODE_W_and_FR0 (Byte 〈x4,x8〉) nat1
; quadruple … SUBC MODE_W_and_FR1 (Byte 〈x4,x9〉) nat1
].

ndefinition opcode_table_IP2022_36 ≝
[
  quadruple … SWAP MODE_FR0_and_W (Byte 〈x3,xA〉) nat1
; quadruple … SWAP MODE_FR1_and_W (Byte 〈x3,xB〉) nat1
; quadruple … SWAP MODE_W_and_FR0 (Byte 〈x3,x8〉) nat1
; quadruple … SWAP MODE_W_and_FR1 (Byte 〈x3,x9〉) nat1
].

ndefinition opcode_table_IP2022_37 ≝
[
  quadruple … TEST MODE_FR0_and_W (Byte 〈x2,x2〉) nat1
; quadruple … TEST MODE_FR1_and_W (Byte 〈x2,x3〉) nat1
].

ndefinition opcode_table_IP2022_38 ≝
[
  quadruple … XOR MODE_FR0_and_W (Byte 〈x1,xA〉) nat1
; quadruple … XOR MODE_FR1_and_W (Byte 〈x1,xB〉) nat1
; quadruple … XOR MODE_W_and_FR0 (Byte 〈x1,x8〉) nat1
; quadruple … XOR MODE_W_and_FR1 (Byte 〈x1,x9〉) nat1
; quadruple … XOR MODE_IMM8      (Byte 〈x7,xF〉) nat1
].

ndefinition opcode_table_IP2022 ≝
 opcode_table_IP2022_1  @ opcode_table_IP2022_2  @ opcode_table_IP2022_3  @ opcode_table_IP2022_4  @
 opcode_table_IP2022_5  @ opcode_table_IP2022_6  @ opcode_table_IP2022_7  @ opcode_table_IP2022_8  @
 opcode_table_IP2022_9  @ opcode_table_IP2022_10 @ opcode_table_IP2022_11 @ opcode_table_IP2022_12 @
 opcode_table_IP2022_13 @ opcode_table_IP2022_14 @ opcode_table_IP2022_15 @ opcode_table_IP2022_16 @
 opcode_table_IP2022_17 @ opcode_table_IP2022_18 @ opcode_table_IP2022_19 @ opcode_table_IP2022_20 @
 opcode_table_IP2022_21 @ opcode_table_IP2022_22 @ opcode_table_IP2022_23 @ opcode_table_IP2022_24 @
 opcode_table_IP2022_25 @ opcode_table_IP2022_26 @ opcode_table_IP2022_27 @ opcode_table_IP2022_28 @
 opcode_table_IP2022_29 @ opcode_table_IP2022_30 @ opcode_table_IP2022_31 @ opcode_table_IP2022_32 @
 opcode_table_IP2022_33 @ opcode_table_IP2022_34 @ opcode_table_IP2022_35 @ opcode_table_IP2022_36 @
 opcode_table_IP2022_37 @ opcode_table_IP2022_38.
