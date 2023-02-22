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
(* TABELLA DELL'RS08 *)
(* ***************** *)

(* definizione come concatenazione finale di liste per velocizzare il parsing *)
(* ogni riga e' (any_opcode m) (instr_mode) (opcode esadecimale) (#cicli esecuzione) *)
(* NB: l'uso di any_opcode m + concatenazione finale tutte liste
       impedisce di introdurre opcode disomogenei (per mcu) *)

definition opcode_table_RS08_1 ≝
[ 
  quadrupleT ???? (anyOP RS08 ADC) MODE_IMM1 (Byte 〈xA,x9〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 ADC) MODE_DIR1 (Byte 〈xB,x9〉) 〈x0,x3〉
].

definition opcode_table_RS08_2 ≝
[ 
  quadrupleT ???? (anyOP RS08 ADD) MODE_IMM1     (Byte 〈xA,xB〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 ADD) MODE_DIR1     (Byte 〈xB,xB〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 ADD) (MODE_TNY x0) (Byte 〈x6,x0〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 ADD) (MODE_TNY x1) (Byte 〈x6,x1〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 ADD) (MODE_TNY x2) (Byte 〈x6,x2〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 ADD) (MODE_TNY x3) (Byte 〈x6,x3〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 ADD) (MODE_TNY x4) (Byte 〈x6,x4〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 ADD) (MODE_TNY x5) (Byte 〈x6,x5〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 ADD) (MODE_TNY x6) (Byte 〈x6,x6〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 ADD) (MODE_TNY x7) (Byte 〈x6,x7〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 ADD) (MODE_TNY x8) (Byte 〈x6,x8〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 ADD) (MODE_TNY x9) (Byte 〈x6,x9〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 ADD) (MODE_TNY xA) (Byte 〈x6,xA〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 ADD) (MODE_TNY xB) (Byte 〈x6,xB〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 ADD) (MODE_TNY xC) (Byte 〈x6,xC〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 ADD) (MODE_TNY xD) (Byte 〈x6,xD〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 ADD) (MODE_TNY xE) (Byte 〈x6,xE〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 ADD) (MODE_TNY xF) (Byte 〈x6,xF〉) 〈x0,x3〉
].

definition opcode_table_RS08_3 ≝
[ 
  quadrupleT ???? (anyOP RS08 AND) MODE_IMM1 (Byte 〈xA,x4〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 AND) MODE_DIR1 (Byte 〈xB,x4〉) 〈x0,x3〉
].

definition opcode_table_RS08_4 ≝
[
  quadrupleT ???? (anyOP RS08 ASL) MODE_INHA (Byte 〈x4,x8〉) 〈x0,x1〉
].

definition opcode_table_RS08_5 ≝
[
  quadrupleT ???? (anyOP RS08 BRA) MODE_IMM1 (Byte 〈x3,x0〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 BCC) MODE_IMM1 (Byte 〈x3,x4〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 BCS) MODE_IMM1 (Byte 〈x3,x5〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 BNE) MODE_IMM1 (Byte 〈x3,x6〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 BEQ) MODE_IMM1 (Byte 〈x3,x7〉) 〈x0,x3〉
].

definition opcode_table_RS08_6 ≝
[
  quadrupleT ???? (anyOP RS08 BSETn) (MODE_DIRn o0) (Byte 〈x1,x0〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BCLRn) (MODE_DIRn o0) (Byte 〈x1,x1〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BSETn) (MODE_DIRn o1) (Byte 〈x1,x2〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BCLRn) (MODE_DIRn o1) (Byte 〈x1,x3〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BSETn) (MODE_DIRn o2) (Byte 〈x1,x4〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BCLRn) (MODE_DIRn o2) (Byte 〈x1,x5〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BSETn) (MODE_DIRn o3) (Byte 〈x1,x6〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BCLRn) (MODE_DIRn o3) (Byte 〈x1,x7〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BSETn) (MODE_DIRn o4) (Byte 〈x1,x8〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BCLRn) (MODE_DIRn o4) (Byte 〈x1,x9〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BSETn) (MODE_DIRn o5) (Byte 〈x1,xA〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BCLRn) (MODE_DIRn o5) (Byte 〈x1,xB〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BSETn) (MODE_DIRn o6) (Byte 〈x1,xC〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BCLRn) (MODE_DIRn o6) (Byte 〈x1,xD〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BSETn) (MODE_DIRn o7) (Byte 〈x1,xE〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BCLRn) (MODE_DIRn o7) (Byte 〈x1,xF〉) 〈x0,x5〉
].

definition opcode_table_RS08_7 ≝
[
  quadrupleT ???? (anyOP RS08 BRSETn) (MODE_DIRn_and_IMM1 o0) (Byte 〈x0,x0〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BRCLRn) (MODE_DIRn_and_IMM1 o0) (Byte 〈x0,x1〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BRSETn) (MODE_DIRn_and_IMM1 o1) (Byte 〈x0,x2〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BRCLRn) (MODE_DIRn_and_IMM1 o1) (Byte 〈x0,x3〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BRSETn) (MODE_DIRn_and_IMM1 o2) (Byte 〈x0,x4〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BRCLRn) (MODE_DIRn_and_IMM1 o2) (Byte 〈x0,x5〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BRSETn) (MODE_DIRn_and_IMM1 o3) (Byte 〈x0,x6〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BRCLRn) (MODE_DIRn_and_IMM1 o3) (Byte 〈x0,x7〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BRSETn) (MODE_DIRn_and_IMM1 o4) (Byte 〈x0,x8〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BRCLRn) (MODE_DIRn_and_IMM1 o4) (Byte 〈x0,x9〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BRSETn) (MODE_DIRn_and_IMM1 o5) (Byte 〈x0,xA〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BRCLRn) (MODE_DIRn_and_IMM1 o5) (Byte 〈x0,xB〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BRSETn) (MODE_DIRn_and_IMM1 o6) (Byte 〈x0,xC〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BRCLRn) (MODE_DIRn_and_IMM1 o6) (Byte 〈x0,xD〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BRSETn) (MODE_DIRn_and_IMM1 o7) (Byte 〈x0,xE〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 BRCLRn) (MODE_DIRn_and_IMM1 o7) (Byte 〈x0,xF〉) 〈x0,x5〉
].

definition opcode_table_RS08_8 ≝
[
  quadrupleT ???? (anyOP RS08 CLC ) MODE_INH (Byte 〈x3,x8〉) 〈x0,x1〉
; quadrupleT ???? (anyOP RS08 SEC ) MODE_INH (Byte 〈x3,x9〉) 〈x0,x1〉
; quadrupleT ???? (anyOP RS08 SLA ) MODE_INH (Byte 〈x4,x2〉) 〈x0,x1〉
; quadrupleT ???? (anyOP RS08 SHA ) MODE_INH (Byte 〈x4,x5〉) 〈x0,x1〉
; quadrupleT ???? (anyOP RS08 NOP ) MODE_INH (Byte 〈xA,xC〉) 〈x0,x1〉
; quadrupleT ???? (anyOP RS08 STOP) MODE_INH (Byte 〈xA,xE〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 WAIT) MODE_INH (Byte 〈xA,xF〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 RTS ) MODE_INH (Byte 〈xB,xE〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 BGND) MODE_INH (Byte 〈xB,xF〉) 〈x0,x5〉
].

definition opcode_table_RS08_9 ≝
[
  quadrupleT ???? (anyOP RS08 CBEQA) MODE_DIR1_and_IMM1 (Byte 〈x3,x1〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 CBEQA) MODE_IMM1_and_IMM1 (Byte 〈x4,x1〉) 〈x0,x4〉
].

definition opcode_table_RS08_10 ≝
[
  quadrupleT ???? (anyOP RS08 CLR) MODE_DIR1      (Byte 〈x3,xF〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 CLR) MODE_INHA      (Byte 〈x4,xF〉) 〈x0,x1〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t00) (Byte 〈x8,x0〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t01) (Byte 〈x8,x1〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t02) (Byte 〈x8,x2〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t03) (Byte 〈x8,x3〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t04) (Byte 〈x8,x4〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t05) (Byte 〈x8,x5〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t06) (Byte 〈x8,x6〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t07) (Byte 〈x8,x7〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t08) (Byte 〈x8,x8〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t09) (Byte 〈x8,x9〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t0A) (Byte 〈x8,xA〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t0B) (Byte 〈x8,xB〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t0C) (Byte 〈x8,xC〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t0D) (Byte 〈x8,xD〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t0E) (Byte 〈x8,xE〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t0F) (Byte 〈x8,xF〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t10) (Byte 〈x9,x0〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t11) (Byte 〈x9,x1〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t12) (Byte 〈x9,x2〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t13) (Byte 〈x9,x3〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t14) (Byte 〈x9,x4〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t15) (Byte 〈x9,x5〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t16) (Byte 〈x9,x6〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t17) (Byte 〈x9,x7〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t18) (Byte 〈x9,x8〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t19) (Byte 〈x9,x9〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t1A) (Byte 〈x9,xA〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t1B) (Byte 〈x9,xB〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t1C) (Byte 〈x9,xC〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t1D) (Byte 〈x9,xD〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t1E) (Byte 〈x9,xE〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CLR) (MODE_SRT t1F) (Byte 〈x9,xF〉) 〈x0,x2〉
].

definition opcode_table_RS08_11 ≝
[
  quadrupleT ???? (anyOP RS08 CMP) MODE_IMM1 (Byte 〈xA,x1〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 CMP) MODE_DIR1 (Byte 〈xB,x1〉) 〈x0,x3〉
].

definition opcode_table_RS08_12 ≝
[
  quadrupleT ???? (anyOP RS08 COM) MODE_INHA (Byte 〈x4,x3〉) 〈x0,x1〉
].

definition opcode_table_RS08_13 ≝
[
  quadrupleT ???? (anyOP RS08 DBNZ) MODE_DIR1_and_IMM1 (Byte 〈x3,xB〉) 〈x0,x7〉
; quadrupleT ???? (anyOP RS08 DBNZ) MODE_INHA_and_IMM1 (Byte 〈x4,xB〉) 〈x0,x4〉
].

definition opcode_table_RS08_14 ≝
[
  quadrupleT ???? (anyOP RS08 DEC) MODE_DIR1     (Byte 〈x3,xA〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 DEC) MODE_INHA     (Byte 〈x4,xA〉) 〈x0,x1〉
; quadrupleT ???? (anyOP RS08 DEC) (MODE_TNY x0) (Byte 〈x5,x0〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 DEC) (MODE_TNY x1) (Byte 〈x5,x1〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 DEC) (MODE_TNY x2) (Byte 〈x5,x2〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 DEC) (MODE_TNY x3) (Byte 〈x5,x3〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 DEC) (MODE_TNY x4) (Byte 〈x5,x4〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 DEC) (MODE_TNY x5) (Byte 〈x5,x5〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 DEC) (MODE_TNY x6) (Byte 〈x5,x6〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 DEC) (MODE_TNY x7) (Byte 〈x5,x7〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 DEC) (MODE_TNY x8) (Byte 〈x5,x8〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 DEC) (MODE_TNY x9) (Byte 〈x5,x9〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 DEC) (MODE_TNY xA) (Byte 〈x5,xA〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 DEC) (MODE_TNY xB) (Byte 〈x5,xB〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 DEC) (MODE_TNY xC) (Byte 〈x5,xC〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 DEC) (MODE_TNY xD) (Byte 〈x5,xD〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 DEC) (MODE_TNY xE) (Byte 〈x5,xE〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 DEC) (MODE_TNY xF) (Byte 〈x5,xF〉) 〈x0,x4〉
].

definition opcode_table_RS08_15 ≝
[ 
  quadrupleT ???? (anyOP RS08 EOR) MODE_IMM1 (Byte 〈xA,x8〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 EOR) MODE_DIR1 (Byte 〈xB,x8〉) 〈x0,x3〉
].

definition opcode_table_RS08_16 ≝
[
  quadrupleT ???? (anyOP RS08 INC) MODE_DIR1     (Byte 〈x3,xC〉) 〈x0,x5〉
; quadrupleT ???? (anyOP RS08 INC) MODE_INHA     (Byte 〈x4,xC〉) 〈x0,x1〉
; quadrupleT ???? (anyOP RS08 INC) (MODE_TNY x0) (Byte 〈x2,x0〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 INC) (MODE_TNY x1) (Byte 〈x2,x1〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 INC) (MODE_TNY x2) (Byte 〈x2,x2〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 INC) (MODE_TNY x3) (Byte 〈x2,x3〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 INC) (MODE_TNY x4) (Byte 〈x2,x4〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 INC) (MODE_TNY x5) (Byte 〈x2,x5〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 INC) (MODE_TNY x6) (Byte 〈x2,x6〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 INC) (MODE_TNY x7) (Byte 〈x2,x7〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 INC) (MODE_TNY x8) (Byte 〈x2,x8〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 INC) (MODE_TNY x9) (Byte 〈x2,x9〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 INC) (MODE_TNY xA) (Byte 〈x2,xA〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 INC) (MODE_TNY xB) (Byte 〈x2,xB〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 INC) (MODE_TNY xC) (Byte 〈x2,xC〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 INC) (MODE_TNY xD) (Byte 〈x2,xD〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 INC) (MODE_TNY xE) (Byte 〈x2,xE〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 INC) (MODE_TNY xF) (Byte 〈x2,xF〉) 〈x0,x4〉
].

definition opcode_table_RS08_17 ≝
[
  quadrupleT ???? (anyOP RS08 JMP) MODE_IMM2 (Byte 〈xB,xC〉) 〈x0,x4〉
].

definition opcode_table_RS08_18 ≝
[
  quadrupleT ???? (anyOP RS08 BSR) MODE_IMM1 (Byte 〈xA,xD〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 JSR) MODE_IMM2 (Byte 〈xB,xD〉) 〈x0,x4〉
].

definition opcode_table_RS08_19 ≝
[
  quadrupleT ???? (anyOP RS08 LDA) MODE_IMM1      (Byte 〈xA,x6〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 LDA) MODE_DIR1      (Byte 〈xB,x6〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t00) (Byte 〈xC,x0〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t01) (Byte 〈xC,x1〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t02) (Byte 〈xC,x2〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t03) (Byte 〈xC,x3〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t04) (Byte 〈xC,x4〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t05) (Byte 〈xC,x5〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t06) (Byte 〈xC,x6〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t07) (Byte 〈xC,x7〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t08) (Byte 〈xC,x8〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t09) (Byte 〈xC,x9〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t0A) (Byte 〈xC,xA〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t0B) (Byte 〈xC,xB〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t0C) (Byte 〈xC,xC〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t0D) (Byte 〈xC,xD〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t0E) (Byte 〈xC,xE〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t0F) (Byte 〈xC,xF〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t10) (Byte 〈xD,x0〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t11) (Byte 〈xD,x1〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t12) (Byte 〈xD,x2〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t13) (Byte 〈xD,x3〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t14) (Byte 〈xD,x4〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t15) (Byte 〈xD,x5〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t16) (Byte 〈xD,x6〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t17) (Byte 〈xD,x7〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t18) (Byte 〈xD,x8〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t19) (Byte 〈xD,x9〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t1A) (Byte 〈xD,xA〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t1B) (Byte 〈xD,xB〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t1C) (Byte 〈xD,xC〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t1D) (Byte 〈xD,xD〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t1E) (Byte 〈xD,xE〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 LDA) (MODE_SRT t1F) (Byte 〈xD,xF〉) 〈x0,x3〉
].

definition opcode_table_RS08_20 ≝
[
  quadrupleT ???? (anyOP RS08 LSR) MODE_INHA (Byte 〈x4,x4〉) 〈x0,x1〉
].

definition opcode_table_RS08_21 ≝
[
  quadrupleT ???? (anyOP RS08 MOV) MODE_IMM1_to_DIR1 (Byte 〈x3,xE〉) 〈x0,x4〉
; quadrupleT ???? (anyOP RS08 MOV) MODE_DIR1_to_DIR1 (Byte 〈x4,xE〉) 〈x0,x5〉
].

definition opcode_table_RS08_22 ≝
[ 
  quadrupleT ???? (anyOP RS08 ORA) MODE_IMM1 (Byte 〈xA,xA〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 ORA) MODE_DIR1 (Byte 〈xB,xA〉) 〈x0,x3〉
].

definition opcode_table_RS08_23 ≝
[
  quadrupleT ???? (anyOP RS08 ROL) MODE_INHA (Byte 〈x4,x9〉) 〈x0,x1〉
].

definition opcode_table_RS08_24 ≝
[
  quadrupleT ???? (anyOP RS08 ROR) MODE_INHA (Byte 〈x4,x6〉) 〈x0,x1〉
].

definition opcode_table_RS08_25 ≝
[
  quadrupleT ???? (anyOP RS08 SBC) MODE_IMM1 (Byte 〈xA,x2〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 SBC) MODE_DIR1 (Byte 〈xB,x2〉) 〈x0,x3〉
].

definition opcode_table_RS08_26 ≝
[
  quadrupleT ???? (anyOP RS08 STA) MODE_DIR1      (Byte 〈xB,x7〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t00) (Byte 〈xE,x0〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t01) (Byte 〈xE,x1〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t02) (Byte 〈xE,x2〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t03) (Byte 〈xE,x3〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t04) (Byte 〈xE,x4〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t05) (Byte 〈xE,x5〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t06) (Byte 〈xE,x6〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t07) (Byte 〈xE,x7〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t08) (Byte 〈xE,x8〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t09) (Byte 〈xE,x9〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t0A) (Byte 〈xE,xA〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t0B) (Byte 〈xE,xB〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t0C) (Byte 〈xE,xC〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t0D) (Byte 〈xE,xD〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t0E) (Byte 〈xE,xE〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t0F) (Byte 〈xE,xF〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t10) (Byte 〈xF,x0〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t11) (Byte 〈xF,x1〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t12) (Byte 〈xF,x2〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t13) (Byte 〈xF,x3〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t14) (Byte 〈xF,x4〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t15) (Byte 〈xF,x5〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t16) (Byte 〈xF,x6〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t17) (Byte 〈xF,x7〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t18) (Byte 〈xF,x8〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t19) (Byte 〈xF,x9〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t1A) (Byte 〈xF,xA〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t1B) (Byte 〈xF,xB〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t1C) (Byte 〈xF,xC〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t1D) (Byte 〈xF,xD〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t1E) (Byte 〈xF,xE〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 STA) (MODE_SRT t1F) (Byte 〈xF,xF〉) 〈x0,x2〉
].

definition opcode_table_RS08_27 ≝
[ 
  quadrupleT ???? (anyOP RS08 SUB) MODE_IMM1     (Byte 〈xA,x0〉) 〈x0,x2〉
; quadrupleT ???? (anyOP RS08 SUB) MODE_DIR1     (Byte 〈xB,x0〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 SUB) (MODE_TNY x0) (Byte 〈x7,x0〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 SUB) (MODE_TNY x1) (Byte 〈x7,x1〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 SUB) (MODE_TNY x2) (Byte 〈x7,x2〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 SUB) (MODE_TNY x3) (Byte 〈x7,x3〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 SUB) (MODE_TNY x4) (Byte 〈x7,x4〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 SUB) (MODE_TNY x5) (Byte 〈x7,x5〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 SUB) (MODE_TNY x6) (Byte 〈x7,x6〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 SUB) (MODE_TNY x7) (Byte 〈x7,x7〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 SUB) (MODE_TNY x8) (Byte 〈x7,x8〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 SUB) (MODE_TNY x9) (Byte 〈x7,x9〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 SUB) (MODE_TNY xA) (Byte 〈x7,xA〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 SUB) (MODE_TNY xB) (Byte 〈x7,xB〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 SUB) (MODE_TNY xC) (Byte 〈x7,xC〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 SUB) (MODE_TNY xD) (Byte 〈x7,xD〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 SUB) (MODE_TNY xE) (Byte 〈x7,xE〉) 〈x0,x3〉
; quadrupleT ???? (anyOP RS08 SUB) (MODE_TNY xF) (Byte 〈x7,xF〉) 〈x0,x3〉
].

definition opcode_table_RS08 ≝
opcode_table_RS08_1  @ opcode_table_RS08_2  @ opcode_table_RS08_3  @ opcode_table_RS08_4  @
opcode_table_RS08_5  @ opcode_table_RS08_6  @ opcode_table_RS08_7  @ opcode_table_RS08_8  @
opcode_table_RS08_9  @ opcode_table_RS08_10 @ opcode_table_RS08_11 @ opcode_table_RS08_12 @
opcode_table_RS08_13 @ opcode_table_RS08_14 @ opcode_table_RS08_15 @ opcode_table_RS08_16 @
opcode_table_RS08_17 @ opcode_table_RS08_18 @ opcode_table_RS08_19 @ opcode_table_RS08_20 @
opcode_table_RS08_21 @ opcode_table_RS08_22 @ opcode_table_RS08_23 @ opcode_table_RS08_24 @
opcode_table_RS08_25 @ opcode_table_RS08_26 @ opcode_table_RS08_27.
