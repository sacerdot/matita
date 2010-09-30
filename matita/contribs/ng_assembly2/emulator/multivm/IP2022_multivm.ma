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

include "emulator/multivm/multivm_base.ma".
include "emulator/read_write/load_write.ma".

(* ************************************************ *)
(* LOGICHE AUSILIARE CHE ACCOMUNANO PIU' OPERAZIONI *)
(* ************************************************ *)

(* **************** *)
(* LOGICA DELLA ALU *)
(* **************** *)

ndefinition execute_NO ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λi:aux_im_type m.
 None (ProdT (any_status m t) word16).

(* raccordo *)
ndefinition IP2022_execute_any ≝
λps:IP2022_pseudo.match ps with
  [ ADD    ⇒ execute_NO (* add *)
  | ADDC   ⇒ execute_NO (* add with carry *)
  | AND    ⇒ execute_NO (* and *)
  | BREAK  ⇒ execute_NO (* enter break mode *)
  | BREAKX ⇒ execute_NO (* enter break mode, after skip *)
  | CALL   ⇒ execute_NO (* subroutine call *)
  | CLR    ⇒ execute_NO (* clear *)
  | CLRB   ⇒ execute_NO (* clear bit *)
  | CMP    ⇒ execute_NO (* set flags according to sub *)
  | CSE    ⇒ execute_NO (* confront & skip if equal *)
  | CSNE   ⇒ execute_NO (* confront & skip if not equal *)
  | CWDT   ⇒ execute_NO (* clear watch dog -- not impl. ERR *)
  | DEC    ⇒ execute_NO (* decrement *)
  | DECSNZ ⇒ execute_NO (* decrement & skip if not zero *)
  | DECSZ  ⇒ execute_NO (* decrement & skip if zero *)
  | FERASE ⇒ execute_NO (* flash erase -- not impl. ERR *)
  | FREAD  ⇒ execute_NO (* flash read -- not impl. ERR *)
  | FWRITE ⇒ execute_NO (* flash write -- not impl. ERR *)
  | INC    ⇒ execute_NO (* increment *)
  | INCSNZ ⇒ execute_NO (* increment & skip if not zero *)
  | INCSZ  ⇒ execute_NO (* increment & skip if zero *)
  | INT    ⇒ execute_NO (* interrupt -- not impl. ERR *)
  | IREAD  ⇒ execute_NO (* memory read *)
  | IWRITE ⇒ execute_NO (* memory write *)
  | JMP    ⇒ execute_NO (* jump *)
  | LOADH  ⇒ execute_NO (* load Data Pointer High *)
  | LOADL  ⇒ execute_NO (* load Data Pointer Low *)
  | MOV    ⇒ execute_NO (* move *)
  | MULS   ⇒ execute_NO (* signed mul *)
  | MULU   ⇒ execute_NO (* unsigned mul *)
  | NOP    ⇒ execute_NO (* nop *)
  | NOT    ⇒ execute_NO (* not *)
  | OR     ⇒ execute_NO (* or *)
  | PAGE   ⇒ execute_NO (* set Page Register *)
  | POP    ⇒ execute_NO (* pop *)
  | PUSH   ⇒ execute_NO (* push *)
  | RET    ⇒ execute_NO (* subroutine ret *)
  | RETI   ⇒ execute_NO (* interrupt ret -- not impl. ERR *)
  | RETNP  ⇒ execute_NO (* subroutine ret & don't restore Page Register *)
  | RETW   ⇒ execute_NO (* subroutine ret & load W Register *)
  | RL     ⇒ execute_NO (* rotate left *)
  | RR     ⇒ execute_NO (* rotate right *)
  | SB     ⇒ execute_NO (* skip if bit set *)
  | SETB   ⇒ execute_NO (* set bit *)
  | SNB    ⇒ execute_NO (* skip if bit not set *)
  | SPEED  ⇒ execute_NO (* set Speed Register *)
  | SUB    ⇒ execute_NO (* sub *)
  | SUBC   ⇒ execute_NO (* sub with carry *)
  | SWAP   ⇒ execute_NO (* swap xxxxyyyy → yyyyxxxx *)
  | TEST   ⇒ execute_NO (* set flags according to zero test *)
  | XOR    ⇒ execute_NO (* xor *)
  ].

(* stati speciali di esecuzione *)
ndefinition IP2022_check_susp ≝
λps:IP2022_pseudo.match ps with
 [ BREAK ⇒ Some ? BGND_MODE
 | BREAKX ⇒ Some ? BGND_MODE
 | _ ⇒ None ?
 ].

(* istruzioni speciali per skip *)
ndefinition IP2022_check_skip ≝
λps:IP2022_pseudo.match ps with
 [ LOADH ⇒ true
 | LOADL ⇒ true
 | PAGE ⇒ true
 | _ ⇒ false
 ].

(* motiplicatore del ciclo di durata *)
ndefinition IP2022_clk_mult ≝
λt.λs:any_status IP2022 t.
 (* divisore del clock, 0 = stop *)
 match speed_reg_IP2022 … (alu … s) with
  [ x0 ⇒ nat1  | x1 ⇒ nat2  | x2 ⇒ nat3   | x3 ⇒ nat4
  | x4 ⇒ nat5  | x5 ⇒ nat6  | x6 ⇒ nat8   | x7 ⇒ nat10
  | x8 ⇒ nat12 | x9 ⇒ nat16 | xA ⇒ nat24  | xB ⇒ nat32
  | xC ⇒ nat48 | xD ⇒ nat64 | xE ⇒ nat128 | xF ⇒ O ] *
 (* FLASH clock 120MHz, RAM clock 40MHz *)
 match IP2022_pc_flashtest (get_pc_reg … s) with
  [ true ⇒ nat3 | false ⇒ nat1 ].
