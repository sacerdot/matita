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

include "num/bool.ma".

(* ********************************************** *)
(* MATTONI BASE PER DEFINIRE LE TABELLE DELLE MCU *)
(* ********************************************** *)

(* enumerazione delle istruzioni *)
ninductive IP2022_pseudo: Type ≝
  ADD     : IP2022_pseudo (* add *)
| ADDC    : IP2022_pseudo (* add with carry *)
| AND     : IP2022_pseudo (* and *)
| BREAK   : IP2022_pseudo (* enter break mode *)
| BREAKX  : IP2022_pseudo (* enter break mode, after skip *)
| CALL    : IP2022_pseudo (* subroutine call *)
| CLR     : IP2022_pseudo (* clear *)
| CLRB    : IP2022_pseudo (* clear bit *)
| CMP     : IP2022_pseudo (* set flags according to sub *)
| CSE     : IP2022_pseudo (* confront & skip if equal *)
| CSNE    : IP2022_pseudo (* confront & skip if not equal *)
| CWDT    : IP2022_pseudo (* clear watch dog -- not impl. ERR *)
| DEC     : IP2022_pseudo (* decrement *)
| DECSNZ  : IP2022_pseudo (* decrement & skip if not zero *)
| DECSZ   : IP2022_pseudo (* decrement & skip if zero *)
| FERASE  : IP2022_pseudo (* flash erase -- not impl. ERR *)
| FREAD   : IP2022_pseudo (* flash read -- not impl. ERR *)
| FWRITE  : IP2022_pseudo (* flash write -- not impl. ERR *)
| INC     : IP2022_pseudo (* increment *)
| INCSNZ  : IP2022_pseudo (* increment & skip if not zero *)
| INCSZ   : IP2022_pseudo (* increment & skip if zero *)
| INT     : IP2022_pseudo (* interrupt -- not impl. ERR *)
| IREAD   : IP2022_pseudo (* memory read *)
(* NB: ignorata la differenza IREAD/IREADI perche' non e' implementata EXT_MEM
       IREAD → ADDRX= 0x00 ram, 0x01 flash, 0x80 0x81 ext_mem
       IREADI → ADDRX= 0x00 ram, 0x01 flash *)
| IWRITE  : IP2022_pseudo (* memory write *)
(* NB: ignorata la differenza IWRITE/IWRITEI perche' non e' implementata EXT_MEM
       IREAD → ADDRX= 0x00 ram, 0x80 0x81 ext_mem
       IREADI → ADDRX= 0x00 ram *)
| JMP     : IP2022_pseudo (* jump *)
| LOADH   : IP2022_pseudo (* load Data Pointer High *)
| LOADL   : IP2022_pseudo (* load Data Pointer Low *)
| MOV     : IP2022_pseudo (* move *)
| MULS    : IP2022_pseudo (* signed mul *)
| MULU    : IP2022_pseudo (* unsigned mul *)
| NOP     : IP2022_pseudo (* nop *)
| NOT     : IP2022_pseudo (* not *)
| OR      : IP2022_pseudo (* or *)
| PAGE    : IP2022_pseudo (* set Page Register *)
| POP     : IP2022_pseudo (* pop *)
| PUSH    : IP2022_pseudo (* push *)
| RET     : IP2022_pseudo (* subroutine ret *)
| RETI    : IP2022_pseudo (* interrupt ret -- not impl. ERR *)
| RETNP   : IP2022_pseudo (* subroutine ret & don't restore Page Register *)
| RETW    : IP2022_pseudo (* subroutine ret & load W Register *)
| RL      : IP2022_pseudo (* rotate left *)
| RR      : IP2022_pseudo (* rotate right *)
| SB      : IP2022_pseudo (* skip if bit set *)
| SETB    : IP2022_pseudo (* set bit *)
| SNB     : IP2022_pseudo (* skip if bit not set *)
| SPEED   : IP2022_pseudo (* set Speed Register *)
| SUB     : IP2022_pseudo (* sub *)
| SUBC    : IP2022_pseudo (* sub with carry *)
| SWAP    : IP2022_pseudo (* swap xxxxyyyy → yyyyxxxx *)
| TEST    : IP2022_pseudo (* set flags according to zero test *)
| XOR     : IP2022_pseudo (* xor *)
.

ndefinition eq_IP2022_pseudo ≝
λps1,ps2:IP2022_pseudo.
 match ps1 with
  [ ADD ⇒ match ps2 with [ ADD ⇒ true | _ ⇒ false ]       | ADDC ⇒ match ps2 with [ ADDC ⇒ true | _ ⇒ false ]
  | AND ⇒ match ps2 with [ AND ⇒ true | _ ⇒ false ]       | BREAK ⇒ match ps2 with [ BREAK ⇒ true | _ ⇒ false ]
  | BREAKX ⇒ match ps2 with [ BREAKX ⇒ true | _ ⇒ false ] | CALL ⇒ match ps2 with [ CALL ⇒ true | _ ⇒ false ]
  | CLR ⇒ match ps2 with [ CLR ⇒ true | _ ⇒ false ]       | CLRB ⇒ match ps2 with [ CLRB ⇒ true | _ ⇒ false ]
  | CMP ⇒ match ps2 with [ CMP ⇒ true | _ ⇒ false ]       | CSE ⇒ match ps2 with [ CSE ⇒ true | _ ⇒ false ]
  | CSNE ⇒ match ps2 with [ CSNE ⇒ true | _ ⇒ false ]     | CWDT ⇒ match ps2 with [ CWDT ⇒ true | _ ⇒ false ]
  | DEC ⇒ match ps2 with [ DEC ⇒ true | _ ⇒ false ]       | DECSNZ ⇒ match ps2 with [ DECSNZ ⇒ true | _ ⇒ false ]
  | DECSZ ⇒ match ps2 with [ DECSZ ⇒ true | _ ⇒ false ]   | FERASE ⇒ match ps2 with [ FERASE ⇒ true | _ ⇒ false ]
  | FREAD ⇒ match ps2 with [ FREAD ⇒ true | _ ⇒ false ]   | FWRITE ⇒ match ps2 with [ FWRITE ⇒ true | _ ⇒ false ]
  | INC ⇒ match ps2 with [ INC ⇒ true | _ ⇒ false ]       | INCSNZ ⇒ match ps2 with [ INCSNZ ⇒ true | _ ⇒ false ]
  | INCSZ ⇒ match ps2 with [ INCSZ ⇒ true | _ ⇒ false ]   | INT ⇒ match ps2 with [ INT ⇒ true | _ ⇒ false ]
  | IREAD ⇒ match ps2 with [ IREAD ⇒ true | _ ⇒ false ]   | IWRITE ⇒ match ps2 with [ IWRITE ⇒ true | _ ⇒ false ]
  | JMP ⇒ match ps2 with [ JMP ⇒ true | _ ⇒ false ]       | LOADH ⇒ match ps2 with [ LOADH ⇒ true | _ ⇒ false ]
  | LOADL ⇒ match ps2 with [ LOADL ⇒ true | _ ⇒ false ]   | MOV ⇒ match ps2 with [ MOV ⇒ true | _ ⇒ false ]
  | MULS ⇒ match ps2 with [ MULS ⇒ true | _ ⇒ false ]     | MULU ⇒ match ps2 with [ MULU ⇒ true | _ ⇒ false ] 
  | NOP ⇒ match ps2 with [ NOP ⇒ true | _ ⇒ false ]       | NOT ⇒ match ps2 with [ NOT ⇒ true | _ ⇒ false ]
  | OR ⇒ match ps2 with [ OR ⇒ true | _ ⇒ false ]         | PAGE ⇒ match ps2 with [ PAGE ⇒ true | _ ⇒ false ]
  | POP ⇒ match ps2 with [ POP ⇒ true | _ ⇒ false ]       | PUSH ⇒ match ps2 with [ PUSH ⇒ true | _ ⇒ false ]
  | RET ⇒ match ps2 with [ RET ⇒ true | _ ⇒ false ]       | RETI ⇒ match ps2 with [ RETI ⇒ true | _ ⇒ false ]
  | RETNP ⇒ match ps2 with [ RETNP ⇒ true | _ ⇒ false ]   | RETW ⇒ match ps2 with [ RETW ⇒ true | _ ⇒ false ]
  | RL ⇒ match ps2 with [ RL ⇒ true | _ ⇒ false ]         | RR ⇒ match ps2 with [ RR ⇒ true | _ ⇒ false ] 
  | SB ⇒ match ps2 with [ SB ⇒ true | _ ⇒ false ]         | SETB ⇒ match ps2 with [ SETB ⇒ true | _ ⇒ false ]
  | SNB ⇒ match ps2 with [ SNB ⇒ true | _ ⇒ false ]       | SPEED ⇒ match ps2 with [ SPEED ⇒ true | _ ⇒ false ]
  | SUB ⇒ match ps2 with [ SUB ⇒ true | _ ⇒ false ]       | SUBC ⇒ match ps2 with [ SUBC ⇒ true | _ ⇒ false ]
  | SWAP ⇒ match ps2 with [ SWAP ⇒ true | _ ⇒ false ]     | TEST ⇒ match ps2 with [ TEST ⇒ true | _ ⇒ false ]
  | XOR ⇒ match ps2 with [ XOR ⇒ true | _ ⇒ false ]
  ].

ndefinition forall_IP2022_pseudo ≝ λP:IP2022_pseudo → bool.
 P ADD     ⊗ P ADDC    ⊗ P AND     ⊗ P BREAK   ⊗ P BREAKX  ⊗ P CALL    ⊗ P CLR    ⊗ P CLRB    ⊗
 P CMP     ⊗ P CSE     ⊗ P CSNE    ⊗ P CWDT    ⊗ P DEC     ⊗ P DECSNZ  ⊗ P DECSZ  ⊗ P FERASE  ⊗
 P FREAD   ⊗ P FWRITE  ⊗ P INC     ⊗ P INCSNZ  ⊗ P INCSZ   ⊗ P INT     ⊗ P IREAD  ⊗ P IWRITE  ⊗
 P JMP     ⊗ P LOADH   ⊗ P LOADL   ⊗ P MOV     ⊗ P MULS    ⊗ P MULU    ⊗ P NOP    ⊗ P NOT     ⊗
 P OR      ⊗ P PAGE    ⊗ P POP     ⊗ P PUSH    ⊗ P RET     ⊗ P RETI    ⊗ P RETNP  ⊗ P RETW    ⊗
 P RL      ⊗ P RR      ⊗ P SB      ⊗ P SETB    ⊗ P SNB     ⊗ P SPEED   ⊗ P SUB    ⊗ P SUBC    ⊗
 P SWAP    ⊗ P TEST    ⊗ P XOR.
