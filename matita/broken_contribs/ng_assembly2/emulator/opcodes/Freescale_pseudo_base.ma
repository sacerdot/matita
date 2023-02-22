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
ninductive Freescale_pseudo: Type ≝
  ADC    : Freescale_pseudo (* add with carry *)
| ADD    : Freescale_pseudo (* add *)
| AIS    : Freescale_pseudo (* add immediate to SP *)
| AIX    : Freescale_pseudo (* add immediate to X *)
| AND    : Freescale_pseudo (* and *)
| ASL    : Freescale_pseudo (* aritmetic shift left *)
| ASR    : Freescale_pseudo (* aritmetic shift right *)
| BCC    : Freescale_pseudo (* branch if C=0 *)
| BCLRn  : Freescale_pseudo (* clear bit n *)
| BCS    : Freescale_pseudo (* branch if C=1 *)
| BEQ    : Freescale_pseudo (* branch if Z=1 *)
| BGE    : Freescale_pseudo (* branch if N⊙V=0 (great or equal) *)
| BGND   : Freescale_pseudo (* !!background mode!! *)
| BGT    : Freescale_pseudo (* branch if Z|N⊙V=0 clear (great) *)
| BHCC   : Freescale_pseudo (* branch if H=0 *)
| BHCS   : Freescale_pseudo (* branch if H=1 *)
| BHI    : Freescale_pseudo (* branch if C|Z=0, (higher) *)
| BIH    : Freescale_pseudo (* branch if nIRQ=1 *)
| BIL    : Freescale_pseudo (* branch if nIRQ=0 *)
| BIT    : Freescale_pseudo (* flag = and (bit test) *)
| BLE    : Freescale_pseudo (* branch if Z|N⊙V=1 (less or equal) *)
| BLS    : Freescale_pseudo (* branch if C|Z=1 (lower or same) *)
| BLT    : Freescale_pseudo (* branch if N⊙1=1 (less) *)
| BMC    : Freescale_pseudo (* branch if I=0 (interrupt mask clear) *)
| BMI    : Freescale_pseudo (* branch if N=1 (minus) *)
| BMS    : Freescale_pseudo (* branch if I=1 (interrupt mask set) *)
| BNE    : Freescale_pseudo (* branch if Z=0 *)
| BPL    : Freescale_pseudo (* branch if N=0 (plus) *)
| BRA    : Freescale_pseudo (* branch always *)
| BRCLRn : Freescale_pseudo (* branch if bit n clear *)
| BRN    : Freescale_pseudo (* branch never (nop) *)
| BRSETn : Freescale_pseudo (* branch if bit n set *)
| BSETn  : Freescale_pseudo (* set bit n *)
| BSR    : Freescale_pseudo (* branch to subroutine *)
| CBEQA  : Freescale_pseudo (* compare (A) and BEQ *)
| CBEQX  : Freescale_pseudo (* compare (X) and BEQ *)
| CLC    : Freescale_pseudo (* C=0 *)
| CLI    : Freescale_pseudo (* I=0 *)
| CLR    : Freescale_pseudo (* operand=0 *)
| CMP    : Freescale_pseudo (* flag = sub (compare A) *)
| COM    : Freescale_pseudo (* not (1 complement) *)
| CPHX   : Freescale_pseudo (* flag = sub (compare H:X) *)
| CPX    : Freescale_pseudo (* flag = sub (compare X) *)
| DAA    : Freescale_pseudo (* decimal adjust A *)
| DBNZ   : Freescale_pseudo (* dec and BNE *)
| DEC    : Freescale_pseudo (* operand=operand-1 (decrement) *)
| DIV    : Freescale_pseudo (* div *)
| EOR    : Freescale_pseudo (* xor *)
| INC    : Freescale_pseudo (* operand=operand+1 (increment) *)
| JMP    : Freescale_pseudo (* jmp word [operand] *)
| JSR    : Freescale_pseudo (* jmp to subroutine *)
| LDA    : Freescale_pseudo (* load in A *)
| LDHX   : Freescale_pseudo (* load in H:X *)
| LDX    : Freescale_pseudo (* load in X *)
| LSR    : Freescale_pseudo (* logical shift right *)
| MOV    : Freescale_pseudo (* move *)
| MUL    : Freescale_pseudo (* mul *)
| NEG    : Freescale_pseudo (* neg (2 complement) *)
| NOP    : Freescale_pseudo (* nop *)
| NSA    : Freescale_pseudo (* nibble swap A (al:ah <- ah:al) *)
| ORA    : Freescale_pseudo (* or *)
| PSHA   : Freescale_pseudo (* push A *)
| PSHH   : Freescale_pseudo (* push H *)
| PSHX   : Freescale_pseudo (* push X *)
| PULA   : Freescale_pseudo (* pop A *)
| PULH   : Freescale_pseudo (* pop H *)
| PULX   : Freescale_pseudo (* pop X *)
| ROL    : Freescale_pseudo (* rotate left *)
| ROR    : Freescale_pseudo (* rotate right *)
| RSP    : Freescale_pseudo (* reset SP (0x00FF) *)
| RTI    : Freescale_pseudo (* return from interrupt *)
| RTS    : Freescale_pseudo (* return from subroutine *)
| SBC    : Freescale_pseudo (* sub with carry*)
| SEC    : Freescale_pseudo (* C=1 *)
| SEI    : Freescale_pseudo (* I=1 *)
| SHA    : Freescale_pseudo (* swap spc_high,A *)
| SLA    : Freescale_pseudo (* swap spc_low,A *)
| STA    : Freescale_pseudo (* store from A *)
| STHX   : Freescale_pseudo (* store from H:X *)
| STOP   : Freescale_pseudo (* !!stop mode!! *)
| STX    : Freescale_pseudo (* store from X *)
| SUB    : Freescale_pseudo (* sub *)
| SWI    : Freescale_pseudo (* software interrupt *)
| TAP    : Freescale_pseudo (* flag=A (transfer A to process status byte *)
| TAX    : Freescale_pseudo (* X=A (transfer A to X) *)
| TPA    : Freescale_pseudo (* A=flag (transfer process status byte to A) *)
| TST    : Freescale_pseudo (* flag = sub (test) *)
| TSX    : Freescale_pseudo (* X:H=SP (transfer SP to H:X) *)
| TXA    : Freescale_pseudo (* A=X (transfer X to A) *)
| TXS    : Freescale_pseudo (* SP=X:H (transfer H:X to SP) *)
| WAIT   : Freescale_pseudo (* !!wait mode!! *)
.

ndefinition eq_Freescale_pseudo ≝
λps1,ps2:Freescale_pseudo.
 match ps1 with
  [ ADC ⇒ match ps2 with [ ADC ⇒ true | _ ⇒ false ] | ADD ⇒ match ps2 with [ ADD ⇒ true | _ ⇒ false ]
  | AIS ⇒ match ps2 with [ AIS ⇒ true | _ ⇒ false ] | AIX ⇒ match ps2 with [ AIX ⇒ true | _ ⇒ false ]
  | AND ⇒ match ps2 with [ AND ⇒ true | _ ⇒ false ] | ASL ⇒ match ps2 with [ ASL ⇒ true | _ ⇒ false ]
  | ASR ⇒ match ps2 with [ ASR ⇒ true | _ ⇒ false ] | BCC ⇒ match ps2 with [ BCC ⇒ true | _ ⇒ false ]
  | BCLRn ⇒ match ps2 with [ BCLRn ⇒ true | _ ⇒ false ] | BCS ⇒ match ps2 with [ BCS ⇒ true | _ ⇒ false ]
  | BEQ ⇒ match ps2 with [ BEQ ⇒ true | _ ⇒ false ] | BGE ⇒ match ps2 with [ BGE ⇒ true | _ ⇒ false ]
  | BGND ⇒ match ps2 with [ BGND ⇒ true | _ ⇒ false ] | BGT ⇒ match ps2 with [ BGT ⇒ true | _ ⇒ false ]
  | BHCC ⇒ match ps2 with [ BHCC ⇒ true | _ ⇒ false ] | BHCS ⇒ match ps2 with [ BHCS ⇒ true | _ ⇒ false ]
  | BHI ⇒ match ps2 with [ BHI ⇒ true | _ ⇒ false ] | BIH ⇒ match ps2 with [ BIH ⇒ true | _ ⇒ false ]
  | BIL ⇒ match ps2 with [ BIL ⇒ true | _ ⇒ false ] | BIT ⇒ match ps2 with [ BIT ⇒ true | _ ⇒ false ]
  | BLE ⇒ match ps2 with [ BLE ⇒ true | _ ⇒ false ] | BLS ⇒ match ps2 with [ BLS ⇒ true | _ ⇒ false ]
  | BLT ⇒ match ps2 with [ BLT ⇒ true | _ ⇒ false ] | BMC ⇒ match ps2 with [ BMC ⇒ true | _ ⇒ false ]
  | BMI ⇒ match ps2 with [ BMI ⇒ true | _ ⇒ false ] | BMS ⇒ match ps2 with [ BMS ⇒ true | _ ⇒ false ]
  | BNE ⇒ match ps2 with [ BNE ⇒ true | _ ⇒ false ] | BPL ⇒ match ps2 with [ BPL ⇒ true | _ ⇒ false ]
  | BRA ⇒ match ps2 with [ BRA ⇒ true | _ ⇒ false ] | BRCLRn ⇒ match ps2 with [ BRCLRn ⇒ true | _ ⇒ false ]
  | BRN ⇒ match ps2 with [ BRN ⇒ true | _ ⇒ false ] | BRSETn ⇒ match ps2 with [ BRSETn ⇒ true | _ ⇒ false ]
  | BSETn ⇒ match ps2 with [ BSETn ⇒ true | _ ⇒ false ] | BSR ⇒ match ps2 with [ BSR ⇒ true | _ ⇒ false ]
  | CBEQA ⇒ match ps2 with [ CBEQA ⇒ true | _ ⇒ false ] | CBEQX ⇒ match ps2 with [ CBEQX ⇒ true | _ ⇒ false ]
  | CLC ⇒ match ps2 with [ CLC ⇒ true | _ ⇒ false ] | CLI ⇒ match ps2 with [ CLI ⇒ true | _ ⇒ false ]
  | CLR ⇒ match ps2 with [ CLR ⇒ true | _ ⇒ false ] | CMP ⇒ match ps2 with [ CMP ⇒ true | _ ⇒ false ]
  | COM ⇒ match ps2 with [ COM ⇒ true | _ ⇒ false ] | CPHX ⇒ match ps2 with [ CPHX ⇒ true | _ ⇒ false ]
  | CPX ⇒ match ps2 with [ CPX ⇒ true | _ ⇒ false ] | DAA ⇒ match ps2 with [ DAA ⇒ true | _ ⇒ false ]
  | DBNZ ⇒ match ps2 with [ DBNZ ⇒ true | _ ⇒ false ] | DEC ⇒ match ps2 with [ DEC ⇒ true | _ ⇒ false ]
  | DIV ⇒ match ps2 with [ DIV ⇒ true | _ ⇒ false ] | EOR ⇒ match ps2 with [ EOR ⇒ true | _ ⇒ false ]
  | INC ⇒ match ps2 with [ INC ⇒ true | _ ⇒ false ] | JMP ⇒ match ps2 with [ JMP ⇒ true | _ ⇒ false ]
  | JSR ⇒ match ps2 with [ JSR ⇒ true | _ ⇒ false ] | LDA ⇒ match ps2 with [ LDA ⇒ true | _ ⇒ false ]
  | LDHX ⇒ match ps2 with [ LDHX ⇒ true | _ ⇒ false ] | LDX ⇒ match ps2 with [ LDX ⇒ true | _ ⇒ false ]
  | LSR ⇒ match ps2 with [ LSR ⇒ true | _ ⇒ false ] | MOV ⇒ match ps2 with [ MOV ⇒ true | _ ⇒ false ]
  | MUL ⇒ match ps2 with [ MUL ⇒ true | _ ⇒ false ] | NEG ⇒ match ps2 with [ NEG ⇒ true | _ ⇒ false ]
  | NOP ⇒ match ps2 with [ NOP ⇒ true | _ ⇒ false ] | NSA ⇒ match ps2 with [ NSA ⇒ true | _ ⇒ false ]
  | ORA ⇒ match ps2 with [ ORA ⇒ true | _ ⇒ false ] | PSHA ⇒ match ps2 with [ PSHA ⇒ true | _ ⇒ false ]
  | PSHH ⇒ match ps2 with [ PSHH ⇒ true | _ ⇒ false ] | PSHX ⇒ match ps2 with [ PSHX ⇒ true | _ ⇒ false ]
  | PULA ⇒ match ps2 with [ PULA ⇒ true | _ ⇒ false ] | PULH ⇒ match ps2 with [ PULH ⇒ true | _ ⇒ false ]
  | PULX ⇒ match ps2 with [ PULX ⇒ true | _ ⇒ false ] | ROL ⇒ match ps2 with [ ROL ⇒ true | _ ⇒ false ]
  | ROR ⇒ match ps2 with [ ROR ⇒ true | _ ⇒ false ] | RSP ⇒ match ps2 with [ RSP ⇒ true | _ ⇒ false ]
  | RTI ⇒ match ps2 with [ RTI ⇒ true | _ ⇒ false ] | RTS ⇒ match ps2 with [ RTS ⇒ true | _ ⇒ false ]
  | SBC ⇒ match ps2 with [ SBC ⇒ true | _ ⇒ false ] | SEC ⇒ match ps2 with [ SEC ⇒ true | _ ⇒ false ]
  | SEI ⇒ match ps2 with [ SEI ⇒ true | _ ⇒ false ] | SHA ⇒ match ps2 with [ SHA ⇒ true | _ ⇒ false ]
  | SLA ⇒ match ps2 with [ SLA ⇒ true | _ ⇒ false ] | STA ⇒ match ps2 with [ STA ⇒ true | _ ⇒ false ]
  | STHX ⇒ match ps2 with [ STHX ⇒ true | _ ⇒ false ] | STOP ⇒ match ps2 with [ STOP ⇒ true | _ ⇒ false ]
  | STX ⇒ match ps2 with [ STX ⇒ true | _ ⇒ false ] | SUB ⇒ match ps2 with [ SUB ⇒ true | _ ⇒ false ]
  | SWI ⇒ match ps2 with [ SWI ⇒ true | _ ⇒ false ] | TAP ⇒ match ps2 with [ TAP ⇒ true | _ ⇒ false ]
  | TAX ⇒ match ps2 with [ TAX ⇒ true | _ ⇒ false ] | TPA ⇒ match ps2 with [ TPA ⇒ true | _ ⇒ false ]
  | TST ⇒ match ps2 with [ TST ⇒ true | _ ⇒ false ] | TSX ⇒ match ps2 with [ TSX ⇒ true | _ ⇒ false ]
  | TXA ⇒ match ps2 with [ TXA ⇒ true | _ ⇒ false ] | TXS ⇒ match ps2 with [ TXS ⇒ true | _ ⇒ false ]
  | WAIT ⇒ match ps2 with [ WAIT ⇒ true | _ ⇒ false ]
  ].

ndefinition forall_Freescale_pseudo ≝ λP:Freescale_pseudo → bool.
 P ADC    ⊗ P ADD    ⊗ P AIS    ⊗ P AIX    ⊗ P AND    ⊗ P ASL    ⊗ P ASR    ⊗ P BCC    ⊗
 P BCLRn  ⊗ P BCS    ⊗ P BEQ    ⊗ P BGE    ⊗ P BGND   ⊗ P BGT    ⊗ P BHCC   ⊗ P BHCS   ⊗
 P BHI    ⊗ P BIH    ⊗ P BIL    ⊗ P BIT    ⊗ P BLE    ⊗ P BLS    ⊗ P BLT    ⊗ P BMC    ⊗
 P BMI    ⊗ P BMS    ⊗ P BNE    ⊗ P BPL    ⊗ P BRA    ⊗ P BRCLRn ⊗ P BRN    ⊗ P BRSETn ⊗
 P BSETn  ⊗ P BSR    ⊗ P CBEQA  ⊗ P CBEQX  ⊗ P CLC    ⊗ P CLI    ⊗ P CLR    ⊗ P CMP    ⊗
 P COM    ⊗ P CPHX   ⊗ P CPX    ⊗ P DAA    ⊗ P DBNZ   ⊗ P DEC    ⊗ P DIV    ⊗ P EOR    ⊗
 P INC    ⊗ P JMP    ⊗ P JSR    ⊗ P LDA    ⊗ P LDHX   ⊗ P LDX    ⊗ P LSR    ⊗ P MOV    ⊗
 P MUL    ⊗ P NEG    ⊗ P NOP    ⊗ P NSA    ⊗ P ORA    ⊗ P PSHA   ⊗ P PSHH   ⊗ P PSHX   ⊗
 P PULA   ⊗ P PULH   ⊗ P PULX   ⊗ P ROL    ⊗ P ROR    ⊗ P RSP    ⊗ P RTI    ⊗ P RTS    ⊗
 P SBC    ⊗ P SEC    ⊗ P SEI    ⊗ P SHA    ⊗ P SLA    ⊗ P STA    ⊗ P STHX   ⊗ P STOP   ⊗
 P STX    ⊗ P SUB    ⊗ P SWI    ⊗ P TAP    ⊗ P TAX    ⊗ P TPA    ⊗ P TST    ⊗ P TSX    ⊗
 P TXA    ⊗ P TXS    ⊗ P WAIT.
