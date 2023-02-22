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

include "freescale/aux_bases.ma".

(* ********************************************** *)
(* MATTONI BASE PER DEFINIRE LE TABELLE DELLE MCU *)
(* ********************************************** *)

(* enumerazione delle ALU *)
inductive mcu_type: Type ≝
  HC05  : mcu_type
| HC08  : mcu_type
| HCS08 : mcu_type
| RS08  : mcu_type.

(* enumerazione delle modalita' di indirizzamento = caricamento degli operandi *)
inductive instr_mode: Type ≝
  (* INHERENT = nessun operando *)
  MODE_INH  : instr_mode
  (* INHERENT = nessun operando (A implicito) *)
| MODE_INHA : instr_mode
  (* INHERENT = nessun operando (X implicito) *)
| MODE_INHX : instr_mode
  (* INHERENT = nessun operando (H implicito) *)
| MODE_INHH : instr_mode

  (* INHERENT_ADDRESS = nessun operando (HX implicito) *)
| MODE_INHX0ADD : instr_mode
  (* INHERENT_ADDRESS = nessun operando (HX implicito+0x00bb) *)
| MODE_INHX1ADD : instr_mode
  (* INHERENT_ADDRESS = nessun operando (HX implicito+0xwwww) *)
| MODE_INHX2ADD : instr_mode

  (* IMMEDIATE = operando valore immediato byte = 0xbb *)
| MODE_IMM1 : instr_mode
  (* IMMEDIATE_EXT = operando valore immediato byte = 0xbb -> esteso a word *)
| MODE_IMM1EXT : instr_mode
  (* IMMEDIATE = operando valore immediato word = 0xwwww *)
| MODE_IMM2 : instr_mode
  (* DIRECT = operando offset byte = [0x00bb] *)
| MODE_DIR1 : instr_mode
  (* DIRECT = operando offset word = [0xwwww] *)
| MODE_DIR2 : instr_mode
  (* INDEXED = nessun operando (implicito [X] *)
| MODE_IX0  : instr_mode
  (* INDEXED = operando offset relativo byte = [X+0x00bb] *)
| MODE_IX1  : instr_mode
  (* INDEXED = operando offset relativo word = [X+0xwwww] *)
| MODE_IX2  : instr_mode
  (* INDEXED = operando offset relativo byte = [SP+0x00bb] *)
| MODE_SP1  : instr_mode
  (* INDEXED = operando offset relativo word = [SP+0xwwww] *)
| MODE_SP2  : instr_mode

  (* DIRECT → DIRECT = carica da diretto/scrive su diretto *)
| MODE_DIR1_to_DIR1 : instr_mode
  (* IMMEDIATE → DIRECT = carica da immediato/scrive su diretto *)
| MODE_IMM1_to_DIR1 : instr_mode
  (* INDEXED++ → DIRECT = carica da [X]/scrive su diretto/H:X++ *)
| MODE_IX0p_to_DIR1 : instr_mode
  (* DIRECT → INDEXED++ = carica da diretto/scrive su [X]/H:X++ *)
| MODE_DIR1_to_IX0p : instr_mode

  (* INHERENT(A) + IMMEDIATE *)
| MODE_INHA_and_IMM1 : instr_mode
  (* INHERENT(X) + IMMEDIATE *)
| MODE_INHX_and_IMM1 : instr_mode
  (* IMMEDIATE + IMMEDIATE *)
| MODE_IMM1_and_IMM1 : instr_mode
  (* DIRECT + IMMEDIATE *)
| MODE_DIR1_and_IMM1 : instr_mode
  (* INDEXED + IMMEDIATE *)
| MODE_IX0_and_IMM1  : instr_mode
  (* INDEXED++ + IMMEDIATE *)
| MODE_IX0p_and_IMM1 : instr_mode
  (* INDEXED + IMMEDIATE *)
| MODE_IX1_and_IMM1  : instr_mode
  (* INDEXED++ + IMMEDIATE *)
| MODE_IX1p_and_IMM1 : instr_mode
  (* INDEXED + IMMEDIATE *)
| MODE_SP1_and_IMM1  : instr_mode

  (* DIRECT(mTNY) = operando offset byte(maschera scrittura implicita 3 bit) *)
  (* ex: DIR3 e' carica b, scrivi b con n-simo bit modificato *)
| MODE_DIRn          : oct → instr_mode
  (* DIRECT(mTNY) + IMMEDIATE = operando offset byte(maschera lettura implicita 3 bit) *)
  (*                            + operando valore immediato byte  *)
  (* ex: DIR2_and_IMM1 e' carica b, carica imm, restituisci n-simo bit di b + imm *)
| MODE_DIRn_and_IMM1 : oct → instr_mode
  (* TINY = nessun operando (diretto implicito 4bit = [0x00000000:0000iiii]) *)
| MODE_TNY           : exadecim → instr_mode
  (* SHORT = nessun operando (diretto implicito 5bit = [0x00000000:000iiiii]) *)
| MODE_SRT           : bitrigesim → instr_mode
.

(* enumerazione delle istruzioni di tutte le ALU *)
inductive opcode: Type ≝
  ADC    : opcode (* add with carry *)
| ADD    : opcode (* add *)
| AIS    : opcode (* add immediate to SP *)
| AIX    : opcode (* add immediate to X *)
| AND    : opcode (* and *)
| ASL    : opcode (* aritmetic shift left *)
| ASR    : opcode (* aritmetic shift right *)
| BCC    : opcode (* branch if C=0 *)
| BCLRn  : opcode (* clear bit n *)
| BCS    : opcode (* branch if C=1 *)
| BEQ    : opcode (* branch if Z=1 *)
| BGE    : opcode (* branch if N⊙V=0 (great or equal) *)
| BGND   : opcode (* !!background mode!! *)
| BGT    : opcode (* branch if Z|N⊙V=0 clear (great) *)
| BHCC   : opcode (* branch if H=0 *)
| BHCS   : opcode (* branch if H=1 *)
| BHI    : opcode (* branch if C|Z=0, (higher) *)
| BIH    : opcode (* branch if nIRQ=1 *)
| BIL    : opcode (* branch if nIRQ=0 *)
| BIT    : opcode (* flag = and (bit test) *)
| BLE    : opcode (* branch if Z|N⊙V=1 (less or equal) *)
| BLS    : opcode (* branch if C|Z=1 (lower or same) *)
| BLT    : opcode (* branch if N⊙1=1 (less) *)
| BMC    : opcode (* branch if I=0 (interrupt mask clear) *)
| BMI    : opcode (* branch if N=1 (minus) *)
| BMS    : opcode (* branch if I=1 (interrupt mask set) *)
| BNE    : opcode (* branch if Z=0 *)
| BPL    : opcode (* branch if N=0 (plus) *)
| BRA    : opcode (* branch always *)
| BRCLRn : opcode (* branch if bit n clear *)
| BRN    : opcode (* branch never (nop) *)
| BRSETn : opcode (* branch if bit n set *)
| BSETn  : opcode (* set bit n *)
| BSR    : opcode (* branch to subroutine *)
| CBEQA  : opcode (* compare (A) and BEQ *)
| CBEQX  : opcode (* compare (X) and BEQ *)
| CLC    : opcode (* C=0 *)
| CLI    : opcode (* I=0 *)
| CLR    : opcode (* operand=0 *)
| CMP    : opcode (* flag = sub (compare A) *)
| COM    : opcode (* not (1 complement) *)
| CPHX   : opcode (* flag = sub (compare H:X) *)
| CPX    : opcode (* flag = sub (compare X) *)
| DAA    : opcode (* decimal adjust A *)
| DBNZ   : opcode (* dec and BNE *)
| DEC    : opcode (* operand=operand-1 (decrement) *)
| DIV    : opcode (* div *)
| EOR    : opcode (* xor *)
| INC    : opcode (* operand=operand+1 (increment) *)
| JMP    : opcode (* jmp word [operand] *)
| JSR    : opcode (* jmp to subroutine *)
| LDA    : opcode (* load in A *)
| LDHX   : opcode (* load in H:X *)
| LDX    : opcode (* load in X *)
| LSR    : opcode (* logical shift right *)
| MOV    : opcode (* move *)
| MUL    : opcode (* mul *)
| NEG    : opcode (* neg (2 complement) *)
| NOP    : opcode (* nop *)
| NSA    : opcode (* nibble swap A (al:ah <- ah:al) *)
| ORA    : opcode (* or *)
| PSHA   : opcode (* push A *)
| PSHH   : opcode (* push H *)
| PSHX   : opcode (* push X *)
| PULA   : opcode (* pop A *)
| PULH   : opcode (* pop H *)
| PULX   : opcode (* pop X *)
| ROL    : opcode (* rotate left *)
| ROR    : opcode (* rotate right *)
| RSP    : opcode (* reset SP (0x00FF) *)
| RTI    : opcode (* return from interrupt *)
| RTS    : opcode (* return from subroutine *)
| SBC    : opcode (* sub with carry*)
| SEC    : opcode (* C=1 *)
| SEI    : opcode (* I=1 *)
| SHA    : opcode (* swap spc_high,A *)
| SLA    : opcode (* swap spc_low,A *)
| STA    : opcode (* store from A *)
| STHX   : opcode (* store from H:X *)
| STOP   : opcode (* !!stop mode!! *)
| STX    : opcode (* store from X *)
| SUB    : opcode (* sub *)
| SWI    : opcode (* software interrupt *)
| TAP    : opcode (* flag=A (transfer A to process status byte *)
| TAX    : opcode (* X=A (transfer A to X) *)
| TPA    : opcode (* A=flag (transfer process status byte to A) *)
| TST    : opcode (* flag = sub (test) *)
| TSX    : opcode (* X:H=SP (transfer SP to H:X) *)
| TXA    : opcode (* A=X (transfer X to A) *)
| TXS    : opcode (* SP=X:H (transfer H:X to SP) *)
| WAIT   : opcode (* !!wait mode!! *)
.

(* introduzione di un tipo opcode dipendente dall'mcu_type (phantom type) *)
inductive any_opcode (m:mcu_type) : Type ≝
 anyOP : opcode → any_opcode m.

definition c_anyOP ≝ anyOP.

coercion c_anyOP.

(* raggruppamento di byte e word in un tipo unico *)
inductive byte8_or_word16 : Type ≝
  Byte: byte8  → byte8_or_word16
| Word: word16 → byte8_or_word16.

definition c_Byte ≝ Byte.
definition c_Word ≝ Word.

coercion c_Byte.
coercion c_Word.

(* opcode → naturali, per usare eqb *)
definition magic_of_opcode ≝
λo:opcode.match o with
[ ADC    ⇒ 〈x0,x0〉
| ADD    ⇒ 〈x0,x1〉
| AIS    ⇒ 〈x0,x2〉
| AIX    ⇒ 〈x0,x3〉
| AND    ⇒ 〈x0,x4〉
| ASL    ⇒ 〈x0,x5〉
| ASR    ⇒ 〈x0,x6〉
| BCC    ⇒ 〈x0,x7〉
| BCLRn  ⇒ 〈x0,x8〉
| BCS    ⇒ 〈x0,x9〉
| BEQ    ⇒ 〈x0,xA〉
| BGE    ⇒ 〈x0,xB〉
| BGND   ⇒ 〈x0,xC〉
| BGT    ⇒ 〈x0,xD〉
| BHCC   ⇒ 〈x0,xE〉
| BHCS   ⇒ 〈x0,xF〉
| BHI    ⇒ 〈x1,x0〉
| BIH    ⇒ 〈x1,x1〉
| BIL    ⇒ 〈x1,x2〉
| BIT    ⇒ 〈x1,x3〉
| BLE    ⇒ 〈x1,x4〉
| BLS    ⇒ 〈x1,x5〉
| BLT    ⇒ 〈x1,x6〉
| BMC    ⇒ 〈x1,x7〉
| BMI    ⇒ 〈x1,x8〉
| BMS    ⇒ 〈x1,x9〉
| BNE    ⇒ 〈x1,xA〉
| BPL    ⇒ 〈x1,xB〉
| BRA    ⇒ 〈x1,xC〉
| BRCLRn ⇒ 〈x1,xD〉
| BRN    ⇒ 〈x1,xE〉
| BRSETn ⇒ 〈x1,xF〉
| BSETn  ⇒ 〈x2,x0〉
| BSR    ⇒ 〈x2,x1〉
| CBEQA  ⇒ 〈x2,x2〉
| CBEQX  ⇒ 〈x2,x3〉
| CLC    ⇒ 〈x2,x4〉
| CLI    ⇒ 〈x2,x5〉
| CLR    ⇒ 〈x2,x6〉
| CMP    ⇒ 〈x2,x7〉
| COM    ⇒ 〈x2,x8〉
| CPHX   ⇒ 〈x2,x9〉
| CPX    ⇒ 〈x2,xA〉
| DAA    ⇒ 〈x2,xB〉
| DBNZ   ⇒ 〈x2,xC〉
| DEC    ⇒ 〈x2,xD〉
| DIV    ⇒ 〈x2,xE〉
| EOR    ⇒ 〈x2,xF〉
| INC    ⇒ 〈x3,x0〉
| JMP    ⇒ 〈x3,x1〉
| JSR    ⇒ 〈x3,x2〉
| LDA    ⇒ 〈x3,x3〉
| LDHX   ⇒ 〈x3,x4〉
| LDX    ⇒ 〈x3,x5〉
| LSR    ⇒ 〈x3,x6〉
| MOV    ⇒ 〈x3,x7〉
| MUL    ⇒ 〈x3,x8〉
| NEG    ⇒ 〈x3,x9〉
| NOP    ⇒ 〈x3,xA〉
| NSA    ⇒ 〈x3,xB〉
| ORA    ⇒ 〈x3,xC〉
| PSHA   ⇒ 〈x3,xD〉
| PSHH   ⇒ 〈x3,xE〉
| PSHX   ⇒ 〈x3,xF〉
| PULA   ⇒ 〈x4,x0〉
| PULH   ⇒ 〈x4,x1〉
| PULX   ⇒ 〈x4,x2〉
| ROL    ⇒ 〈x4,x3〉
| ROR    ⇒ 〈x4,x4〉
| RSP    ⇒ 〈x4,x5〉
| RTI    ⇒ 〈x4,x6〉
| RTS    ⇒ 〈x4,x7〉
| SBC    ⇒ 〈x4,x8〉
| SEC    ⇒ 〈x4,x9〉
| SEI    ⇒ 〈x4,xA〉
| SHA    ⇒ 〈x4,xB〉
| SLA    ⇒ 〈x4,xC〉
| STA    ⇒ 〈x4,xD〉
| STHX   ⇒ 〈x4,xE〉
| STOP   ⇒ 〈x4,xF〉
| STX    ⇒ 〈x5,x0〉
| SUB    ⇒ 〈x5,x1〉
| SWI    ⇒ 〈x5,x2〉
| TAP    ⇒ 〈x5,x3〉
| TAX    ⇒ 〈x5,x4〉
| TPA    ⇒ 〈x5,x5〉
| TST    ⇒ 〈x5,x6〉
| TSX    ⇒ 〈x5,x7〉
| TXA    ⇒ 〈x5,x8〉
| TXS    ⇒ 〈x5,x9〉
| WAIT   ⇒ 〈x5,xA〉
].

(* confronto fra opcode, legale solo se tipati sulla stessa mcu *)
definition eqop ≝
λm:mcu_type.λo:any_opcode m.λo':any_opcode m.match o with
 [ anyOP p ⇒ match o' with
  [ anyOP p' ⇒ (eq_b8 (magic_of_opcode p) (magic_of_opcode p')) ] ].

(* instr_mode → naturali, per usare eqb *)
definition magic_of_instr_mode ≝
λi:instr_mode.match i with
[ MODE_INH  ⇒ 〈x0,x0〉
| MODE_INHA ⇒ 〈x0,x1〉
| MODE_INHX ⇒ 〈x0,x2〉
| MODE_INHH ⇒ 〈x0,x3〉

| MODE_INHX0ADD ⇒ 〈x0,x4〉
| MODE_INHX1ADD ⇒ 〈x0,x5〉
| MODE_INHX2ADD ⇒ 〈x0,x6〉

| MODE_IMM1 ⇒ 〈x0,x7〉
| MODE_IMM1EXT ⇒ 〈x0,x8〉
| MODE_IMM2 ⇒ 〈x0,x9〉
| MODE_DIR1 ⇒ 〈x0,xA〉
| MODE_DIR2 ⇒ 〈x0,xB〉
| MODE_IX0  ⇒ 〈x0,xC〉
| MODE_IX1  ⇒ 〈x0,xD〉
| MODE_IX2  ⇒ 〈x0,xE〉
| MODE_SP1  ⇒ 〈x0,xF〉
| MODE_SP2  ⇒ 〈x1,x0〉

| MODE_DIR1_to_DIR1 ⇒ 〈x1,x1〉
| MODE_IMM1_to_DIR1 ⇒ 〈x1,x2〉
| MODE_IX0p_to_DIR1 ⇒ 〈x1,x3〉
| MODE_DIR1_to_IX0p ⇒ 〈x1,x4〉

| MODE_INHA_and_IMM1 ⇒ 〈x1,x5〉
| MODE_INHX_and_IMM1 ⇒ 〈x1,x6〉
| MODE_IMM1_and_IMM1 ⇒ 〈x1,x7〉
| MODE_DIR1_and_IMM1 ⇒ 〈x1,x8〉
| MODE_IX0_and_IMM1  ⇒ 〈x1,x9〉
| MODE_IX0p_and_IMM1 ⇒ 〈x1,xA〉
| MODE_IX1_and_IMM1  ⇒ 〈x1,xB〉
| MODE_IX1p_and_IMM1 ⇒ 〈x1,xC〉
| MODE_SP1_and_IMM1  ⇒ 〈x1,xD〉

  (* 27-34: bisogna considerare l'operando implicito *)
| MODE_DIRn o          ⇒ plus_b8nc 〈x1,xE〉 〈x0,(exadecim_of_oct o)〉
  (* 35-42: bisogna considerare l'operando implicito *)
| MODE_DIRn_and_IMM1 o ⇒ plus_b8nc 〈x2,x6〉 〈x0,(exadecim_of_oct o)〉
  (* 43-58: bisogna considerare l'operando implicito *)
| MODE_TNY e           ⇒ plus_b8nc 〈x2,xE〉 〈x0,e〉
  (* 59-100: bisogna considerare gli operandi impliciti *)
| MODE_SRT t           ⇒ plus_b8nc 〈x3,xE〉 (byte8_of_bitrigesim t)
].

(* confronto fra instr_mode *)
definition eqim ≝
λi:instr_mode.λi':instr_mode.(eq_b8 (magic_of_instr_mode i) (magic_of_instr_mode i')).

(* ********************************************* *)
(* STRUMENTI PER LE DIMOSTRAZIONI DI CORRETTEZZA *)
(* ********************************************* *)

(* su tutta la lista quante volte compare il byte *)
let rec get_byte_count (m:mcu_type) (b:byte8) (c:nat)
 (l:list (Prod4T (any_opcode m) instr_mode byte8_or_word16 byte8)) on l ≝
 match l with
  [ nil ⇒ c
  | cons hd tl ⇒ match thd4T ???? hd with
   [ Byte b' ⇒ match eq_b8 b b' with
    [ true ⇒ get_byte_count m b (S c) tl
    | false ⇒ get_byte_count m b c tl
    ]
   | Word _ ⇒ get_byte_count m b c tl
   ]
  ].

(* su tutta la lista quante volte compare la word (0x9E+byte) *)
let rec get_word_count (m:mcu_type) (b:byte8) (c:nat)
 (l:list (Prod4T (any_opcode m) instr_mode byte8_or_word16 byte8)) on l ≝
 match l with
  [ nil ⇒ c
  | cons hd tl ⇒ match thd4T ???? hd with
   [ Byte _ ⇒ get_word_count m b c tl
   | Word w ⇒ match eq_w16 〈〈x9,xE〉:b〉 w with
    [ true ⇒ get_word_count m b (S c) tl
    | false ⇒ get_word_count m b c tl
    ]
   ]
  ].

(* su tutta la lista quante volte compare lo pseudocodice *)
let rec get_pseudo_count (m:mcu_type) (o:opcode) (c:nat)
 (l:list (Prod4T (any_opcode m) instr_mode byte8_or_word16 byte8)) on l ≝
 match l with
  [ nil ⇒ c
  | cons hd tl ⇒ match fst4T ???? hd with
   [ anyOP o' ⇒ match eqop m (anyOP m o) (anyOP m o') with
    [ true ⇒ get_pseudo_count m o (S c) tl
    | false ⇒ get_pseudo_count m o c tl
    ]
   ]
  ].

(* su tutta la lista quante volte compare la modalita' *)
let rec get_mode_count (m:mcu_type) (i:instr_mode) (c:nat)
 (l:list (Prod4T (any_opcode m) instr_mode byte8_or_word16 byte8)) on l ≝
 match l with
  [ nil ⇒ c
  | cons hd tl ⇒ match eqim (snd4T ???? hd) i with
   [ true ⇒ get_mode_count m i (S c) tl
   | false ⇒ get_mode_count m i c tl
   ]
  ].

(* b e' non implementato? *)
let rec test_not_impl_byte (b:byte8) (l:list byte8) on l ≝
 match l with
  [ nil ⇒ false
  | cons hd tl ⇒ match eq_b8 b hd with
   [ true ⇒ true
   | false ⇒ test_not_impl_byte b tl
   ]
  ].

(* o e' non implementato? *)
let rec test_not_impl_pseudo (o:opcode) (l:list opcode) on l ≝
 match l with
  [ nil ⇒ false
  | cons hd tl ⇒ match eqop HC05 (anyOP HC05 o) (anyOP HC05 hd) with
   [ true ⇒ true
   | false ⇒ test_not_impl_pseudo o tl
   ]
  ].

(* i e' non implementato? *)
let rec test_not_impl_mode (i:instr_mode) (l:list instr_mode) on l ≝
 match l with
  [ nil ⇒ false
  | cons hd tl ⇒ match eqim i hd with
   [ true ⇒ true
   | false ⇒ test_not_impl_mode i tl
   ]
  ].

(* su tutta la lista quante volte compare la coppia opcode,instr_mode *)
let rec get_OpIm_count (m:mcu_type) (o:any_opcode m) (i:instr_mode) (c:nat)
 (l:list (Prod4T (any_opcode m) instr_mode byte8_or_word16 byte8)) on l ≝
 match l with
  [ nil ⇒ c
  | cons hd tl ⇒
   match (eqop m o (fst4T ???? hd)) ⊗
         (eqim i (snd4T ???? hd)) with
    [ true ⇒ get_OpIm_count m o i (S c) tl
    | false ⇒ get_OpIm_count m o i c tl
    ] 
  ].

(* iteratore sugli opcode *)
definition forall_opcode ≝ λP.
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

(* iteratore sulle modalita' *)
definition forall_instr_mode ≝ λP.
  P MODE_INH
⊗ P MODE_INHA
⊗ P MODE_INHX
⊗ P MODE_INHH

⊗ P MODE_INHX0ADD
⊗ P MODE_INHX1ADD
⊗ P MODE_INHX2ADD

⊗ P MODE_IMM1
⊗ P MODE_IMM1EXT
⊗ P MODE_IMM2
⊗ P MODE_DIR1
⊗ P MODE_DIR2
⊗ P MODE_IX0
⊗ P MODE_IX1
⊗ P MODE_IX2
⊗ P MODE_SP1
⊗ P MODE_SP2

⊗ P MODE_DIR1_to_DIR1
⊗ P MODE_IMM1_to_DIR1
⊗ P MODE_IX0p_to_DIR1
⊗ P MODE_DIR1_to_IX0p

⊗ P MODE_INHA_and_IMM1
⊗ P MODE_INHX_and_IMM1
⊗ P MODE_IMM1_and_IMM1
⊗ P MODE_DIR1_and_IMM1
⊗ P MODE_IX0_and_IMM1
⊗ P MODE_IX0p_and_IMM1
⊗ P MODE_IX1_and_IMM1
⊗ P MODE_IX1p_and_IMM1
⊗ P MODE_SP1_and_IMM1

⊗ forall_oct (λo. P (MODE_DIRn o))
⊗ forall_oct (λo. P (MODE_DIRn_and_IMM1 o))
⊗ forall_exadecim (λe. P (MODE_TNY e))
⊗ forall_bitrigesim (λt. P (MODE_SRT t)).
