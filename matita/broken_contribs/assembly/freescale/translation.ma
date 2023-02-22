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

include "freescale/table_HC05.ma".
include "freescale/table_HC08.ma".
include "freescale/table_HCS08.ma".
include "freescale/table_RS08.ma".

(* ***************************** *)
(* TRADUZIONE ESADECIMALE → INFO *)
(* ***************************** *)

(* accesso alla tabella della ALU prescelta *)
definition opcode_table ≝
λm:mcu_type.
 match m
  return λm:mcu_type.list (Prod4T (any_opcode m) instr_mode byte8_or_word16 byte8)
 with
  [ HC05  ⇒ opcode_table_HC05
  | HC08  ⇒ opcode_table_HC08
  | HCS08 ⇒ opcode_table_HCS08
  | RS08  ⇒ opcode_table_RS08
 ].

(* traduzione mcu+esadecimale → info *)
(* NB: la ricerca per byte non matcha con una word con lo stesso byte superiore uguale *)
(* NB: per matchare una word (precode+code) bisogna passare una word *)
(* NB: il risultato e' sempre un'opzione, NON esiste un dummy opcode tipo UNKNOWN/ILLEGAL *)
definition full_info_of_word16 ≝
λm:mcu_type.λborw:byte8_or_word16.
 let rec aux param ≝ match param with
  [ nil ⇒ None ?
  | cons hd tl ⇒
   match thd4T ???? hd with
    [ Byte b ⇒ match borw with
     [ Byte borw' ⇒ match eq_b8 borw' b with
      [ true ⇒ Some ? hd | false ⇒ aux tl ]
     | Word _ ⇒ aux tl ]
    | Word w ⇒ match borw with
     [ Byte _ ⇒ aux tl
     | Word borw' ⇒ match eq_w16 borw' w with
      [ true ⇒ Some ? hd | false ⇒ aux tl ]            
    ]]] in aux (opcode_table m).

(* ******************************************************* *)
(* TRADUZIONE MCU+OPCODE+MODALITA'+ARGOMENTI → ESADECIMALE *)
(* ******************************************************* *)

(* introduzione di un tipo byte8 dipendente dall'mcu_type (phantom type) *)
inductive t_byte8 (m:mcu_type) : Type ≝
 TByte : byte8 → t_byte8 m.

definition c_TByte ≝ TByte.

coercion c_TByte.

(* introduzione di un tipo dipendente (dalla modalita') per gli argomenti *)
inductive MA_check : instr_mode → Type ≝
  maINH              : MA_check MODE_INH
| maINHA             : MA_check MODE_INHA
| maINHX             : MA_check MODE_INHX
| maINHH             : MA_check MODE_INHH
| maINHX0ADD         : MA_check MODE_INHX0ADD
| maINHX1ADD         : byte8 → MA_check MODE_INHX1ADD
| maINHX2ADD         : word16 → MA_check MODE_INHX2ADD
| maIMM1             : byte8  → MA_check MODE_IMM1
| maIMM1EXT          : byte8  → MA_check MODE_IMM1EXT
| maIMM2             : word16 → MA_check MODE_IMM2
| maDIR1             : byte8  → MA_check MODE_DIR1
| maDIR2             : word16 → MA_check MODE_DIR2
| maIX0              : MA_check MODE_IX0
| maIX1              : byte8  → MA_check MODE_IX1
| maIX2              : word16 → MA_check MODE_IX2
| maSP1              : byte8  → MA_check MODE_SP1
| maSP2              : word16 → MA_check MODE_SP2
| maDIR1_to_DIR1     : byte8 → byte8 → MA_check MODE_DIR1_to_DIR1
| maIMM1_to_DIR1     : byte8 → byte8 → MA_check MODE_IMM1_to_DIR1
| maIX0p_to_DIR1     : byte8 → MA_check MODE_IX0p_to_DIR1
| maDIR1_to_IX0p     : byte8 → MA_check MODE_DIR1_to_IX0p
| maINHA_and_IMM1    : byte8 → MA_check MODE_INHA_and_IMM1
| maINHX_and_IMM1    : byte8 → MA_check MODE_INHX_and_IMM1
| maIMM1_and_IMM1    : byte8 → byte8 → MA_check MODE_IMM1_and_IMM1
| maDIR1_and_IMM1    : byte8 → byte8 → MA_check MODE_DIR1_and_IMM1
| maIX0_and_IMM1     : byte8 → MA_check MODE_IX0_and_IMM1
| maIX0p_and_IMM1    : byte8 → MA_check MODE_IX0p_and_IMM1
| maIX1_and_IMM1     : byte8 → byte8 → MA_check MODE_IX1_and_IMM1
| maIX1p_and_IMM1    : byte8 → byte8 → MA_check MODE_IX1p_and_IMM1
| maSP1_and_IMM1     : byte8 → byte8 → MA_check MODE_SP1_and_IMM1
| maDIRn             : ∀o.byte8 → MA_check (MODE_DIRn o)
| maDIRn_and_IMM1    : ∀o.byte8 → byte8 → MA_check (MODE_DIRn_and_IMM1 o)
| maTNY              : ∀e.MA_check (MODE_TNY e)
| maSRT              : ∀t.MA_check (MODE_SRT t)
.

(* tipo istruzione per unificare in una lista omogenea il sorgente *)
inductive instruction : Type ≝ 
instr: ∀i:instr_mode.opcode → MA_check i → instruction.

definition c_instr ≝ instr.

coercion c_instr.

(* picker: trasforma l'argomento necessario in input a bytes_of_pseudo_instr_mode_param:
   MA_check i → list (t_byte8 m) *)
definition args_picker ≝
λm:mcu_type.λi:instr_mode.λargs:MA_check i.
 match args with
  (* inherent: legale se nessun operando *) 
  [ maINH    ⇒ nil ? 
  | maINHA   ⇒ nil ? 
  | maINHX   ⇒ nil ? 
  | maINHH   ⇒ nil ?
  (* inherent address: legale se nessun operando/1 byte/1 word *)
  | maINHX0ADD ⇒ nil ?
  | maINHX1ADD b ⇒ [ TByte m b ]
  | maINHX2ADD w ⇒ [ TByte m (w16h w); TByte m (w16l w) ]    
  (* _0/1/2: legale se nessun operando/1 byte/1 word *)
  | maIMM1 b ⇒ [ TByte m b ]
  | maIMM1EXT b ⇒ [ TByte m b ]
  | maIMM2 w ⇒ [ TByte m (w16h w); TByte m (w16l w) ]
  | maDIR1 b ⇒ [ TByte m b ]
  | maDIR2 w ⇒ [ TByte m (w16h w); TByte m (w16l w) ]
  | maIX0    ⇒ nil ?
  | maIX1 b  ⇒ [ TByte m b ]
  | maIX2 w  ⇒ [ TByte m (w16h w); TByte m (w16l w) ]
  | maSP1 b  ⇒ [ TByte m b ]
  | maSP2 w  ⇒ [ TByte m (w16h w); TByte m (w16l w) ]
  (* movimento: legale se 2 operandi byte *)
  | maDIR1_to_DIR1 b1 b2  ⇒ [ TByte m b1 ; TByte m b2 ]
  | maIMM1_to_DIR1 b1 b2  ⇒ [ TByte m b1 ; TByte m b2 ]
  | maIX0p_to_DIR1 b      ⇒ [ TByte m b]
  | maDIR1_to_IX0p b      ⇒ [ TByte m b]
  (* cbeq/dbnz: legale se 1/2 operandi byte *)
  | maINHA_and_IMM1 b     ⇒ [ TByte m b]
  | maINHX_and_IMM1 b     ⇒ [ TByte m b]
  | maIMM1_and_IMM1 b1 b2 ⇒ [ TByte m b1 ; TByte m b2 ]
  | maDIR1_and_IMM1 b1 b2 ⇒ [ TByte m b1 ; TByte m b2 ]
  | maIX0_and_IMM1  b     ⇒ [ TByte m b]
  | maIX0p_and_IMM1 b     ⇒ [ TByte m b]
  | maIX1_and_IMM1  b1 b2 ⇒ [ TByte m b1 ; TByte m b2 ]
  | maIX1p_and_IMM1 b1 b2 ⇒ [ TByte m b1 ; TByte m b2 ]
  | maSP1_and_IMM1  b1 b2 ⇒ [ TByte m b1 ; TByte m b2 ]
  (* DIRn: legale se 1 operando byte *)
  | maDIRn _ b ⇒ [ TByte m b]
  (* DIRn_and_IMM1: legale se 2 operandi byte *)
  | maDIRn_and_IMM1 _ b1 b2 ⇒ [ TByte m b1 ; TByte m b2 ]
  (* TNY: legale se nessun operando *)
  | maTNY _ ⇒ nil ?
  (* SRT: legale se nessun operando *)
  | maSRT _ ⇒ nil ?
  ].

(* trasformatore finale: mcu+opcode+instr_mode+args → list (t_byte8 m) *)
definition bytes_of_pseudo_instr_mode_param ≝
λm:mcu_type.λo:any_opcode m.λi:instr_mode.λp:MA_check i.
let rec aux param  ≝ match param with
 [ nil ⇒ None ? | cons hd tl ⇒
  match (eqop m o (fst4T ???? hd)) ⊗ (eqim i (snd4T ???? hd)) with
   [ true ⇒ match thd4T ???? hd with 
    [ Byte isab ⇒ 
     Some ? ([ (TByte m isab) ]@(args_picker m i p))
    | Word isaw ⇒
     Some ? ([ (TByte m (w16h isaw)) ; (TByte m (w16l isaw)) ]@(args_picker m i p))
    ]
   | false ⇒ aux tl ]] in aux (opcode_table m).

(* tipatore degli opcode generici *)
definition opcode_to_any ≝ λm:mcu_type.λo:opcode.anyOP m o.

(* ****************************** *)
(* APPROCCIO COMPILAZIONE AL VOLO *)
(* ****************************** *)

(* ausiliario di compile *)
definition defined ≝
 λT:Type.λo:option T.
  match o with
   [ None ⇒ False
   | Some _ ⇒ True
   ].

(* compila solo se l'intera istruzione+modalita'+argomenti ha riscontro nelle tabelle *)
definition compile ≝
λmcu:mcu_type.λi:instr_mode.λop:opcode.λarg:MA_check i.
 let res ≝ bytes_of_pseudo_instr_mode_param mcu (opcode_to_any mcu op) i arg in
  λp:defined ? res.
   let value ≝
    match res return λres: option (list (t_byte8 mcu)).defined ? res → ? with
    [ None ⇒ λp:defined (list (t_byte8 mcu)) (None ?).
       False_rect ? p
    | Some v ⇒ λ_:defined ? (Some ? v).v
    ] p in value.

(* detipatore del compilato: (t_byte8 m) → byte8 *)
definition source_to_byte8 ≝
λmcu:mcu_type.
 match mcu
  return λmcu:mcu_type.list (t_byte8 mcu) → list byte8 with
  [ HC05 ⇒ λl:list (t_byte8 HC05).
   let rec aux (p1:list (t_byte8 HC05)) (p2:list byte8) ≝ match p1 with
    [ nil ⇒ p2 | cons hd tl ⇒ match hd with [ TByte b ⇒ aux tl (p2@[b]) ]] in aux l ([])
  | HC08 ⇒ λl:list (t_byte8 HC08).
   let rec aux (p1:list (t_byte8 HC08)) (p2:list byte8) ≝ match p1 with
    [ nil ⇒ p2 | cons hd tl ⇒ match hd with [ TByte b ⇒ aux tl (p2@[b]) ]] in aux l ([])
  | HCS08 ⇒ λl:list (t_byte8 HCS08).
   let rec aux (p1:list (t_byte8 HCS08)) (p2:list byte8) ≝ match p1 with
    [ nil ⇒ p2 | cons hd tl ⇒ match hd with [ TByte b ⇒ aux tl (p2@[b]) ]] in aux l ([])
  | RS08 ⇒ λl:list (t_byte8 RS08).
   let rec aux (p1:list (t_byte8 RS08)) (p2:list byte8) ≝ match p1 with
    [ nil ⇒ p2 | cons hd tl ⇒ match hd with [ TByte b ⇒ aux tl (p2@[b]) ]] in aux l ([])
  ].

(* esempio da riciclare su come scrivere un sorgente *)
(*
definition source_example_of_correct_HC08: list byte8 ≝
let m ≝ HC08 in
 source_to_byte8 m (
  (compile m ? CLR maINHA I) @
  (compile m ? NOP maINH I) @
  (compile m ? BRSETn (maDIRn_and_IMM1 x1 〈x1,x2〉 〈x3,x4〉) I) @
  (compile m ? ADD maIX0 I) @
  (compile m ? ADD (maIX1 〈x1,x2〉) I) @
  (compile m ? ADD (maSP2 〈〈x1,x2〉:〈x3,x4〉〉) I)
 ).
*)
