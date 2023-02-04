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

include "emulator/read_write/load_write_base.ma".
include "emulator/status/status_getter.ma".
include "emulator/read_write/IP2022_fetch.ma".

(* lettura da [OLD PC<<1 + 1] : argomento non caricato dal fetch word-aligned *)
ndefinition mode_IMM1_load ≝
λt:memory_impl.λs:any_status IP2022 t.
 match IP2022_pc_translation (get_pc_reg … s) with
  [ pair seg pc ⇒ mem_read_s … s seg (succc ? pc) ].

(* SCHEMA:
   ADDRX=0x00 [ADDRH|ADDRL] 16Kb PROGRAM RAM
   ADDRX=0x01 [ADDRH|ADDRL] 64Kb FLASH
   ADDRX=0x80 [ADDRH|ADDRL] 64Kb EXTERNAL RAM
   ADDRX=0x81 [ADDRH|ADDRL] 64Kb EXTERNAL RAM *)

(* lettura da [ADDR] *)
ndefinition mode_ADDR_load ≝
λt:memory_impl.λs:any_status IP2022 t.
 opt_map … (get_addr_reg … s)
  (λaddr.match eqc ? (w24x addr) 〈x0,x0〉 with
   (* lettura della RAM, sempre non blocking *)
   [ true ⇒ opt_map … (mem_read_s … s o1 (clrLSBc ? 〈(w24h addr):(w24l addr)〉))
             (λbh.opt_map … (mem_read_s … s o1 (setLSBc ? 〈(w24h addr):(w24l addr)〉))
              (λbl.Some ? 〈bh:bl〉))
   (* lettura della FLASH da codice in RAM : operazione non bloccante non implementata! *)
   (* lettura da alri ADDRX, errore *)
   | false ⇒ match (gtc ? (w24x addr) 〈x0,x1〉)⊕(⊖(IP2022_pc_flashtest (get_pc_reg … s))) with
    [ true ⇒ None ?
    | false ⇒ opt_map … (mem_read_s … s o2 (clrLSBc ? 〈(w24h addr):(w24l addr)〉))
               (λbh.opt_map … (mem_read_s … s o2 (setLSBc ? 〈(w24h addr):(w24l addr)〉))
                (λbl.Some ? 〈bh:bl〉))
    ]
   ]).

(* scrittura su [ADDR] *)
ndefinition mode_ADDR_write ≝
λt:memory_impl.λs:any_status IP2022 t.λval:word16.
 opt_map ?? (get_addr_reg … s)
  (λaddr.opt_map ?? (match eqc ? (w24x addr) 〈x0,x0〉 with
                   [ true ⇒ Some ? o1
                   | false ⇒ match eqc ? (w24x addr) 〈x0,x1〉 with
                    [ true ⇒ Some ? o2
                    | false ⇒ None ? ]])
   (λseg.opt_map ?? (mem_write_s ?? s seg (clrLSBc ?  〈(w24h addr):(w24l addr)〉) (cnH ? val))
    (λs'.mem_write_s ?? s' seg (setLSBc ?  〈(w24h addr):(w24l addr)〉) (cnL ? val)))).

(* IMM1 > 0 : lettura/scrittura da [IMM1] *)
(* else     : lettura/scrittura da [IP] : IP ≥ 0x20 *)
ndefinition mode_DIR1IP_aux ≝
λt:memory_impl.λs:any_status IP2022 t.λT.λf:word16 → option T.
 opt_map … (mode_IMM1_load t s)
  (λaddr.match eqc ? addr 〈x0,x0〉 with
   (* xxxxxxx0 00000000 → [IP] *)
   [ true ⇒ opt_map … (get_ip_reg … s)
             (λip.match gec ? ip 〈〈x0,x0〉:〈x2,x0〉〉 with
              (* IP ≥ 0x20 *)
              [ true ⇒ f ip
              | false ⇒ None ? ])
   (* xxxxxxx0 nnnnnnnn → [IMM1] *)
   | false ⇒ f (extu_w16 addr)
   ]).

(* IMM1 < 0x80 : lettura/scrittura da [DP+IMM1] : DP+IMM1 ≥ 0x20 *)
(* else        : lettura/scrittura da [SP+IMM1] : SP+IMM1 ≥ 0x20 *)
ndefinition mode_DPSP_aux ≝
λt:memory_impl.λs:any_status IP2022 t.λT.λf:word16 → option T.
 opt_map … (mode_IMM1_load t s)
  (λaddr.opt_map … (match getMSBc ? addr with
                    (* xxxxxxx1 1nnnnnnn → [SP+IMM1] *)
                    [ true ⇒ get_sp_reg … s
                    (* xxxxxxx1 0nnnnnnn → [DP+IMM1] *)
                    | false ⇒ get_dp_reg … s ])
   (λreg.match gec ? (plusc_d_d ? reg (extu_w16 (clrMSBc ? addr))) 〈〈x0,x0〉:〈x2,x0〉〉 with
    (* reg+IMM1 ≥ 0x20 *)
    [ true ⇒ f (plusc_d_d ? reg (extu_w16 (clrMSBc ? addr)))
    | false ⇒ None ? ])).

(* FR0 *)
ndefinition mode_FR0_load ≝
λt:memory_impl.λs:any_status IP2022 t.
 mode_DIR1IP_aux t s byte8 (memory_filter_read … s).

ndefinition mode_FR0n_load ≝
λt:memory_impl.λs:any_status IP2022 t.λsub:oct.
 mode_DIR1IP_aux t s bool (λaddr.memory_filter_read_bit … s addr sub).

ndefinition mode_FR0_write ≝
λt:memory_impl.λs:any_status IP2022 t.λflag:aux_mod_type.λval:byte8.
 mode_DIR1IP_aux t s (any_status IP2022 t) (λaddr.memory_filter_write … s addr flag val).

ndefinition mode_FR0n_write ≝
λt:memory_impl.λs:any_status IP2022 t.λsub:oct.λval:bool.
 mode_DIR1IP_aux t s (any_status IP2022 t) (λaddr.memory_filter_write_bit … s addr sub val).

(* FR1 *)
ndefinition mode_FR1_load ≝
λt:memory_impl.λs:any_status IP2022 t.
 mode_DPSP_aux t s byte8 (memory_filter_read … s).

ndefinition mode_FR1n_load ≝
λt:memory_impl.λs:any_status IP2022 t.λsub:oct.
 mode_DPSP_aux t s bool (λaddr.memory_filter_read_bit … s addr sub).

ndefinition mode_FR1_write ≝
λt:memory_impl.λs:any_status IP2022 t.λflag:aux_mod_type.λval:byte8.
 mode_DPSP_aux t s (any_status IP2022 t) (λaddr.memory_filter_write … s addr flag val).

ndefinition mode_FR1n_write ≝
λt:memory_impl.λs:any_status IP2022 t.λsub:oct.λval:bool.
 mode_DPSP_aux t s (any_status IP2022 t) (λaddr.memory_filter_write_bit … s addr sub val).

(* ************************************** *)
(* raccordo di tutte le possibili letture *)
(* ************************************** *)

(* addr+=2 *)
ndefinition aux_inc_addr2 ≝
λt:memory_impl.λs:any_status IP2022 t.
 set_addr_reg_sIP2022 t s (succ_w24 (succ_w24 (get_addr_reg_IP2022 (alu … s)))).

ndefinition IP2022_multi_mode_load_auxb ≝
λt.λs:any_status IP2022 t.λcur_pc:word16.λi:IP2022_instr_mode.match i with
(* NO: non ci sono indicazioni *)
   [ MODE_INH ⇒ None ?
(* NO: solo word *)
   | MODE_INHADDR ⇒ None ?
(* NO: solo word *)
   | MODE_INHADDRpp ⇒ None ?

(* IMM3 *)
   | MODE_IMM3 o ⇒ Some ? (triple … s (extu_b8 (ex_of_oct o)) cur_pc)
(* IMM8 *)
   | MODE_IMM8 ⇒ opt_map … (mode_IMM1_load t s)
                  (λb.Some ? (triple … s b cur_pc))
(* NO: solo lettura word *)
   | MODE_IMM13 _ ⇒ None ?

(* NO: solo word *)
   | MODE_FR0_and_W ⇒ None ?
(* NO: solo word *)
   | MODE_FR1_and_W ⇒ None ?
(* NO: solo word *)
   | MODE_W_and_FR0 ⇒ None ?
(* NO: solo word *)
   | MODE_W_and_FR1 ⇒ None ?

(* [FRn] *)
   | MODE_FR0n o ⇒ opt_map … (mode_FR0n_load t s o)
                    (λb.Some ? (triple … s (extu_b8 (match b with [ true ⇒ x1 | false ⇒ x0 ])) cur_pc))
(* [FRn] *)
   | MODE_FR1n o ⇒ opt_map … (mode_FR1n_load t s o)
                    (λb.Some ? (triple … s (extu_b8 (match b with [ true ⇒ x1 | false ⇒ x0 ])) cur_pc))
   ].

ndefinition IP2022_multi_mode_load_auxw ≝
λt.λs:any_status IP2022 t.λcur_pc:word16.λi:IP2022_instr_mode.match i with
(* NO: non ci sono indicazioni *)
   [ MODE_INH ⇒ None ?
(* [ADDR] *)
   | MODE_INHADDR ⇒ opt_map … (mode_ADDR_load t s)
                     (λw.Some ? (triple … s w cur_pc))
(* [ADDR], ADDR+=2 *)
   | MODE_INHADDRpp ⇒ opt_map … (mode_ADDR_load t s)
                       (λw.Some ? (triple … (aux_inc_addr2 t s) w cur_pc))

(* NO: solo lettura byte *)
   | MODE_IMM3 _ ⇒ None ?
(* NO: solo lettura byte *)
   | MODE_IMM8 ⇒ None ?
(* IMM13 *)
   | MODE_IMM13 bt ⇒ opt_map … (mode_IMM1_load t s)
                      (λb.Some ? (triple … s 〈(b8_of_bit bt):b〉 cur_pc))

(* FR, W → FR *)
   | MODE_FR0_and_W ⇒ opt_map … (mode_FR0_load t s)
                       (λfr.Some ? (triple … s 〈fr:(get_acc_8_low_reg … s)〉 cur_pc))
(* FR, W → FR *)
   | MODE_FR1_and_W ⇒ opt_map … (mode_FR1_load t s)
                       (λfr.Some ? (triple … s 〈fr:(get_acc_8_low_reg … s)〉 cur_pc))
(* W, FR → W *)
   | MODE_W_and_FR0 ⇒ opt_map … (mode_FR0_load t s)
                       (λfr.Some ? (triple … s 〈(get_acc_8_low_reg … s):fr〉 cur_pc))
(* W, FR → W *)
   | MODE_W_and_FR1 ⇒ opt_map … (mode_FR1_load t s)
                       (λfr.Some ? (triple … s 〈(get_acc_8_low_reg … s):fr〉 cur_pc))

(* NO: solo byte *)
   | MODE_FR0n _ ⇒ None ?
(* NO: solo byte *)
   | MODE_FR1n _ ⇒ None ?
   ].

(* **************************************** *)
(* raccordo di tutte le possibili scritture *)
(* **************************************** *)

ndefinition IP2022_multi_mode_write_auxb ≝
λt.λs:any_status IP2022 t.λcur_pc:word16.λflag:aux_mod_type.λi:IP2022_instr_mode.λwriteb:byte8.match i with
(* NO: non ci sono indicazioni *)
   [ MODE_INH ⇒ None ?
(* NO: solo word *)
   | MODE_INHADDR ⇒ None ?
(* NO: solo word *)
   | MODE_INHADDRpp ⇒ None ?

(* NO: solo lettura byte *)
   | MODE_IMM3 _ ⇒ None ?
(* NO: solo lettura byte *)
   | MODE_IMM8 ⇒ None ?
(* NO: solo lettura word *)
   | MODE_IMM13 _ ⇒ None ?

(* FR, W → FR *)
   | MODE_FR0_and_W ⇒ opt_map … (mode_FR0_write t s flag writeb)
                       (λs'.Some ? (pair … s' cur_pc))
(* FR, W → FR *)
   | MODE_FR1_and_W ⇒ opt_map … (mode_FR1_write t s flag writeb)
                       (λs'.Some ? (pair … s' cur_pc))
(* W, FR → W *)
   | MODE_W_and_FR0 ⇒ Some ? (pair … (set_acc_8_low_reg … s writeb) cur_pc)
(* W, FR → W *)
   | MODE_W_and_FR1 ⇒ Some ? (pair … (set_acc_8_low_reg … s writeb) cur_pc)

(* [FRn] *)
   | MODE_FR0n o ⇒ opt_map … (mode_FR0n_write t s o (getn_array8T o ? (bits_of_byte8 writeb)))
                    (λs'.Some ? (pair … s' cur_pc))
(* [FRn] *)
   | MODE_FR1n o ⇒ opt_map … (mode_FR1n_write t s o (getn_array8T o ? (bits_of_byte8 writeb)))
                    (λs'.Some ? (pair … s' cur_pc))
   ].

ndefinition IP2022_multi_mode_write_auxw ≝
λt.λs:any_status IP2022 t.λcur_pc:word16.λi:IP2022_instr_mode.λwritew:word16.match i with
(* NO: non ci sono indicazioni *)
   [ MODE_INH ⇒ None ?
(* [ADDR] *)
   | MODE_INHADDR ⇒ opt_map … (mode_ADDR_write t s writew)
                     (λs'.Some ? (pair … s' cur_pc))
(* [ADDR], ADDR+=2 *)
   | MODE_INHADDRpp ⇒ opt_map … (mode_ADDR_write t s writew)
                       (λs'.Some ? (pair … (aux_inc_addr2 t s') cur_pc))

(* NO: solo lettura byte *)
   | MODE_IMM3 _ ⇒ None ?
(* NO: solo lettura byte *)
   | MODE_IMM8 ⇒ None ?
(* NO: solo lettura word *)
   | MODE_IMM13 _ ⇒ None ?

(* NO: solo byte *)
   | MODE_FR0_and_W ⇒ None ?
(* NO: solo byte *)
   | MODE_FR1_and_W ⇒ None ?
(* NO: solo byte *)
   | MODE_W_and_FR0 ⇒ None ?
(* NO: solo byte *)
   | MODE_W_and_FR1 ⇒ None ?

(* NO: solo byte *)
   | MODE_FR0n _ ⇒ None ?
(* NO: solo byte *)
   | MODE_FR1n _ ⇒ None ?
   ].
