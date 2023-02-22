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

(* accesso argomenti immediati solo da segmento 0 [mem_read_s … o0] *)
(* accesso indiretto solo da segmento 0 filtrato [aux_load] *)

ndefinition code_seg ≝ o0.

(* lettura da [curpc]: IMM1 *)
ndefinition mode_IMM1_load ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map … (mem_read_s … s code_seg cur_pc)
  (λb.Some ? (triple … s b (succc ? cur_pc))).

(* lettura da [curpc]: IMM1 + estensione a word *)
ndefinition mode_IMM1EXT_load ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map … (mem_read_s …  s code_seg cur_pc)
  (λb.Some ? (triple … s (extu_w16 b) (succc ? cur_pc))).

(* lettura da [curpc]: IMM2 *)
ndefinition mode_IMM2_load ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map … (mem_read_s …  s code_seg cur_pc)
  (λbh.opt_map … (mem_read_s …  s code_seg (succc ? cur_pc))
   (λbl.Some ? (triple … s 〈bh:bl〉 (succc ? (succc ? cur_pc))))).

(* lettura da [byte [curpc]]: true=DIR1 loadb, false=DIR1 loadw *)
ndefinition mode_DIR1_load ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map … (mem_read_s …  s code_seg cur_pc)
  (λaddr.(aux_load … byteflag) s (extu_w16 addr) cur_pc x1).

(* lettura da [byte [curpc]]: loadbit *)
ndefinition mode_DIR1n_load ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λsub:oct.
 opt_map … (mem_read_s …  s  code_seg cur_pc)
  (λaddr.loadbit_from … s (extu_w16 addr) sub cur_pc x1).

(* scrittura su [byte [curpc]]: true=DIR1 writeb, false=DIR1 writew *)
ndefinition mode_DIR1_write ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
λwritebw:match byteflag with [ true ⇒ byte8 | false ⇒ word16 ].
 opt_map … (mem_read_s …  s code_seg cur_pc)
  (λaddr.(aux_write … byteflag) s (extu_w16 addr) auxMode_ok cur_pc x1 writebw).

(* scrittura su [byte [curpc]]: writebit *)
ndefinition mode_DIR1n_write ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.λsub:oct.λwriteb:bool.
 opt_map … (mem_read_s …  s code_seg cur_pc)
  (λaddr.writebit_to … s (extu_w16 addr) sub cur_pc x1 writeb).

(* lettura da [word [curpc]]: true=DIR2 loadb, false=DIR2 loadw *)
ndefinition mode_DIR2_load ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map … (mem_read_s …  s code_seg cur_pc)
  (λaddrh.opt_map … (mem_read_s …  s code_seg (succc ? cur_pc))
   (λaddrl.(aux_load … byteflag) s 〈addrh:addrl〉 cur_pc x2)).

(* scrittura su [word [curpc]]: true=DIR2 writeb, false=DIR2 writew *)
ndefinition mode_DIR2_write ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
λwritebw:match byteflag with [ true ⇒ byte8 | false ⇒ word16 ].
 opt_map … (mem_read_s …  s code_seg cur_pc)
  (λaddrh.opt_map … (mem_read_s …  s code_seg (succc ? cur_pc))
   (λaddrl.(aux_write … byteflag) s 〈addrh:addrl〉 auxMode_ok cur_pc x2 writebw)).

ndefinition get_IX ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 match m with
  [ HC05 ⇒ opt_map … (get_indX_8_low_reg … s) (λindx.Some ? (extu_w16 indx)) 
  | HC08 ⇒ opt_map … (get_indX_16_reg … s) (λindx.Some ? indx) 
  | HCS08 ⇒ opt_map … (get_indX_16_reg … s) (λindx.Some ? indx) 
  | RS08 ⇒ None ?
  | IP2022 ⇒ None ? ].

(* lettura da [IX]: true=IX0 loadb, false=IX0 loadw *)
ndefinition mode_IX0_load ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map … (get_IX … s)
  (λaddr.(aux_load … byteflag) s addr cur_pc x0).

(* scrittura su [IX]: true=IX0 writeb, false=IX0 writew *)
ndefinition mode_IX0_write ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
λwritebw:match byteflag with [ true ⇒ byte8 | false ⇒ word16 ].
 opt_map … (get_IX … s)
  (λaddr.(aux_write … byteflag) s addr auxMode_ok cur_pc x0 writebw).

(* lettura da [IX+byte [pc]]: true=IX1 loadb, false=IX1 loadw *)
ndefinition mode_IX1_load ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map … (get_IX … s)
  (λaddr.opt_map … (mem_read_s …  s code_seg cur_pc)
   (λoffs.(aux_load … byteflag) s (plusc_d_d ? addr (extu_w16 offs)) cur_pc x1)).

(* lettura da X+[byte curpc] *)
ndefinition mode_IX1ADD_load ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map … (get_IX … s)
  (λaddr.opt_map … (mem_read_s …  s code_seg cur_pc)
   (λb.Some ? (triple … s (plusc_d_d ? addr (extu_w16 b)) (succc ? cur_pc)))).

(* scrittura su [IX+byte [pc]]: true=IX1 writeb, false=IX1 writew *)
ndefinition mode_IX1_write ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
λwritebw:match byteflag with [ true ⇒ byte8 | false ⇒ word16 ].
 opt_map … (get_IX … s)
  (λaddr.opt_map … (mem_read_s …  s code_seg cur_pc)
   (λoffs.(aux_write … byteflag) s (plusc_d_d ? addr (extu_w16 offs)) auxMode_ok cur_pc x1 writebw)).

(* lettura da [IX+word [pc]]: true=IX2 loadb, false=IX2 loadw *)
ndefinition mode_IX2_load ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map … (get_IX … s)
  (λaddr.opt_map … (mem_read_s …  s code_seg cur_pc)
   (λoffsh.opt_map … (mem_read_s …  s code_seg (succc ? cur_pc))
    (λoffsl.(aux_load … byteflag) s (plusc_d_d ? addr 〈offsh:offsl〉) cur_pc x2))).

(* lettura da X+[word curpc] *)
ndefinition mode_IX2ADD_load ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map … (get_IX … s)
  (λaddr.opt_map … (mem_read_s …  s code_seg cur_pc)
   (λbh.opt_map … (mem_read_s …  s code_seg (succc ? cur_pc))
    (λbl.Some ? (triple … s (plusc_d_d ? addr 〈bh:bl〉) (succc ? (succc ? cur_pc)))))).

(* scrittura su [IX+word [pc]]: true=IX2 writeb, false=IX2 writew *)
ndefinition mode_IX2_write ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
λwritebw:match byteflag with [ true ⇒ byte8 | false ⇒ word16 ].
 opt_map … (get_IX … s)
  (λaddr.opt_map … (mem_read_s …  s code_seg cur_pc)
   (λoffsh.opt_map … (mem_read_s …  s code_seg (succc ? cur_pc))
    (λoffsl.(aux_write … byteflag) s (plusc_d_d ? addr 〈offsh:offsl〉) auxMode_ok cur_pc x2 writebw))).

(* lettura da [SP+byte [pc]]: true=SP1 loadb, false=SP1 loadw *)
ndefinition mode_SP1_load ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map … (get_sp_reg … s)
  (λaddr.opt_map … (mem_read_s …  s code_seg cur_pc)
   (λoffs.(aux_load … byteflag) s (plusc_d_d ? addr (extu_w16 offs)) cur_pc x1)).

(* scrittura su [SP+byte [pc]]: true=SP1 writeb, false=SP1 writew *)
ndefinition mode_SP1_write ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
λwritebw:match byteflag with [ true ⇒ byte8 | false ⇒ word16 ].
 opt_map … (get_sp_reg … s)
  (λaddr.opt_map … (mem_read_s …  s code_seg cur_pc)
   (λoffs.(aux_write … byteflag) s (plusc_d_d ? addr (extu_w16 offs)) auxMode_ok cur_pc x1 writebw)).

(* lettura da [SP+word [pc]]: true=SP2 loadb, false=SP2 loadw *)
ndefinition mode_SP2_load ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
 opt_map … (get_sp_reg … s)
  (λaddr.opt_map … (mem_read_s …  s code_seg cur_pc)
   (λoffsh.opt_map … (mem_read_s …  s code_seg (succc ? cur_pc))
    (λoffsl.(aux_load … byteflag) s (plusc_d_d ? addr 〈offsh:offsl〉) cur_pc x2))).

(* scrittura su [SP+word [pc]]: true=SP2 writeb, false=SP2 writew *)
ndefinition mode_SP2_write ≝
λbyteflag:bool.λm:mcu_type.λt:memory_impl.λs:any_status m t.λcur_pc:word16.
λwritebw:match byteflag with [ true ⇒ byte8 | false ⇒ word16 ].
 opt_map … (get_sp_reg … s)
  (λaddr.opt_map … (mem_read_s …  s code_seg cur_pc)
   (λoffsh.opt_map … (mem_read_s …  s code_seg (succc ? cur_pc))
    (λoffsl.(aux_write … byteflag) s (plusc_d_d ? addr 〈offsh:offsl〉) auxMode_ok cur_pc x2 writebw))).

(* ************************************** *)
(* raccordo di tutte le possibili letture *)
(* ************************************** *)

(* H:X++ *)
ndefinition aux_inc_indX_16 ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
 opt_map … (get_indX_16_reg … s)
  (λX_op.opt_map … (set_indX_16_reg … s (succc ? X_op))
   (λs_tmp.Some ? s_tmp)).

ndefinition Freescale_multi_mode_load_auxb ≝
λm,t.λs:any_status m t.λcur_pc:word16.λi:Freescale_instr_mode.match i with
(* NO: non ci sono indicazioni *)
   [ MODE_INH  ⇒ None ?
(* restituisce A *)
   | MODE_INHA ⇒ Some ? (triple … s (get_acc_8_low_reg … s) cur_pc)
(* restituisce X *)
   | MODE_INHX ⇒ opt_map … (get_indX_8_low_reg … s)
                  (λindx.Some ? (triple … s indx cur_pc))
(* restituisce H *)
   | MODE_INHH ⇒ opt_map … (get_indX_8_high_reg … s)
                  (λindx.Some ? (triple … s indx cur_pc))

(* NO: solo lettura word *)
  | MODE_INHX0ADD ⇒ None ?
(* NO: solo lettura word *)
  | MODE_INHX1ADD ⇒ None ?
(* NO: solo lettura word *)
  | MODE_INHX2ADD ⇒ None ?

(* preleva 1 byte immediato *) 
   | MODE_IMM1 ⇒ mode_IMM1_load … s cur_pc
(* NO: solo lettura word *)
   | MODE_IMM1EXT ⇒ None ?
(* NO: solo lettura word *)
   | MODE_IMM2 ⇒ None ?
(* preleva 1 byte da indirizzo diretto 1 byte *) 
   | MODE_DIR1 ⇒ mode_DIR1_load true … s cur_pc
(* preleva 1 byte da indirizzo diretto 1 word *)
   | MODE_DIR2 ⇒ mode_DIR2_load true … s cur_pc
(* preleva 1 byte da H:X *)
   | MODE_IX0  ⇒ mode_IX0_load true … s cur_pc
(* preleva 1 byte da H:X+1 byte offset *)
   | MODE_IX1  ⇒ mode_IX1_load true … s cur_pc
(* preleva 1 byte da H:X+1 word offset *)
   | MODE_IX2  ⇒ mode_IX2_load true … s cur_pc
(* preleva 1 byte da SP+1 byte offset *)
   | MODE_SP1  ⇒ mode_SP1_load true … s cur_pc
(* preleva 1 byte da SP+1 word offset *)
   | MODE_SP2  ⇒ mode_SP2_load true … s cur_pc

(* come DIR1, chiamare scrittura per passo2: scrittura su DIR1 *)
   | MODE_DIR1_to_DIR1 ⇒ mode_DIR1_load true … s cur_pc
(* come IMM1, chiamare scrittura per passo2: scrittura su DIR1 *)
   | MODE_IMM1_to_DIR1 ⇒ mode_IMM1_load … s cur_pc
(* come IX0, chiamare scrittura per passo2: scrittura su DIR1 e X++ *)
   | MODE_IX0p_to_DIR1 ⇒ mode_IX0_load true … s cur_pc
(* come DIR1, chiamare scrittura per passo2: scrittura su IX0 e X++ *)
   | MODE_DIR1_to_IX0p ⇒ mode_DIR1_load true … s cur_pc

(* NO: solo lettura word/scrittura byte *)
   | MODE_INHA_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *)     
   | MODE_INHX_and_IMM1 ⇒ None ?
(* NO: solo lettura word *) 
   | MODE_IMM1_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *) 
   | MODE_DIR1_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *) 
   | MODE_IX0_and_IMM1  ⇒ None ?
(* NO: solo lettura word *) 
   | MODE_IX0p_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *) 
   | MODE_IX1_and_IMM1  ⇒ None ?
(* NO: solo lettura word *) 
   | MODE_IX1p_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *) 
   | MODE_SP1_and_IMM1  ⇒ None ?

(* NO: solo scrittura byte *)
   | MODE_DIRn _          ⇒ None ?
(* NO: solo lettura word *)
   | MODE_DIRn_and_IMM1 _ ⇒ None ?
(* preleva 1 byte da 0000 0000 0000 xxxxb *)
   | MODE_TNY e           ⇒ opt_map … (memory_filter_read … s (extu2_w16 e))
                             (λb.Some ? (triple … s b cur_pc))
(* preleva 1 byte da 0000 0000 000x xxxxb *)
   | MODE_SRT t           ⇒ opt_map … (memory_filter_read … s (extu_w16 (b8_of_bit t)))
                             (λb.Some ? (triple … s b cur_pc))
   ].

ndefinition Freescale_multi_mode_load_auxw ≝
λm,t.λs:any_status m t.λcur_pc:word16.λi:Freescale_instr_mode.match i with
(* NO: non ci sono indicazioni *)
   [ MODE_INH  ⇒ None ?
(* NO: solo lettura/scrittura byte *)
   | MODE_INHA ⇒ None ?
(* NO: solo lettura/scrittura byte *)
   | MODE_INHX ⇒ None ?
(* NO: solo lettura/scrittura byte *)
   | MODE_INHH ⇒ None ?

(* preleva 1 word immediato *) 
  | MODE_INHX0ADD ⇒ opt_map … (get_IX … s)
                     (λw.Some ? (triple … s w cur_pc))
(* preleva 1 word immediato *) 
  | MODE_INHX1ADD ⇒ mode_IX1ADD_load … s cur_pc
(* preleva 1 word immediato *) 
  | MODE_INHX2ADD ⇒ mode_IX2ADD_load … s cur_pc

(* NO: solo lettura byte *)
   | MODE_IMM1 ⇒ None ?
(* preleva 1 word immediato *) 
   | MODE_IMM1EXT ⇒ mode_IMM1EXT_load … s cur_pc
(* preleva 1 word immediato *) 
   | MODE_IMM2 ⇒ mode_IMM2_load … s cur_pc
(* preleva 1 word da indirizzo diretto 1 byte *) 
   | MODE_DIR1 ⇒ mode_DIR1_load false … s cur_pc
(* preleva 1 word da indirizzo diretto 1 word *) 
   | MODE_DIR2 ⇒ mode_DIR2_load false … s cur_pc
(* preleva 1 word da H:X *)
   | MODE_IX0  ⇒ mode_IX0_load false … s cur_pc
(* preleva 1 word da H:X+1 byte offset *)
   | MODE_IX1  ⇒ mode_IX1_load false … s cur_pc
(* preleva 1 word da H:X+1 word offset *)
   | MODE_IX2  ⇒ mode_IX2_load false … s cur_pc
(* preleva 1 word da SP+1 byte offset *)
   | MODE_SP1  ⇒ mode_SP1_load false … s cur_pc
(* preleva 1 word da SP+1 word offset *)
   | MODE_SP2  ⇒ mode_SP2_load false … s cur_pc

(* NO: solo lettura/scrittura byte *)
   | MODE_DIR1_to_DIR1 ⇒ None ?
(* NO: solo lettura/scrittura byte *)
   | MODE_IMM1_to_DIR1 ⇒ None ?
(* NO: solo lettura/scrittura byte *)
   | MODE_IX0p_to_DIR1 ⇒ None ?
(* NO: solo lettura/scrittura byte *)
   | MODE_DIR1_to_IX0p ⇒ None ?

(* preleva 2 byte, possibilita' modificare Io argomento *)
   | MODE_INHA_and_IMM1 ⇒ opt_map … (mode_IMM1_load … s cur_pc)
                           (λS_immb_and_PC.match S_immb_and_PC with
                            [ triple _ immb cur_pc' ⇒
                             Some ? (triple … s 〈(get_acc_8_low_reg … s):immb〉 cur_pc')])
(* preleva 2 byte, possibilita' modificare Io argomento *)
   | MODE_INHX_and_IMM1 ⇒ opt_map … (get_indX_8_low_reg … s)
                           (λX_op.opt_map … (mode_IMM1_load … s cur_pc)
                            (λS_immb_and_PC.match S_immb_and_PC with
                             [ triple _ immb cur_pc' ⇒
                              Some ? (triple … s 〈X_op:immb〉 cur_pc')]))
(* preleva 2 byte, NO possibilita' modificare Io argomento *)               
   | MODE_IMM1_and_IMM1 ⇒ opt_map … (mode_IMM1_load … s cur_pc)
                           (λS_immb1_and_PC.match S_immb1_and_PC with
                            [ triple _ immb1 cur_pc' ⇒
                             opt_map … (mode_IMM1_load … s cur_pc')
                              (λS_immb2_and_PC.match S_immb2_and_PC with
                               [ triple _ immb2 cur_pc'' ⇒
                                Some ? (triple … s 〈immb1:immb2〉 cur_pc'')])])
(* preleva 2 byte, possibilita' modificare Io argomento *)
   | MODE_DIR1_and_IMM1 ⇒ opt_map … (mode_DIR1_load true … s cur_pc)
                           (λS_dirb_and_PC.match S_dirb_and_PC with
                            [ triple _ dirb cur_pc' ⇒
                             opt_map … (mode_IMM1_load … s cur_pc')
                              (λS_immb_and_PC.match S_immb_and_PC with
                               [ triple _ immb cur_pc'' ⇒
                                Some ? (triple … s 〈dirb:immb〉 cur_pc'')])])
(* preleva 2 byte, possibilita' modificare Io argomento *)
   | MODE_IX0_and_IMM1  ⇒ opt_map … (mode_IX0_load true … s cur_pc)
                           (λS_ixb_and_PC.match S_ixb_and_PC with
                            [ triple _ ixb cur_pc' ⇒
                             opt_map … (mode_IMM1_load … s cur_pc')
                              (λS_immb_and_PC.match S_immb_and_PC with
                               [ triple _ immb cur_pc'' ⇒
                                Some ? (triple … s 〈ixb:immb〉 cur_pc'')])])
(* preleva 2 byte, H:X++, NO possibilita' modificare Io argomento *)
   | MODE_IX0p_and_IMM1 ⇒ opt_map … (mode_IX0_load true … s cur_pc)
                           (λS_ixb_and_PC.match S_ixb_and_PC with
                            [ triple _ ixb cur_pc' ⇒
                             opt_map … (mode_IMM1_load … s cur_pc')
                              (λS_immb_and_PC.match S_immb_and_PC with
                               [ triple _ immb cur_pc'' ⇒
                                (* H:X++ *)
                                opt_map … (aux_inc_indX_16 … s)
                                 (λs'.Some ? (triple … s' 〈ixb:immb〉 cur_pc''))])])
(* preleva 2 byte, possibilita' modificare Io argomento *)
   | MODE_IX1_and_IMM1  ⇒ opt_map … (mode_IX1_load true … s cur_pc)
                           (λS_ixb_and_PC.match S_ixb_and_PC with
                            [ triple _ ixb cur_pc' ⇒
                             opt_map … (mode_IMM1_load … s cur_pc')
                              (λS_immb_and_PC.match S_immb_and_PC with
                               [ triple _ immb cur_pc'' ⇒
                                Some ? (triple … s 〈ixb:immb〉 cur_pc'')])])
(* preleva 2 byte, H:X++, NO possibilita' modificare Io argomento *)
   | MODE_IX1p_and_IMM1 ⇒ opt_map … (mode_IX1_load true … s cur_pc)
                           (λS_ixb_and_PC.match S_ixb_and_PC with
                            [ triple _ ixb cur_pc' ⇒
                             opt_map … (mode_IMM1_load … s cur_pc')
                              (λS_immb_and_PC.match S_immb_and_PC with
                               [ triple _ immb cur_pc'' ⇒
                                (* H:X++ *)
                                opt_map … (aux_inc_indX_16 … s)
                                 (λs'.Some ? (triple … s' 〈ixb:immb〉 cur_pc''))])])
(* preleva 2 byte, possibilita' modificare Io argomento *)
   | MODE_SP1_and_IMM1  ⇒ opt_map … (mode_SP1_load true … s cur_pc)
                           (λS_spb_and_PC.match S_spb_and_PC with
                            [ triple _ spb cur_pc' ⇒
                             opt_map … (mode_IMM1_load … s cur_pc')
                              (λS_immb_and_PC.match S_immb_and_PC with
                               [ triple _ immb cur_pc'' ⇒
                                Some ? (triple … s 〈spb:immb〉 cur_pc'')])])

(* NO: solo scrittura byte *)
   | MODE_DIRn _            ⇒ None ?
(* preleva 2 byte, il primo e' filtrato per azzerare tutti i bit tranne n-simo *)
   | MODE_DIRn_and_IMM1 msk ⇒ opt_map … (mode_DIR1n_load … s cur_pc msk)
                               (λS_dirbn_and_PC.match S_dirbn_and_PC with
                                [ triple _ dirbn cur_pc'   ⇒
                                 opt_map … (mode_IMM1_load … s cur_pc')
                                  (λS_immb_and_PC.match S_immb_and_PC with
                                   [ triple _ immb cur_pc'' ⇒
                                     Some ? (triple … s 〈(extu_b8 match dirbn with [ true ⇒ x1 | false ⇒ x0 ]):immb〉 cur_pc'') ])])
(* NO: solo lettura/scrittura byte *)
   | MODE_TNY _             ⇒ None ?
(* NO: solo lettura/scrittura byte *)
   | MODE_SRT _             ⇒ None ?
   ].

(* **************************************** *)
(* raccordo di tutte le possibili scritture *)
(* **************************************** *)

ndefinition Freescale_multi_mode_write_auxb ≝
λm,t.λs:any_status m t.λcur_pc:word16.λflag:aux_mod_type.λi:Freescale_instr_mode.λwriteb:byte8.match i with
(* NO: non ci sono indicazioni *)
  [ MODE_INH        ⇒ None ?
(* scrive A *)
  | MODE_INHA       ⇒ Some ? (pair … (set_acc_8_low_reg … s writeb) cur_pc)
(* scrive X *)
  | MODE_INHX       ⇒ opt_map … (set_indX_8_low_reg … s writeb)
                      (λtmps.Some ? (pair … tmps cur_pc)) 
(* scrive H *)
  | MODE_INHH       ⇒ opt_map … (set_indX_8_high_reg … s writeb)
                       (λtmps.Some ? (pair … tmps cur_pc)) 

(* NO: solo lettura word *)
  | MODE_INHX0ADD ⇒ None ?
(* NO: solo lettura word *)
  | MODE_INHX1ADD ⇒ None ?
(* NO: solo lettura word *)
  | MODE_INHX2ADD ⇒ None ?

(* NO: solo lettura byte *)
  | MODE_IMM1       ⇒ None ?
(* NO: solo lettura word *)
  | MODE_IMM1EXT    ⇒ None ?
(* NO: solo lettura word *)
  | MODE_IMM2       ⇒ None ?
(* scrive 1 byte su indirizzo diretto 1 byte *)
  | MODE_DIR1       ⇒ mode_DIR1_write true … s cur_pc writeb
(* scrive 1 byte su indirizzo diretto 1 word *)
  | MODE_DIR2       ⇒ mode_DIR2_write true … s cur_pc writeb
(* scrive 1 byte su H:X *)
  | MODE_IX0        ⇒ mode_IX0_write true … s cur_pc writeb
(* scrive 1 byte su H:X+1 byte offset *)
  | MODE_IX1        ⇒ mode_IX1_write true … s cur_pc writeb
(* scrive 1 byte su H:X+1 word offset *)
  | MODE_IX2        ⇒ mode_IX2_write true … s cur_pc writeb
(* scrive 1 byte su SP+1 byte offset *)
  | MODE_SP1        ⇒ mode_SP1_write true … s cur_pc writeb
(* scrive 1 byte su SP+1 word offset *)
  | MODE_SP2        ⇒ mode_SP2_write true … s cur_pc writeb

(* passo2: scrittura su DIR1, passo1: lettura da DIR1 *)
  | MODE_DIR1_to_DIR1   ⇒ mode_DIR1_write true … s cur_pc writeb
(* passo2: scrittura su DIR1, passo1: lettura da IMM1 *)
  | MODE_IMM1_to_DIR1   ⇒ mode_DIR1_write true … s cur_pc writeb
(* passo2: scrittura su DIR1 e X++, passo1: lettura da IX0 *)
  | MODE_IX0p_to_DIR1   ⇒ opt_map … (mode_DIR1_write true … s cur_pc writeb)
                           (λS_and_PC.match S_and_PC with [ pair S_op PC_op ⇒
                            (* H:X++ *)
                            opt_map … (aux_inc_indX_16 … S_op)
                             (λS_op'.Some ? (pair … S_op' PC_op))])
(* passo2: scrittura su IX0 e X++, passo1: lettura da DIR1 *)
  | MODE_DIR1_to_IX0p   ⇒ opt_map … (mode_IX0_write true … s cur_pc writeb)
                           (λS_and_PC.match S_and_PC with [ pair S_op PC_op ⇒
                            (* H:X++ *)
                            opt_map … (aux_inc_indX_16 … S_op)
                             (λS_op'.Some ? (pair … S_op' PC_op))])

(* dopo aver prelevato 2 byte la possibilita' modificare Io argomento = INHA *)
  | MODE_INHA_and_IMM1 ⇒ Some ? (pair … (set_acc_8_low_reg … s writeb) cur_pc)
(* dopo aver prelevato 2 byte la possibilita' modificare Io argomento = INHX *)  
  | MODE_INHX_and_IMM1 ⇒ opt_map … (set_indX_8_low_reg … s writeb)
                           (λtmps.Some ? (pair … tmps cur_pc)) 
(* NO: solo lettura word *) 
  | MODE_IMM1_and_IMM1 ⇒ None ?
(* dopo aver prelevato 2 byte la possibilita' modificare Io argomento = DIR1 *) 
  | MODE_DIR1_and_IMM1 ⇒ mode_DIR1_write true … s cur_pc writeb
(* dopo aver prelevato 2 byte la possibilita' modificare Io argomento = IX0 *)
  | MODE_IX0_and_IMM1  ⇒ mode_IX0_write true … s cur_pc writeb
(* NO: solo lettura word *) 
  | MODE_IX0p_and_IMM1 ⇒ None ?
(* dopo aver prelevato 2 byte la possibilita' modificare Io argomento = IX1 *)
  | MODE_IX1_and_IMM1  ⇒ mode_IX1_write true … s cur_pc writeb
(* NO: solo lettura word *) 
  | MODE_IX1p_and_IMM1 ⇒ None ?
(* dopo aver prelevato 2 byte la possibilita' modificare Io argomento = SP1 *)
  | MODE_SP1_and_IMM1  ⇒ mode_SP1_write true … s cur_pc writeb

(* scrive 1 byte, ma la scrittura avviene solo per n-simo bit = leggi/modifica bit/scrivi *)
  | MODE_DIRn msk ⇒ mode_DIR1n_write … s cur_pc msk (getn_array8T msk bool (bits_of_byte8 writeb))   
(* NO: solo lettura word *)
  | MODE_DIRn_and_IMM1 _ ⇒ None ?
(* scrive 1 byte su 0000 0000 0000 xxxxb *)
  | MODE_TNY e ⇒ opt_map … (memory_filter_write … s (extu2_w16 e) auxMode_ok writeb)
                   (λtmps.Some ? (pair … tmps cur_pc))
(* scrive 1 byte su 0000 0000 000x xxxxb *)
  | MODE_SRT e ⇒ opt_map … (memory_filter_write … s (extu_w16 (b8_of_bit e)) auxMode_ok writeb)
                      (λtmps.Some ? (pair … tmps cur_pc))
  ].

ndefinition Freescale_multi_mode_write_auxw ≝
λm,t.λs:any_status m t.λcur_pc:word16.λi:Freescale_instr_mode.λwritew:word16.match i with
(* NO: non ci sono indicazioni *)
  [ MODE_INH        ⇒ None ?
(* NO: solo lettura/scrittura byte *)
  | MODE_INHA       ⇒ None ?
(* NO: solo lettura/scrittura byte *)
  | MODE_INHX       ⇒ None ?
(* NO: solo lettura/scrittura byte *)
  | MODE_INHH       ⇒ None ?

(* NO: solo lettura word *)
  | MODE_INHX0ADD ⇒ None ?
(* NO: solo lettura word *)
  | MODE_INHX1ADD ⇒ None ?
(* NO: solo lettura word *)
  | MODE_INHX2ADD ⇒ None ?

(* NO: solo lettura byte *)
  | MODE_IMM1       ⇒ None ?
(* NO: solo lettura word *)
  | MODE_IMM1EXT    ⇒ None ?
(* NO: solo lettura word *)
  | MODE_IMM2       ⇒ None ?
(* scrive 1 word su indirizzo diretto 1 byte *) 
  | MODE_DIR1       ⇒ mode_DIR1_write false … s cur_pc writew
(* scrive 1 word su indirizzo diretto 1 word *)
  | MODE_DIR2       ⇒ mode_DIR2_write false … s cur_pc writew
(* scrive 1 word su H:X *)
  | MODE_IX0        ⇒ mode_IX0_write false … s cur_pc writew
(* scrive 1 word su H:X+1 byte offset *)
  | MODE_IX1        ⇒ mode_IX1_write false … s cur_pc writew
(* scrive 1 word su H:X+1 word offset *)
  | MODE_IX2        ⇒ mode_IX2_write false … s cur_pc writew
(* scrive 1 word su SP+1 byte offset *)
  | MODE_SP1        ⇒ mode_SP1_write false … s cur_pc writew
(* scrive 1 word su SP+1 word offset *)
  | MODE_SP2        ⇒ mode_SP2_write false … s cur_pc writew

(* NO: solo lettura/scrittura byte *)
  | MODE_DIR1_to_DIR1 ⇒ None ?
(* NO: solo lettura/scrittura byte *)
  | MODE_IMM1_to_DIR1 ⇒ None ?
(* NO: solo lettura/scrittura byte *)
  | MODE_IX0p_to_DIR1 ⇒ None ?
(* NO: solo lettura/scrittura byte *)
  | MODE_DIR1_to_IX0p ⇒ None ?

(* NO: solo lettura word/scrittura byte *)
  | MODE_INHA_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *)     
  | MODE_INHX_and_IMM1 ⇒ None ?
(* NO: solo lettura word *) 
  | MODE_IMM1_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *) 
  | MODE_DIR1_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *) 
  | MODE_IX0_and_IMM1  ⇒ None ?
(* NO: solo lettura word *) 
  | MODE_IX0p_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *)
  | MODE_IX1_and_IMM1  ⇒ None ?
(* NO: solo lettura word *) 
  | MODE_IX1p_and_IMM1 ⇒ None ?
(* NO: solo lettura word/scrittura byte *) 
  | MODE_SP1_and_IMM1  ⇒ None ?

(* NO: solo scrittura byte *)
  | MODE_DIRn _          ⇒ None ?
(* NO: solo lettura word *)
  | MODE_DIRn_and_IMM1 _ ⇒ None ?
(* NO: solo lettura/scrittura byte *)
  | MODE_TNY _           ⇒ None ?
(* NO: solo lettura/scrittura byte *)
  | MODE_SRT _           ⇒ None ?
  ].
