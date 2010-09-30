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

include "emulator/status/status_setter.ma".

(* **** *)
(* READ *)
(* **** *)

(* NB: fare molta attenzione alle note sulle combinazioni possibili perche'
       il comportamento della memoria nell'RS08 e' strano e ci sono
       precise condizioni che impediscono una semantica circolare dell'accesso
       (divergenza=assenza di definizione) *)
ndefinition RS08_memory_filter_read_aux ≝
λt:memory_impl.λs:any_status RS08 t.λaddr:word16.
λT:Type.λfREG:byte8 → option T.λfMEM:word16 → option T.
(* possibili accessi al registro X
   1) addr=000F: diretto
   2) addr=000E (X =0F): indiretto
   3) addr=00CF (PS=00): paging  
   [NB] altre combinazioni non funzionano perche' la MCU non e' un oggetto reattivo:
   non si possono combinare due effetti contemporaneamente!
   per esempio accesso addr=00CE (PS=00,X=0F) non puo' produrre 2 indirezioni *) 
 match (eqc ? addr 〈〈x0,x0〉:〈x0,xF〉〉) ⊕
       (eqc ? addr 〈〈x0,x0〉:〈x0,xE〉〉 ⊗ eqc ? (x_map_RS08 (alu … s)) 〈x0,xF〉) ⊕
       (eqc ? addr 〈〈x0,x0〉:〈xC,xF〉〉 ⊗ eqc ? (ps_map_RS08 (alu … s)) 〈x0,x0〉) with
  [ true ⇒ fREG (x_map_RS08 (alu … s))
  | false ⇒
(* possibili accessi al registro PS
   1) addr=001F: diretto
   2) addr=000E (X =1F): indiretto
   3) addr=00DF (PS=00): paging *)
 match (eqc ? addr 〈〈x0,x0〉:〈x1,xF〉〉) ⊕
       (eqc ? addr 〈〈x0,x0〉:〈x0,xE〉〉 ⊗ eqc ? (x_map_RS08 (alu … s)) 〈x1,xF〉) ⊕
       (eqc ? addr 〈〈x0,x0〉:〈xD,xF〉〉 ⊗ eqc ? (ps_map_RS08 (alu … s)) 〈x0,x0〉) with
  [ true ⇒ fREG (ps_map_RS08 (alu … s))
  | false ⇒
(* accesso a D[X]: se accede a [00C0-00FF] e' la RAM fisica, non il paging 
   altrimenti sarebbero 2 indirezioni *)
 match eqc ? addr 〈〈x0,x0〉:〈x0,xE〉〉 with
  [ true ⇒ fMEM (extu_w16 (x_map_RS08 (alu … s)))
  | false ⇒ 
(* accesso al paging: [00pp pppp ppxx xxxx] con p=PS x=addr *)
 match inrangec ? addr 〈〈x0,x0〉:〈xC,x0〉〉 〈〈x0,x0〉:〈xF,xF〉〉 with
  [ true ⇒ fMEM (orc ? (rorc ? (rorc ? 〈(ps_map_RS08 (alu … s)):〈x0,x0〉〉))
                       (andc ? addr 〈〈x0,x0〉:〈x3,xF〉〉))
(* accesso normale *)
  | false ⇒ fMEM addr ]]]].

(* lettura RS08 di un byte *)
ndefinition RS08_memory_filter_read ≝
λt:memory_impl.λs:any_status RS08 t.λaddr:word16.
 RS08_memory_filter_read_aux t s addr byte8
  (λb.Some byte8 b)
  (mem_read t (mem_desc … s) (chk_desc … s) o0).

(* lettura RS08 di un bit *)
ndefinition RS08_memory_filter_read_bit ≝
λt:memory_impl.λs:any_status RS08 t.λaddr:word16.λsub:oct.
 RS08_memory_filter_read_aux t s addr bool
  (λb.Some bool (getn_array8T sub bool (bits_of_byte8 b)))
  (λa.mem_read_bit t (mem_desc … s) (chk_desc … s) o0 a sub).

(* ***** *)
(* WRITE *)
(* ***** *)

ndefinition RS08_memory_filter_write_aux ≝
λt:memory_impl.λs:any_status RS08 t.λaddr:word16.
λfREG:byte8 → byte8.λfMEM:word16 → option (aux_mem_type t).
(* possibili accessi al registro X
   1) addr=000F: diretto
   2) addr=000E (X =0F): indiretto
   3) addr=00CF (PS=00): paging  
   [NB] altre combinazioni non funzionano perche' la MCU non e' un oggetto reattivo:
   non si possono combinare due effetti contemporaneamente!
   per esempio accesso addr=00CE (PS=00,X=0F) non puo' produrre 2 indirezioni *) 
 match (eqc ? addr 〈〈x0,x0〉:〈x0,xF〉〉) ⊕
       (eqc ? addr 〈〈x0,x0〉:〈x0,xE〉〉 ⊗ eqc ? (x_map_RS08 (alu … s)) 〈x0,xF〉) ⊕
       (eqc ? addr 〈〈x0,x0〉:〈xC,xF〉〉 ⊗ eqc ? (ps_map_RS08 (alu … s)) 〈x0,x0〉) with
  [ true ⇒ set_x_map … s (fREG (x_map_RS08 (alu … s)))
  | false ⇒
(* possibili accessi al registro PS
   1) addr=001F: diretto
   2) addr=000E (X =1F): indiretto
   3) addr=00DF (PS=00): paging *)
 match (eqc ? addr 〈〈x0,x0〉:〈x1,xF〉〉) ⊕
       (eqc ? addr 〈〈x0,x0〉:〈x0,xE〉〉 ⊗ eqc ? (x_map_RS08 (alu … s)) 〈x1,xF〉) ⊕
       (eqc ? addr 〈〈x0,x0〉:〈xD,xF〉〉 ⊗ eqc ? (ps_map_RS08 (alu … s)) 〈x0,x0〉) with
  [ true ⇒ set_ps_map … s (fREG (x_map_RS08 (alu … s)))
  | false ⇒
(* accesso a D[X]: se accede a [00C0-00FF] e' la RAM fisica, non il paging 
   altrimenti sarebbero 2 indirezioni *)
 match eqc ? addr 〈〈x0,x0〉:〈x0,xE〉〉 with
  [ true ⇒ opt_map … (fMEM (extu_w16 (x_map_RS08 (alu … s))))
            (λmem'.Some ? (set_mem_desc … s mem'))
  | false ⇒
(* accesso al paging: [00pp pppp ppxx xxxx] con p=PS x=addr *)
 match inrangec ? addr 〈〈x0,x0〉:〈xC,x0〉〉 〈〈x0,x0〉:〈xF,xF〉〉 with
  [ true ⇒ opt_map … (fMEM (orc ? (rorc ? (rorc ? 〈(ps_map_RS08 (alu … s)):〈x0,x0〉〉))
                                  (andc ? addr 〈〈x0,x0〉:〈x3,xF〉〉)))
            (λmem'.Some ? (set_mem_desc … s mem'))
(* accesso normale *)
  | false ⇒ opt_map … (fMEM addr)
             (λmem'.Some ? (set_mem_desc … s mem')) ]]]].

(* scrittura RS08 di un byte *)
ndefinition RS08_memory_filter_write ≝
λt:memory_impl.λs:any_status RS08 t.λaddr:word16.λval:byte8.
 RS08_memory_filter_write_aux t s addr
  (λb.val)
  (λa.mem_update t (mem_desc … s) (chk_desc … s) o0 a val).

(* scrittura RS08 di un bit *)
ndefinition RS08_memory_filter_write_bit ≝
λt:memory_impl.λs:any_status RS08 t.λaddr:word16.λsub:oct.λval:bool.
 RS08_memory_filter_write_aux t s addr
  (λb.byte8_of_bits (setn_array8T sub bool (bits_of_byte8 b) val))
  (λa.mem_update_bit t (mem_desc … s) (chk_desc … s) o0 a sub val).
