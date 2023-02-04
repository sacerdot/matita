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

include "emulator/memory/memory_trees.ma".

(* ********************* *)
(* MEMORIA E DESCRITTORE *)
(* ********************* *)

(* tutta la memoria non installata *)
ndefinition mb_out_of_bound_memory ≝
 aux_20B_filler ?
  (mk_Array8T ? MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND
                MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND).

(* tutta la memoria a 0 *)
ndefinition mb_zero_memory ≝
 aux_20B_filler ? (mk_Array8T ? false false false false false false false false).

(* scrivi bit controllando il tipo di memoria *)
ndefinition mb_mem_update_bit ≝
λmem:aux_20B_type (Array8T bool).
λchk:aux_20B_type (Array8T memory_type).
λsel:oct.λaddr:word16.λsub:oct.λv:bool.
 match getn_array8T sub ? (mt_visit ? chk sel addr) with
  (* ROM? ok, ma il valore viene perso *)
  [ MEM_READ_ONLY ⇒ Some ? mem
  (* RAM? ok *)
  | MEM_READ_WRITE ⇒ Some ? (mt_update ? mem sel addr (setn_array8T sub ? (mt_visit ? mem sel addr) v))
  (* NON INSTALLATA? no *)
  | MEM_OUT_OF_BOUND ⇒ None ? ].

ndefinition mb_mem_update ≝
λmem:aux_20B_type (Array8T bool).
λchk:aux_20B_type (Array8T memory_type).
λsel:oct.λaddr:word16.λv:byte8.
let old_value ≝ mt_visit (Array8T bool) mem sel addr in
let new_value ≝ bits_of_byte8 v in
let memtypes ≝ mt_visit (Array8T memory_type) chk sel addr in
let newbit0 ≝ match getn_array8T o0 memory_type memtypes with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o0 bool old_value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o0 bool new_value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit1 ≝ match getn_array8T o1 memory_type memtypes with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o1 bool old_value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o1 bool new_value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit2 ≝ match getn_array8T o2 memory_type memtypes with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o2 bool old_value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o2 bool new_value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit3 ≝ match getn_array8T o3 memory_type memtypes with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o3 bool old_value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o3 bool new_value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit4 ≝ match getn_array8T o4 memory_type memtypes with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o4 bool old_value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o4 bool new_value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit5 ≝ match getn_array8T o5 memory_type memtypes with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o5 bool old_value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o5 bool new_value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit6 ≝ match getn_array8T o6 memory_type memtypes with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o6 bool old_value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o6 bool new_value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit7 ≝ match getn_array8T o7 memory_type memtypes with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o7 bool old_value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o7 bool new_value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
       opt_map … newbit0
 (λnb0.opt_map … newbit1
 (λnb1.opt_map … newbit2
 (λnb2.opt_map … newbit3
 (λnb3.opt_map … newbit4
 (λnb4.opt_map … newbit5
 (λnb5.opt_map … newbit6
 (λnb6.opt_map … newbit7
 (λnb7.Some ? (mt_update ? mem sel addr (mk_Array8T bool nb7 nb6 nb5 nb4 nb3 nb2 nb1 nb0)))))))))).

(* scrivi tipo di bit *)
ndefinition mb_chk_update_bit ≝
λchk:aux_20B_type (Array8T memory_type).
λsel:oct.λaddr:word16.λsub:oct.λv:memory_type.
 mt_update ? chk sel addr (setn_array8T sub ? (mt_visit ? chk sel addr) v).

(* leggi bit controllando il tipo di memoria *)
ndefinition mb_mem_read_bit ≝
λmem:aux_20B_type (Array8T bool).
λchk:aux_20B_type (Array8T memory_type).
λsel:oct.λaddr:word16.λsub:oct.
 match getn_array8T sub ? (mt_visit ? chk sel addr) with
  (* ROM? ok, ma il valore viene perso *)
  [ MEM_READ_ONLY ⇒ Some ? (getn_array8T sub ? (mt_visit ? mem sel addr))
  (* RAM? ok *)
  | MEM_READ_WRITE ⇒ Some ? (getn_array8T sub ? (mt_visit ? mem sel addr))
  (* NON INSTALLATA? no *)
  | MEM_OUT_OF_BOUND ⇒ None ? ]. 

(* leggi controllando il tipo di memoria *)
(* NB: devono esistere tutti i bit *)
ndefinition mb_mem_read ≝
λmem:aux_20B_type (Array8T bool).
λchk:aux_20B_type (Array8T memory_type).
λsel:oct.λaddr:word16.
let value ≝ mt_visit (Array8T bool) mem sel addr in
let memtypes ≝ mt_visit (Array8T memory_type) chk sel addr in
let newbit0 ≝ match getn_array8T o0 memory_type memtypes with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o0 bool value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o0 bool value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit1 ≝ match getn_array8T o1 memory_type memtypes with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o1 bool value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o1 bool value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit2 ≝ match getn_array8T o2 memory_type memtypes with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o2 bool value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o2 bool value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit3 ≝ match getn_array8T o3 memory_type memtypes with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o3 bool value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o3 bool value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit4 ≝ match getn_array8T o4 memory_type memtypes with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o4 bool value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o4 bool value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit5 ≝ match getn_array8T o5 memory_type memtypes with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o5 bool value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o5 bool value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit6 ≝ match getn_array8T o6 memory_type memtypes with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o6 bool value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o6 bool value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit7 ≝ match getn_array8T o7 memory_type memtypes with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o7 bool value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o7 bool value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
       opt_map … newbit0
 (λnb0.opt_map … newbit1
 (λnb1.opt_map … newbit2
 (λnb2.opt_map … newbit3
 (λnb3.opt_map … newbit4
 (λnb4.opt_map … newbit5
 (λnb5.opt_map … newbit6
 (λnb6.opt_map … newbit7
 (λnb7.Some ? (byte8_of_bits (mk_Array8T bool nb7 nb6 nb5 nb4 nb3 nb2 nb1 nb0)))))))))).

(* ************************** *)
(* CARICAMENTO PROGRAMMA/DATI *)
(* ************************** *)

(* carica a paratire da addr, scartando source (pescando da old_mem) se si supera 0xFFFF... *)
nlet rec mb_load_from_source_at (old_mem:aux_20B_type (Array8T bool))
                                (src:list byte8) (sel:oct) (addr:word16) on src ≝
 match src with
  (* fine di source: carica da old_mem *)
  [ nil ⇒ old_mem
  | cons hd tl ⇒ mb_load_from_source_at (mt_update ? old_mem sel addr (bits_of_byte8 hd))
                                        tl sel (succc ? addr)
  ].
