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

include "freescale/memory_trees.ma".

(* ********************* *)
(* MEMORIA E DESCRITTORE *)
(* ********************* *)

(* tutta la memoria non installata *)
definition mb_out_of_bound_memory ≝
let base ≝ array_8T memory_type MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND
                                MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND in
let lev4 ≝ array_16T ? 
           base base base base base base base base
           base base base base base base base base
           in
let lev3 ≝ array_16T ?
           lev4 lev4 lev4 lev4 lev4 lev4 lev4 lev4
           lev4 lev4 lev4 lev4 lev4 lev4 lev4 lev4
           in
let lev2 ≝ array_16T ?
           lev3 lev3 lev3 lev3 lev3 lev3 lev3 lev3
           lev3 lev3 lev3 lev3 lev3 lev3 lev3 lev3
           in
let lev1 ≝ array_16T ?
           lev2 lev2 lev2 lev2 lev2 lev2 lev2 lev2
           lev2 lev2 lev2 lev2 lev2 lev2 lev2 lev2
           in
lev1.

(* tutta la memoria a 0 *)
definition mb_zero_memory ≝
let base ≝ array_8T bool false false false false false false false false in
let lev4 ≝ array_16T ? 
           base base base base base base base base
           base base base base base base base base
           in
let lev3 ≝ array_16T ?
           lev4 lev4 lev4 lev4 lev4 lev4 lev4 lev4
           lev4 lev4 lev4 lev4 lev4 lev4 lev4 lev4
           in
let lev2 ≝ array_16T ?
           lev3 lev3 lev3 lev3 lev3 lev3 lev3 lev3
           lev3 lev3 lev3 lev3 lev3 lev3 lev3 lev3
           in
let lev1 ≝ array_16T ?
           lev2 lev2 lev2 lev2 lev2 lev2 lev2 lev2
           lev2 lev2 lev2 lev2 lev2 lev2 lev2 lev2
           in
lev1.

(* scrivi bit controllando il tipo di memoria *)
definition mb_mem_update_bit ≝
λmem:Prod16T (Prod16T (Prod16T (Prod16T (Prod8T bool)))).
λchk:Prod16T (Prod16T (Prod16T (Prod16T (Prod8T memory_type)))).
λaddr:word16.λsub:oct.λv:bool.
 match getn_array8T sub memory_type (mt_visit (Prod8T memory_type) chk addr) with
  (* ROM? ok, ma il valore viene perso *)
  [ MEM_READ_ONLY ⇒ Some ? mem
  (* RAM? ok *)
  | MEM_READ_WRITE ⇒ Some ? (mt_update (Prod8T bool) mem addr (setn_array8T sub bool (mt_visit (Prod8T bool) mem addr) v))
  (* NON INSTALLATA? no *)
  | MEM_OUT_OF_BOUND ⇒ None ? ].

(* scrivi tipo di bit *)
definition mb_chk_update_bit ≝
λchk:Prod16T (Prod16T (Prod16T (Prod16T (Prod8T memory_type)))).
λaddr:word16.λsub:oct.λv:memory_type.
 mt_update (Prod8T memory_type) chk addr (setn_array8T sub memory_type (mt_visit (Prod8T memory_type) chk addr) v).

(* leggi bit controllando il tipo di memoria *)
definition mb_mem_read_bit ≝
λmem:Prod16T (Prod16T (Prod16T (Prod16T (Prod8T bool)))).
λchk:Prod16T (Prod16T (Prod16T (Prod16T (Prod8T memory_type)))).
λaddr:word16.λsub:oct.
 match getn_array8T sub memory_type (mt_visit (Prod8T memory_type) chk addr) with
  (* ROM? ok, ma il valore viene perso *)
  [ MEM_READ_ONLY ⇒ Some ? (getn_array8T sub bool (mt_visit (Prod8T bool) mem addr))
  (* RAM? ok *)
  | MEM_READ_WRITE ⇒ Some ? (getn_array8T sub bool (mt_visit (Prod8T bool) mem addr))
  (* NON INSTALLATA? no *)
  | MEM_OUT_OF_BOUND ⇒ None ? ]. 

definition mb_chk_get ≝
λchk:Prod16T (Prod16T (Prod16T (Prod16T (Prod8T memory_type)))).λaddr:word16.
let c ≝ mt_visit (Prod8T memory_type) chk addr in
array_8T ? (getn_array8T o7 ? c) (getn_array8T o6 ? c)
           (getn_array8T o5 ? c) (getn_array8T o4 ? c)
           (getn_array8T o3 ? c) (getn_array8T o2 ? c)
           (getn_array8T o1 ? c) (getn_array8T o0 ? c).

(* scrivi controllando il tipo di memoria *)
(* NB: devono esistere tutti i bit *)
definition mb_mem_update ≝
λmem:Prod16T (Prod16T (Prod16T (Prod16T (Prod8T bool)))).
λchk:Prod8T memory_type.
λaddr:word16.λv:byte8.
let old_value ≝ mt_visit (Prod8T bool) mem addr in
let new_value ≝ bits_of_byte8 v in
let newbit0 ≝ match getn_array8T o0 memory_type chk with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o0 bool old_value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o0 bool new_value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit1 ≝ match getn_array8T o1 memory_type chk with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o1 bool old_value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o1 bool new_value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit2 ≝ match getn_array8T o2 memory_type chk with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o2 bool old_value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o2 bool new_value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit3 ≝ match getn_array8T o3 memory_type chk with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o3 bool old_value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o3 bool new_value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit4 ≝ match getn_array8T o4 memory_type chk with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o4 bool old_value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o4 bool new_value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit5 ≝ match getn_array8T o5 memory_type chk with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o5 bool old_value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o5 bool new_value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit6 ≝ match getn_array8T o6 memory_type chk with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o6 bool old_value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o6 bool new_value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit7 ≝ match getn_array8T o7 memory_type chk with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o7 bool old_value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o7 bool new_value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
       opt_map ?? newbit0
 (λnb0.opt_map ?? newbit1
 (λnb1.opt_map ?? newbit2
 (λnb2.opt_map ?? newbit3
 (λnb3.opt_map ?? newbit4
 (λnb4.opt_map ?? newbit5
 (λnb5.opt_map ?? newbit6
 (λnb6.opt_map ?? newbit7
 (λnb7.Some ? (mt_update (Prod8T bool) mem addr (array_8T bool nb7 nb6 nb5 nb4 nb3 nb2 nb1 nb0)))))))))).

(* leggi controllando il tipo di memoria *)
(* NB: devono esistere tutti i bit *)
definition mb_mem_read ≝
λmem:Prod16T (Prod16T (Prod16T (Prod16T (Prod8T bool)))).
λchk:Prod16T (Prod16T (Prod16T (Prod16T (Prod8T memory_type)))).
λaddr:word16.
let bit_types ≝ mt_visit (Prod8T memory_type) chk addr in
let value ≝ mt_visit (Prod8T bool) mem addr in
let newbit0 ≝ match getn_array8T o0 memory_type bit_types with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o0 bool value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o0 bool value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit1 ≝ match getn_array8T o1 memory_type bit_types with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o1 bool value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o1 bool value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit2 ≝ match getn_array8T o2 memory_type bit_types with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o2 bool value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o2 bool value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit3 ≝ match getn_array8T o3 memory_type bit_types with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o3 bool value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o3 bool value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit4 ≝ match getn_array8T o4 memory_type bit_types with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o4 bool value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o4 bool value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit5 ≝ match getn_array8T o5 memory_type bit_types with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o5 bool value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o5 bool value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit6 ≝ match getn_array8T o6 memory_type bit_types with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o6 bool value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o6 bool value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
let newbit7 ≝ match getn_array8T o7 memory_type bit_types with
 [ MEM_READ_ONLY ⇒ Some bool (getn_array8T o7 bool value)
 | MEM_READ_WRITE ⇒ Some bool (getn_array8T o7 bool value)
 | MEM_OUT_OF_BOUND ⇒ None bool ] in
       opt_map ?? newbit0
 (λnb0.opt_map ?? newbit1
 (λnb1.opt_map ?? newbit2
 (λnb2.opt_map ?? newbit3
 (λnb3.opt_map ?? newbit4
 (λnb4.opt_map ?? newbit5
 (λnb5.opt_map ?? newbit6
 (λnb6.opt_map ?? newbit7
 (λnb7.Some ? (byte8_of_bits (array_8T bool nb7 nb6 nb5 nb4 nb3 nb2 nb1 nb0)))))))))).

(* ************************** *)
(* CARICAMENTO PROGRAMMA/DATI *)
(* ************************** *)

(* carica a paratire da addr, scartando source (pescando da old_mem) se si supera 0xFFFF... *)
let rec mb_load_from_source_at (old_mem:Prod16T (Prod16T (Prod16T (Prod16T (Prod8T bool)))))
                               (source:list byte8) (addr:word16) on source ≝
match source with
 (* fine di source: carica da old_mem *)
 [ nil ⇒ old_mem
 | cons hd tl ⇒ match lt_w16 addr 〈〈xF,xF〉:〈xF,xF〉〉 with
  (* non supera 0xFFFF, ricorsione *)
  [ true ⇒ mb_load_from_source_at (mt_update ? old_mem addr (bits_of_byte8 hd)) tl (plus_w16nc addr 〈〈x0,x0〉:〈x0,x1〉〉)
  (* supera 0xFFFF, niente ricorsione *)
  | false ⇒ mt_update ? old_mem addr (bits_of_byte8 hd)
  ]].
