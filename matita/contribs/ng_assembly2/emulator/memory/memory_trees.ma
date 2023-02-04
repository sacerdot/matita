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

include "emulator/memory/memory_base.ma".
include "emulator/memory/memory_struct.ma".
include "num/word32.ma".
include "common/list.ma".

(* ************************** *)
(* 8 segmenti da 64Kb → 512Kb *)
(* 4 + 16 bit indirizzo       *)
(* ************************** *)

(* ********************* *)
(* MEMORIA E DESCRITTORE *)
(* ********************* *)

ndefinition aux_20B_filler ≝
λT:Type.λel:T.
let lev4 ≝ mk_Array16T T el el el el el el el el el el el el el el el el in
let lev3 ≝ mk_Array16T ?
           lev4 lev4 lev4 lev4 lev4 lev4 lev4 lev4
           lev4 lev4 lev4 lev4 lev4 lev4 lev4 lev4 in
let lev2 ≝ mk_Array16T ?
           lev3 lev3 lev3 lev3 lev3 lev3 lev3 lev3
           lev3 lev3 lev3 lev3 lev3 lev3 lev3 lev3 in
let lev1 ≝ mk_Array16T ?
           lev2 lev2 lev2 lev2 lev2 lev2 lev2 lev2
           lev2 lev2 lev2 lev2 lev2 lev2 lev2 lev2 in
let lev0 ≝ mk_Array8T ?
           lev1 lev1 lev1 lev1 lev1 lev1 lev1 lev1
           in
lev0.

ndefinition aux_20B_type ≝
λT:Type.Array8T (Array16T (Array16T (Array16T (Array16T T)))).

(* tutta la memoria non installata *)
ndefinition mt_out_of_bound_memory ≝ aux_20B_filler ? MEM_OUT_OF_BOUND.

(* tutta la memoria a 0 *)
ndefinition mt_zero_memory ≝ aux_20B_filler ? 〈x0,x0〉.

(* visita di un albero da 512Kb di elementi: ln16(512Kb)=5 passaggi *)
ndefinition mt_visit ≝
λT:Type.λdata:aux_20B_type T.λsel:oct.λaddr:word16.
 getn_array16T (cnL ? (cnL ? addr)) ?
  (getn_array16T (cnH ? (cnL ? addr)) ?
   (getn_array16T (cnL ? (cnH ? addr)) ?
    (getn_array16T (cnH ? (cnH ? addr)) ?
     (getn_array8T sel ? data)))).

(* scrittura di un elemento in un albero da 512Kb *)
ndefinition mt_update ≝
λT:Type.λdata:aux_20B_type T.λsel:oct.λaddr:word16.λv:T.
 let lev1 ≝ getn_array8T sel ? data in
 let lev2 ≝ getn_array16T (cnH ? (cnH ? addr)) ? lev1 in
 let lev3 ≝ getn_array16T (cnL ? (cnH ? addr)) ? lev2 in
 let lev4 ≝ getn_array16T (cnH ? (cnL ? addr)) ? lev3 in
 setn_array8T sel ? data
  (setn_array16T (cnH ? (cnH ? addr)) ? lev1
   (setn_array16T (cnL ? (cnH ? addr)) ? lev2
    (setn_array16T (cnH ? (cnL ? addr)) ? lev3
     (setn_array16T (cnL ? (cnL ? addr)) T lev4 v)))).

(* scrittura di un segmento (max 64Kb) degli otto disponibili *)
nlet rec mt_update_ranged (T:Type) (data:aux_20B_type T) (sel:oct) (addr:word16) (w:word16) (rw:rec_word16 w) (v:T) on rw ≝
 match rw with
  [ w16_O ⇒ data
  | w16_S w' rw' ⇒ mt_update_ranged T (mt_update T data sel addr v)
                                      sel (succc ? addr) w' rw' v
  ].

(* scrivi controllando il tipo di memoria *)
ndefinition mt_mem_update ≝
λmem:aux_20B_type byte8.
λchk:aux_20B_type memory_type.
λsel:oct.λaddr:word16.λv:byte8.
 match mt_visit ? chk sel addr with
  (* ROM? ok, ma il valore viene perso *)
  [ MEM_READ_ONLY ⇒ Some ? mem
  (* RAM? ok *)
  | MEM_READ_WRITE ⇒ Some ? (mt_update ? mem sel addr v)
  (* NON INSTALLATA? no *)
  | MEM_OUT_OF_BOUND ⇒ None ? ].  

(* leggi controllando il tipo di memoria *)
ndefinition mt_mem_read ≝
λmem:aux_20B_type byte8.
λchk:aux_20B_type memory_type.
λsel:oct.λaddr:word16.
 match mt_visit ? chk sel addr with
  [ MEM_READ_ONLY ⇒ Some ? (mt_visit ? mem sel addr)
  | MEM_READ_WRITE ⇒ Some ? (mt_visit ? mem sel addr)
  | MEM_OUT_OF_BOUND ⇒ None ? ].

(* ************************** *)
(* CARICAMENTO PROGRAMMA/DATI *)
(* ************************** *)

(* carica a paratire da addr, overflow se si supera 0xFFFF... *)
nlet rec mt_load_from_source_at (old_mem:aux_20B_type byte8)
                                (src:list byte8) (sel:oct) (addr:word16) on src ≝
 match src with
  (* fine di source: carica da old_mem *)
  [ nil ⇒ old_mem
  | cons hd tl ⇒ mt_load_from_source_at (mt_update ? old_mem sel addr hd)
                                        tl sel (succc ? addr)
  ].
