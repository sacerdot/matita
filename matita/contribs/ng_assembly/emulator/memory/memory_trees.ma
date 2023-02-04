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

include "emulator/memory/memory_struct.ma".
include "num/word32.ma".
include "common/option.ma".
include "common/list.ma".

(* ********************* *)
(* MEMORIA E DESCRITTORE *)
(* ********************* *)

ndefinition aux_32B_filler ≝
λT:Type.λel:T.
let lev8 ≝ mk_Array16T T el el el el el el el el el el el el el el el el in
let lev7 ≝ mk_Array16T ?
           lev8 lev8 lev8 lev8 lev8 lev8 lev8 lev8
           lev8 lev8 lev8 lev8 lev8 lev8 lev8 lev8
           in
let lev6 ≝ mk_Array16T ?
           lev7 lev7 lev7 lev7 lev7 lev7 lev7 lev7
           lev7 lev7 lev7 lev7 lev7 lev7 lev7 lev7
           in
let lev5 ≝ mk_Array16T ?
           lev6 lev6 lev6 lev6 lev6 lev6 lev6 lev6
           lev6 lev6 lev6 lev6 lev6 lev6 lev6 lev6
           in
let lev4 ≝ mk_Array16T ?
           lev5 lev5 lev5 lev5 lev5 lev5 lev5 lev5
           lev5 lev5 lev5 lev5 lev5 lev5 lev5 lev5
           in
let lev3 ≝ mk_Array16T ?
           lev4 lev4 lev4 lev4 lev4 lev4 lev4 lev4
           lev4 lev4 lev4 lev4 lev4 lev4 lev4 lev4
           in
let lev2 ≝ mk_Array16T ?
           lev3 lev3 lev3 lev3 lev3 lev3 lev3 lev3
           lev3 lev3 lev3 lev3 lev3 lev3 lev3 lev3
           in
let lev1 ≝ mk_Array16T ?
           lev2 lev2 lev2 lev2 lev2 lev2 lev2 lev2
           lev2 lev2 lev2 lev2 lev2 lev2 lev2 lev2
           in
lev1.

ndefinition aux_32B_type ≝
λT:Type.Array16T (Array16T (Array16T (Array16T (Array16T (Array16T (Array16T (Array16T T))))))).

(* tutta la memoria non installata *)
ndefinition mt_out_of_bound_memory ≝ aux_32B_filler ? MEM_OUT_OF_BOUND.

(* tutta la memoria a 0 *)
ndefinition mt_zero_memory ≝ aux_32B_filler ? 〈x0,x0〉.

(* visita di un albero da 4GB di elementi: ln16(4GB)=8 passaggi *)
ndefinition mt_visit ≝
λT:Type.λdata:aux_32B_type T.λaddr:word32.
 getn_array16T (cnL ? (cnL ? (cnL ? addr))) ?
  (getn_array16T (cnH ? (cnL ? (cnL ? addr))) ?
   (getn_array16T (cnL ? (cnH ? (cnL ? addr))) ?
    (getn_array16T (cnH ? (cnH ? (cnL ? addr))) ?
     (getn_array16T (cnL ? (cnL ? (cnH ? addr))) ?
      (getn_array16T (cnH ? (cnL ? (cnH ? addr))) ?
       (getn_array16T (cnL ? (cnH ? (cnH ? addr))) ?
        (getn_array16T (cnH ? (cnH ? (cnH ? addr))) ? data))))))).

(* scrittura di un elemento in un albero da 4GB *)
ndefinition mt_update ≝
λT:Type.λdata:aux_32B_type T.λaddr:word32.λv:T.
 let lev2 ≝ getn_array16T (cnH ? (cnH ? (cnH ? addr))) ? data in
 let lev3 ≝ getn_array16T (cnL ? (cnH ? (cnH ? addr))) ? lev2 in
 let lev4 ≝ getn_array16T (cnH ? (cnL ? (cnH ? addr))) ? lev3 in
 let lev5 ≝ getn_array16T (cnL ? (cnL ? (cnH ? addr))) ? lev4 in
 let lev6 ≝ getn_array16T (cnH ? (cnH ? (cnL ? addr))) ? lev5 in
 let lev7 ≝ getn_array16T (cnL ? (cnH ? (cnL ? addr))) ? lev6 in
 let lev8 ≝ getn_array16T (cnH ? (cnL ? (cnL ? addr))) ? lev7 in

 setn_array16T (cnH ? (cnH ? (cnH ? addr))) ? data
  (setn_array16T (cnL ? (cnH ? (cnH ? addr))) ? lev2
   (setn_array16T (cnH ? (cnL ? (cnH ? addr))) ? lev3
    (setn_array16T (cnL ? (cnL ? (cnH ? addr))) ? lev4
     (setn_array16T (cnH ? (cnH ? (cnL ? addr))) ? lev5
      (setn_array16T (cnL ? (cnH ? (cnL ? addr))) ? lev6
       (setn_array16T (cnH ? (cnL ? (cnL ? addr))) ? lev7
        (setn_array16T (cnL ? (cnL ? (cnL ? addr))) T lev8 v))))))).

(* scrittura di un range (max 64KB) in un albero da 4GB *)
nlet rec mt_update_ranged (T:Type) (data:aux_32B_type T) (addr:word32) (w:word16) (rw:rec_word16 w) (v:T) on rw ≝
 match rw with
  [ w16_O ⇒ data
  | w16_S w' rw' ⇒ mt_update_ranged T (mt_update T data addr v)
                                    (succ_w32 addr) w' rw' v
  ].

(* scrivi controllando il tipo di memoria *)
ndefinition mt_mem_update ≝
λmem:aux_32B_type byte8.
λchk:aux_32B_type memory_type.
λaddr:word32.λv:byte8.
 match mt_visit ? chk addr with
  (* ROM? ok, ma il valore viene perso *)
  [ MEM_READ_ONLY ⇒ Some ? mem
  (* RAM? ok *)
  | MEM_READ_WRITE ⇒ Some ? (mt_update ? mem addr v)
  (* NON INSTALLATA? no *)
  | MEM_OUT_OF_BOUND ⇒ None ? ].  

(* leggi controllando il tipo di memoria *)
ndefinition mt_mem_read ≝
λmem:aux_32B_type byte8.
λchk:aux_32B_type memory_type.
λaddr:word32.
 match mt_visit ? chk addr with
  [ MEM_READ_ONLY ⇒ Some ? (mt_visit ? mem addr)
  | MEM_READ_WRITE ⇒ Some ? (mt_visit ? mem addr)
  | MEM_OUT_OF_BOUND ⇒ None ? ].

(* ************************** *)
(* CARICAMENTO PROGRAMMA/DATI *)
(* ************************** *)

(* carica a paratire da addr, overflow se si supera 0xFFFF... *)
nlet rec mt_load_from_source_at (old_mem:aux_32B_type byte8)
                                (src:list byte8) (addr:word32) on src ≝
 match src with
  (* fine di source: carica da old_mem *)
  [ nil ⇒ old_mem
  | cons hd tl ⇒ mt_load_from_source_at (mt_update ? old_mem addr hd) tl (succ_w32 addr)
  ].
