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

include "freescale/memory_func.ma".
include "freescale/memory_trees.ma".
include "freescale/memory_bits.ma".

(* ********************************************* *)
(* ASTRAZIONE DALL'IMPLEMENTAZIONE DELLA MEMORIA *)
(* ********************************************* *)

(* tipi di implementazione della memoria *)
inductive memory_impl : Type ???
  MEM_FUNC: memory_impl
| MEM_TREE: memory_impl
| MEM_BITS: memory_impl.

(* ausiliario per il tipo della memoria *)
definition aux_mem_type ???
??t:memory_impl.match t with
 [ MEM_FUNC ??? word16 ??? byte8
 | MEM_TREE ??? Prod16T (Prod16T (Prod16T (Prod16T byte8)))
 | MEM_BITS ??? Prod16T (Prod16T (Prod16T (Prod16T (Prod8T bool))))
 ].

(* ausiliario per il tipo del checker *)
definition aux_chk_type ???
??t:memory_impl.match t with
 [ MEM_FUNC ??? word16 ??? memory_type
 | MEM_TREE ??? Prod16T (Prod16T (Prod16T (Prod16T memory_type)))
 | MEM_BITS ??? Prod16T (Prod16T (Prod16T (Prod16T (Prod8T memory_type))))
 ].

(* unificazione di out_of_bound_memory *)
definition out_of_bound_memory ???
??t:memory_impl.
 match t
  return ??t.aux_chk_type t
 with
  [ MEM_FUNC ??? mf_out_of_bound_memory
  | MEM_TREE ??? mt_out_of_bound_memory
  | MEM_BITS ??? mb_out_of_bound_memory
  ].

(* unificazione di zero_memory *)
definition zero_memory ???
??t:memory_impl.
 match t
  return ??t.aux_mem_type t
 with
  [ MEM_FUNC ??? mf_zero_memory
  | MEM_TREE ??? mt_zero_memory
  | MEM_BITS ??? mb_zero_memory
  ].

(* unificazione della lettura senza chk: mem_read_abs mem addr *)
definition mem_read_abs ???
??t:memory_impl.
 match t
  return ??t.aux_mem_type t ??? word16 ??? byte8 
 with
  [ MEM_FUNC ??? ??m:aux_mem_type MEM_FUNC.
               ??addr:word16.
               m addr
  | MEM_TREE ??? ??m:aux_mem_type MEM_TREE.
               ??addr:word16.
               mt_visit byte8 m addr
  | MEM_BITS ??? ??m:aux_mem_type MEM_BITS.
               ??addr:word16.
               byte8_of_bits (mt_visit (Prod8T bool) m addr)
  ].

(* unificazione del chk *)
definition chk_get ???
??t:memory_impl.??c:aux_chk_type t.??addr:word16.
 match t
  return ??t.aux_chk_type t ??? word16 ??? Prod8T memory_type
 with
  [ MEM_FUNC ??? mf_chk_get
  | MEM_TREE ??? mt_chk_get
  | MEM_BITS ??? mb_chk_get
  ] c addr.

(* unificazione della lettura con chk: mem_read mem chk addr *)
definition mem_read ???
??t:memory_impl.??m:aux_mem_type t.??c:aux_chk_type t.??addr:word16.
 match t
  return ??t.aux_mem_type t ??? aux_chk_type t ??? word16 ??? option byte8 
 with
  [ MEM_FUNC ??? mf_mem_read
  | MEM_TREE ??? mt_mem_read
  | MEM_BITS ??? mb_mem_read
  ] m c addr.

(* unificazione della lettura di bit con chk: mem_read mem chk addr sub *)
definition mem_read_bit ???
??t:memory_impl.
 match t
  return ??t.aux_mem_type t ??? aux_chk_type t ??? word16 ??? oct ??? option bool 
 with
  [ MEM_FUNC ??? ??m:aux_mem_type MEM_FUNC.
               ??c:aux_chk_type MEM_FUNC.
               ??addr:word16.
               ??o:oct.
               opt_map ?? (mf_mem_read m c addr)
                (??b.Some ? (getn_array8T o bool (bits_of_byte8 b))) 
  | MEM_TREE ??? ??m:aux_mem_type MEM_TREE.
               ??c:aux_chk_type MEM_TREE.
               ??addr:word16.
               ??o:oct.
               opt_map ?? (mt_mem_read m c addr)
                (??b.Some ? (getn_array8T o bool (bits_of_byte8 b)))
  | MEM_BITS ??? ??m:aux_mem_type MEM_BITS.
               ??c:aux_chk_type MEM_BITS.
               ??addr:word16.
               ??o:oct.
               mb_mem_read_bit m c addr o
  ].

(* unificazione della scrittura con chk: mem_update mem chk addr val *)
definition mem_update ???
??t:memory_impl.??m:aux_mem_type t.??c:aux_chk_type t.??addr:word16.??v:byte8.
 match t
  return ??t.aux_mem_type t ??? Prod8T memory_type ??? word16 ??? byte8 ??? option (aux_mem_type t)
 with
  [ MEM_FUNC ??? mf_mem_update
  | MEM_TREE ??? mt_mem_update
  | MEM_BITS ??? mb_mem_update
  ] m (chk_get t c addr) addr v.

(* unificazione della scrittura di bit con chk: mem_update mem chk addr sub val *)
definition mem_update_bit ???
??t:memory_impl.
 match t
  return ??t.aux_mem_type t ??? aux_chk_type t ??? word16 ??? oct ??? bool ??? option (aux_mem_type t) 
 with
  [ MEM_FUNC ??? ??m:aux_mem_type MEM_FUNC.
               ??c:aux_chk_type MEM_FUNC.
               ??addr:word16.
               ??o:oct.
               ??v:bool.
               opt_map ?? (mf_mem_read m c addr)
                (??b.mf_mem_update m (chk_get MEM_FUNC c addr) addr (byte8_of_bits (setn_array8T o bool (bits_of_byte8 b) v)))
  | MEM_TREE ??? ??m:aux_mem_type MEM_TREE.
               ??c:aux_chk_type MEM_TREE.
               ??addr:word16.
               ??o:oct.
               ??v:bool.
               opt_map ?? (mt_mem_read m c addr)
                (??b.mt_mem_update m (chk_get MEM_TREE c addr) addr (byte8_of_bits (setn_array8T o bool (bits_of_byte8 b) v)))
  | MEM_BITS ??? ??m:aux_mem_type MEM_BITS.
               ??c:aux_chk_type MEM_BITS.
               ??addr:word16.
               ??o:oct.
               ??v:bool.
               mb_mem_update_bit m c addr o v
  ].

(* unificazione del caricamento: load_from_source_at old_mem source addr *)
definition load_from_source_at ???
??t:memory_impl.??m:aux_mem_type t.??l:list byte8.??addr:word16.
 match t
  return ??t.aux_mem_type t ??? list byte8 ??? word16 ??? aux_mem_type t 
 with
  [ MEM_FUNC ??? mf_load_from_source_at
  | MEM_TREE ??? mt_load_from_source_at
  | MEM_BITS ??? mb_load_from_source_at
  ] m l addr.

(* unificazione dell'impostazione della memoria: chk_update_ranged chk inf sup v *)
definition check_update_ranged ???
??t:memory_impl.
 match t
  return ??t.aux_chk_type t ??? word16 ??? word16 ??? memory_type ??? aux_chk_type t 
 with
  [ MEM_FUNC ??? ??c:aux_chk_type MEM_FUNC.
               ??inf,sup:word16.
               ??v:memory_type.
               mf_check_update_ranged c inf sup v
  | MEM_TREE ??? ??c:aux_chk_type MEM_TREE.
               ??inf,sup:word16.
               ??v:memory_type.
               mt_update_ranged memory_type c inf sup v
  | MEM_BITS ??? ??c:aux_chk_type MEM_BITS.
               ??inf,sup:word16.
               ??v:memory_type.
               mt_update_ranged (Prod8T memory_type) c inf sup (array_8T memory_type v v v v v v v v)
  ].

(* unificazione dell'impostazione dei bit: chk_update_bit chk addr sub v *)
(* NB: dove non esiste la granularita' del bit, lascio inalterato *)
definition check_update_bit ???
??t:memory_impl.
 match t
  return ??t.aux_chk_type t ??? word16 ??? oct ??? memory_type ??? aux_chk_type t
 with
  [ MEM_FUNC ??? ??c:aux_chk_type MEM_FUNC.
               ??addr:word16.
               ??o:oct.
               ??v:memory_type.
               c
  | MEM_TREE ??? ??c:aux_chk_type MEM_TREE.
               ??addr:word16.
               ??o:oct.
               ??v:memory_type.
               c
  | MEM_BITS ??? ??c:aux_chk_type MEM_BITS.
               ??addr:word16.
               ??o:oct.
               ??v:memory_type.
               mb_chk_update_bit c addr o v
  ].
