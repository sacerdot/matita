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

include "emulator/memory/memory_func.ma".
include "emulator/memory/memory_trees.ma".
include "emulator/memory/memory_bits.ma".

(* ********************************************* *)
(* ASTRAZIONE DALL'IMPLEMENTAZIONE DELLA MEMORIA *)
(* ********************************************* *)

(* tipi di implementazione della memoria *)
ninductive memory_impl : Type ≝
  MEM_FUNC: memory_impl
| MEM_TREE: memory_impl
| MEM_BITS: memory_impl.

(* ausiliario per il tipo della memoria *)
ndefinition aux_mem_type ≝
λt:memory_impl.match t with
 [ MEM_FUNC ⇒ word32 → byte8
 | MEM_TREE ⇒ aux_32B_type byte8
 | MEM_BITS ⇒ aux_32B_type (Array8T bool)
 ].

(* ausiliario per il tipo del checker *)
ndefinition aux_chk_type ≝
λt:memory_impl.match t with
 [ MEM_FUNC ⇒ word32 → memory_type
 | MEM_TREE ⇒ aux_32B_type memory_type
 | MEM_BITS ⇒ aux_32B_type (Array8T memory_type)
 ].

(* unificazione di out_of_bound_memory *)
ndefinition out_of_bound_memory ≝
λt:memory_impl.
 match t
  return λt.aux_chk_type t
 with
  [ MEM_FUNC ⇒ mf_out_of_bound_memory
  | MEM_TREE ⇒ mt_out_of_bound_memory
  | MEM_BITS ⇒ mb_out_of_bound_memory
  ].

(* unificazione di zero_memory *)
ndefinition zero_memory ≝
λt:memory_impl.
 match t
  return λt.aux_mem_type t
 with
  [ MEM_FUNC ⇒ mf_zero_memory
  | MEM_TREE ⇒ mt_zero_memory
  | MEM_BITS ⇒ mb_zero_memory
  ].

(* unificazione della lettura senza chk: mem_read_abs mem addr *)
ndefinition mem_read_abs ≝
λt:memory_impl.
 match t
  return λt.aux_mem_type t → word32 → byte8 
 with
  [ MEM_FUNC ⇒ λm:aux_mem_type MEM_FUNC.
               λaddr:word32.
               m addr
  | MEM_TREE ⇒ λm:aux_mem_type MEM_TREE.
               λaddr:word32.
               mt_visit ? m addr
  | MEM_BITS ⇒ λm:aux_mem_type MEM_BITS.
               λaddr:word32.
               byte8_of_bits (mt_visit ? m addr)
  ].

(* unificazione del chk *)
ndefinition chk_get ≝
λt:memory_impl.
 match t
  return λt.aux_chk_type t → word32 → Array8T memory_type
 with
  [ MEM_FUNC ⇒ λc:aux_chk_type MEM_FUNC.λaddr:word32.
   match c addr with
    [ MEM_READ_ONLY ⇒ mk_Array8T ? MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY
    | MEM_READ_WRITE ⇒ mk_Array8T ? MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE
    | MEM_OUT_OF_BOUND ⇒ mk_Array8T ? MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND
    ]
  | MEM_TREE ⇒ λc:aux_chk_type MEM_TREE.λaddr:word32.
   match mt_visit ? c addr with
    [ MEM_READ_ONLY ⇒ mk_Array8T ? MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY
    | MEM_READ_WRITE ⇒ mk_Array8T ? MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE
    | MEM_OUT_OF_BOUND ⇒ mk_Array8T ? MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND
    ]
  | MEM_BITS ⇒ λc:aux_chk_type MEM_BITS.λaddr:word32.
   mt_visit ? c addr
  ].

(* unificazione della lettura con chk: mem_read mem chk addr *)
ndefinition mem_read ≝
λt:memory_impl.λm:aux_mem_type t.λc:aux_chk_type t.λaddr:word32.
 match t
  return λt.aux_mem_type t → aux_chk_type t → word32 → option byte8 
 with
  [ MEM_FUNC ⇒ mf_mem_read
  | MEM_TREE ⇒ mt_mem_read
  | MEM_BITS ⇒ mb_mem_read
  ] m c addr.

(* unificazione della lettura di bit con chk: mem_read mem chk addr sub *)
ndefinition mem_read_bit ≝
λt:memory_impl.
 match t
  return λt.aux_mem_type t → aux_chk_type t → word32 → oct → option bool 
 with
  [ MEM_FUNC ⇒ λm:aux_mem_type MEM_FUNC.
               λc:aux_chk_type MEM_FUNC.
               λaddr:word32.
               λo:oct.
               opt_map … (mf_mem_read m c addr)
                (λb.Some ? (getn_array8T o bool (bits_of_byte8 b))) 
  | MEM_TREE ⇒ λm:aux_mem_type MEM_TREE.
               λc:aux_chk_type MEM_TREE.
               λaddr:word32.
               λo:oct.
               opt_map … (mt_mem_read m c addr)
                (λb.Some ? (getn_array8T o bool (bits_of_byte8 b)))
  | MEM_BITS ⇒ λm:aux_mem_type MEM_BITS.
               λc:aux_chk_type MEM_BITS.
               λaddr:word32.
               λo:oct.
               mb_mem_read_bit m c addr o
  ].

(* unificazione della scrittura con chk: mem_update mem chk addr val *)
ndefinition mem_update ≝
λt:memory_impl.λm:aux_mem_type t.λc:aux_chk_type t.λaddr:word32.λv:byte8.
 match t
  return λt.aux_mem_type t → aux_chk_type t → word32 → byte8 → option (aux_mem_type t)
 with
  [ MEM_FUNC ⇒ mf_mem_update
  | MEM_TREE ⇒ mt_mem_update
  | MEM_BITS ⇒ mb_mem_update
  ] m c addr v.

(* unificazione della scrittura di bit con chk: mem_update mem chk addr sub val *)
ndefinition mem_update_bit ≝
λt:memory_impl.
 match t
  return λt.aux_mem_type t → aux_chk_type t → word32 → oct → bool → option (aux_mem_type t) 
 with
  [ MEM_FUNC ⇒ λm:aux_mem_type MEM_FUNC.
               λc:aux_chk_type MEM_FUNC.
               λaddr:word32.
               λo:oct.
               λv:bool.
               mf_mem_update m c addr (byte8_of_bits (setn_array8T o bool (bits_of_byte8 (m addr)) v))
  | MEM_TREE ⇒ λm:aux_mem_type MEM_TREE.
               λc:aux_chk_type MEM_TREE.
               λaddr:word32.
               λo:oct.
               λv:bool.
               mt_mem_update m c addr (byte8_of_bits (setn_array8T o bool (bits_of_byte8 (mt_visit ? m addr)) v))
  | MEM_BITS ⇒ λm:aux_mem_type MEM_BITS.
               λc:aux_chk_type MEM_BITS.
               λaddr:word32.
               λo:oct.
               λv:bool.
               mb_mem_update_bit m c addr o v
  ].

(* unificazione del caricamento: load_from_source_at old_mem source addr *)
ndefinition load_from_source_at ≝
λt:memory_impl.λm:aux_mem_type t.λl:list byte8.λaddr:word32.
 match t
  return λt.aux_mem_type t → list byte8 → word32 → aux_mem_type t 
 with
  [ MEM_FUNC ⇒ mf_load_from_source_at
  | MEM_TREE ⇒ mt_load_from_source_at
  | MEM_BITS ⇒ mb_load_from_source_at
  ] m l addr.

(* unificazione dell'impostazione della memoria: chk_update_ranged chk inf sup v *)
ndefinition check_update_ranged ≝
λt:memory_impl.
 match t
  return λt.aux_chk_type t → word32 → word16 → memory_type → aux_chk_type t 
 with
  [ MEM_FUNC ⇒ λc:aux_chk_type MEM_FUNC.
               λaddr:word32.
               λrange:word16.
               λv:memory_type.
               mf_check_update_ranged c addr range v
  | MEM_TREE ⇒ λc:aux_chk_type MEM_TREE.
               λaddr:word32.
               λrange:word16.
               λv:memory_type.
               mt_update_ranged ? c addr ? (w16_to_recw16 range) v
  | MEM_BITS ⇒ λc:aux_chk_type MEM_BITS.
               λaddr:word32.
               λrange:word16.
               λv:memory_type.
               mt_update_ranged ? c addr ? (w16_to_recw16 range) (mk_Array8T ? v v v v v v v v)
  ].

(* unificazione dell'impostazione dei bit: chk_update_bit chk addr sub v *)
(* NB: dove non esiste la granularita' del bit, lascio inalterato *)
ndefinition check_update_bit ≝
λt:memory_impl.
 match t
  return λt.aux_chk_type t → word32 → oct → memory_type → aux_chk_type t
 with
  [ MEM_FUNC ⇒ λc:aux_chk_type MEM_FUNC.
               λaddr:word32.
               λo:oct.
               λv:memory_type.
               c
  | MEM_TREE ⇒ λc:aux_chk_type MEM_TREE.
               λaddr:word32.
               λo:oct.
               λv:memory_type.
               c
  | MEM_BITS ⇒ λc:aux_chk_type MEM_BITS.
               λaddr:word32.
               λo:oct.
               λv:memory_type.
               mb_chk_update_bit c addr o v
  ].
