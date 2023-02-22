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

(* se si disattiva l'implementazione a funzione
   la memoria diventa un'oggetto confrontabile! *)

(* tipi di implementazione della memoria *)
ninductive memory_impl : Type ≝
  (*MEM_FUNC: memory_impl
|*) MEM_TREE: memory_impl
| MEM_BITS: memory_impl.

(* ausiliario per il tipo della memoria *)
ndefinition aux_mem_type ≝
λt:memory_impl.match t with
 [ (*MEM_FUNC ⇒ oct → word16 → byte8
 |*) MEM_TREE ⇒ aux_20B_type byte8
 | MEM_BITS ⇒ aux_20B_type (Array8T bool)
 ].

(* ausiliario per il tipo del checker *)
ndefinition aux_chk_type ≝
λt:memory_impl.match t with
 [ (*MEM_FUNC ⇒ oct → word16 → memory_type
 |*) MEM_TREE ⇒ aux_20B_type memory_type
 | MEM_BITS ⇒ aux_20B_type (Array8T memory_type)
 ].

(* unificazione di out_of_bound_memory *)
ndefinition out_of_bound_memory ≝
λt:memory_impl.
 match t
  return λt.aux_chk_type t
 with
  [ (*MEM_FUNC ⇒ mf_out_of_bound_memory
  |*) MEM_TREE ⇒ mt_out_of_bound_memory
  | MEM_BITS ⇒ mb_out_of_bound_memory
  ].

(* unificazione di zero_memory *)
ndefinition zero_memory ≝
λt:memory_impl.
 match t
  return λt.aux_mem_type t
 with
  [ (*MEM_FUNC ⇒ mf_zero_memory
  |*) MEM_TREE ⇒ mt_zero_memory
  | MEM_BITS ⇒ mb_zero_memory
  ].

(* unificazione della lettura senza chk: mem_read_abs mem addr *)
ndefinition mem_read_abs ≝
λt:memory_impl.
 match t
  return λt.aux_mem_type t → oct → word16 → byte8 
 with
  [ (*MEM_FUNC ⇒ λm:aux_mem_type MEM_FUNC.
               m
  |*) MEM_TREE ⇒ λm:aux_mem_type MEM_TREE.
               mt_visit ? m
  | MEM_BITS ⇒ λm:aux_mem_type MEM_BITS.
               λsel:oct.λaddr:word16.
               byte8_of_bits (mt_visit ? m sel addr)
  ].

(* unificazione del chk *)
ndefinition chk_get ≝
λt:memory_impl.
 match t
  return λt.aux_chk_type t → oct → word16 → Array8T memory_type
 with
  [ (*MEM_FUNC ⇒ λc:aux_chk_type MEM_FUNC.λsel:oct.λaddr:word16.
   match c sel addr with
    [ MEM_READ_ONLY ⇒ mk_Array8T ? MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY
    | MEM_READ_WRITE ⇒ mk_Array8T ? MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE
    | MEM_OUT_OF_BOUND ⇒ mk_Array8T ? MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND
    ]
  |*) MEM_TREE ⇒ λc:aux_chk_type MEM_TREE.λsel:oct.λaddr:word16.
   match mt_visit ? c sel addr with
    [ MEM_READ_ONLY ⇒ mk_Array8T ? MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY MEM_READ_ONLY
    | MEM_READ_WRITE ⇒ mk_Array8T ? MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE MEM_READ_WRITE
    | MEM_OUT_OF_BOUND ⇒ mk_Array8T ? MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND MEM_OUT_OF_BOUND
    ]
  | MEM_BITS ⇒ mt_visit ?
  ].

(* unificazione della lettura con chk: mem_read mem chk addr *)
ndefinition mem_read ≝
λt:memory_impl.
 match t
  return λt.aux_mem_type t → aux_chk_type t → oct → word16 → option byte8 
 with
  [ (*MEM_FUNC ⇒ mf_mem_read
  |*) MEM_TREE ⇒ mt_mem_read
  | MEM_BITS ⇒ mb_mem_read
  ].

(* unificazione della lettura di bit con chk: mem_read mem chk addr sub *)
ndefinition mem_read_bit ≝
λt:memory_impl.
 match t
  return λt.aux_mem_type t → aux_chk_type t → oct → word16 → oct → option bool 
 with
  [ (*MEM_FUNC ⇒ λm:aux_mem_type MEM_FUNC.
               λc:aux_chk_type MEM_FUNC.
               λsel:oct.λaddr:word16.
               λo:oct.
               opt_map … (mf_mem_read m c sel addr)
                (λb.Some ? (getn_array8T o bool (bits_of_byte8 b))) 
  |*) MEM_TREE ⇒ λm:aux_mem_type MEM_TREE.
               λc:aux_chk_type MEM_TREE.
               λsel:oct.λaddr:word16.
               λo:oct.
               opt_map … (mt_mem_read m c sel addr)
                (λb.Some ? (getn_array8T o bool (bits_of_byte8 b)))
  | MEM_BITS ⇒ mb_mem_read_bit
  ].

(* unificazione della scrittura con chk: mem_update mem chk addr val *)
ndefinition mem_update ≝
λt:memory_impl.
 match t
  return λt.aux_mem_type t → aux_chk_type t → oct → word16 → byte8 → option (aux_mem_type t)
 with
  [ (*MEM_FUNC ⇒ mf_mem_update
  |*) MEM_TREE ⇒ mt_mem_update
  | MEM_BITS ⇒ mb_mem_update
  ].

(* unificazione della scrittura di bit con chk: mem_update mem chk addr sub val *)
ndefinition mem_update_bit ≝
λt:memory_impl.
 match t
  return λt.aux_mem_type t → aux_chk_type t → oct → word16 → oct → bool → option (aux_mem_type t) 
 with
  [ (*MEM_FUNC ⇒ λm:aux_mem_type MEM_FUNC.
               λc:aux_chk_type MEM_FUNC.
               λsel:oct.λaddr:word16.
               λo:oct.
               λv:bool.
               mf_mem_update m c sel addr (byte8_of_bits (setn_array8T o bool (bits_of_byte8 (m addr)) v))
  |*) MEM_TREE ⇒ λm:aux_mem_type MEM_TREE.
               λc:aux_chk_type MEM_TREE.
               λsel:oct.λaddr:word16.
               λo:oct.
               λv:bool.
               mt_mem_update m c sel addr (byte8_of_bits (setn_array8T o bool (bits_of_byte8 (mt_visit ? m sel addr)) v))
  | MEM_BITS ⇒ mb_mem_update_bit
  ].

(* unificazione del caricamento: load_from_source_at old_mem source addr *)
ndefinition load_from_source_at ≝
λt:memory_impl.
 match t
  return λt.aux_mem_type t → list byte8 → oct → word16 → aux_mem_type t 
 with
  [ (*MEM_FUNC ⇒ mf_load_from_source_at
  |*) MEM_TREE ⇒ mt_load_from_source_at
  | MEM_BITS ⇒ mb_load_from_source_at
  ].

(* unificazione dell'impostazione della memoria: chk_update_ranged chk inf sup v *)
ndefinition check_update_ranged ≝
λt:memory_impl.
 match t
  return λt.aux_chk_type t → oct → word16 → word16 → memory_type → aux_chk_type t 
 with
  [ (*MEM_FUNC ⇒ mf_check_update_ranged
  |*) MEM_TREE ⇒ λc:aux_chk_type MEM_TREE.
               λsel:oct.λaddr:word16.
               λrange:word16.
               mt_update_ranged ? c sel addr ? (w16_to_recw16 range)
  | MEM_BITS ⇒ λc:aux_chk_type MEM_BITS.
               λsel:oct.λaddr:word16.
               λrange:word16.
               λv:memory_type.
               mt_update_ranged ? c sel addr ? (w16_to_recw16 range) (mk_Array8T ? v v v v v v v v)
  ].

(* unificazione dell'impostazione dei bit: chk_update_bit chk addr sub v *)
(* NB: dove non esiste la granularita' del bit, lascio inalterato *)
ndefinition check_update_bit ≝
λt:memory_impl.
 match t
  return λt.aux_chk_type t → oct → word16 → oct → memory_type → aux_chk_type t
 with
  [ (*MEM_FUNC ⇒ λc:aux_chk_type MEM_FUNC.
               λsel:oct.λaddr:word16.
               λo:oct.
               λv:memory_type.
               c
  |*) MEM_TREE ⇒ λc:aux_chk_type MEM_TREE.
               λsel:oct.λaddr:word16.
               λo:oct.
               λv:memory_type.
               c
  | MEM_BITS ⇒ mb_chk_update_bit
  ].

ndefinition mem_is_comparable: memory_impl → comparable.
 #m; @ (aux_mem_type m)
  ##[ nelim m;
      ##[ napply mt_zero_memory
      ##| napply mb_zero_memory ##]
  ##| nelim m;
      ##[ napply (forallc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable byte8_is_comparable))))))
      ##| napply (forallc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar8_is_comparable bool_is_comparable))))))) ##]
  ##| nelim m;
      ##[ napply (eqc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable byte8_is_comparable))))))
      ##| napply (eqc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar8_is_comparable bool_is_comparable))))))) ##]
  ##| nelim m;
      ##[ napply (eqc_to_eq (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable byte8_is_comparable))))))
      ##| napply (eqc_to_eq (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar8_is_comparable bool_is_comparable))))))) ##]
  ##| nelim m;
      ##[ napply (eq_to_eqc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable byte8_is_comparable))))))
      ##| napply (eq_to_eqc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar8_is_comparable bool_is_comparable))))))) ##]
  ##| nelim m;
      ##[ napply (neqc_to_neq (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable byte8_is_comparable))))))
      ##| napply (neqc_to_neq (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar8_is_comparable bool_is_comparable))))))) ##]
  ##| nelim m;
      ##[ napply (neq_to_neqc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable byte8_is_comparable))))))
      ##| napply (neq_to_neqc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar8_is_comparable bool_is_comparable))))))) ##]
  ##| nelim m;
      ##[ napply (decidable_c (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable byte8_is_comparable))))))
      ##| napply (decidable_c (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar8_is_comparable bool_is_comparable))))))) ##]
  ##| nelim m;
      ##[ napply (symmetric_eqc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable byte8_is_comparable))))))
      ##| napply (symmetric_eqc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar8_is_comparable bool_is_comparable))))))) ##]
  ##]
nqed.

unification hint 0 ≔ M:memory_impl ⊢ carr (mem_is_comparable M) ≡ aux_mem_type M.

ndefinition chk_is_comparable: memory_impl → comparable.
 #m; @ (aux_chk_type m)
  ##[ nelim m;
      ##[ napply mt_out_of_bound_memory
      ##| napply mb_out_of_bound_memory ##]
  ##| nelim m;
      ##[ napply (forallc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable memorytype_is_comparable))))))
      ##| napply (forallc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar8_is_comparable memorytype_is_comparable))))))) ##]
  ##| nelim m;
      ##[ napply (eqc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable memorytype_is_comparable))))))
      ##| napply (eqc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar8_is_comparable memorytype_is_comparable))))))) ##]
  ##| nelim m;
      ##[ napply (eqc_to_eq (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable memorytype_is_comparable))))))
      ##| napply (eqc_to_eq (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar8_is_comparable memorytype_is_comparable))))))) ##]
  ##| nelim m;
      ##[ napply (eq_to_eqc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable memorytype_is_comparable))))))
      ##| napply (eq_to_eqc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar8_is_comparable memorytype_is_comparable))))))) ##]
  ##| nelim m;
      ##[ napply (neqc_to_neq (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable memorytype_is_comparable))))))
      ##| napply (neqc_to_neq (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar8_is_comparable memorytype_is_comparable))))))) ##]
  ##| nelim m;
      ##[ napply (neq_to_neqc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable memorytype_is_comparable))))))
      ##| napply (neq_to_neqc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar8_is_comparable memorytype_is_comparable))))))) ##]
  ##| nelim m;
      ##[ napply (decidable_c (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable memorytype_is_comparable))))))
      ##| napply (decidable_c (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar8_is_comparable memorytype_is_comparable))))))) ##]
  ##| nelim m;
      ##[ napply (symmetric_eqc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable memorytype_is_comparable))))))
      ##| napply (symmetric_eqc (ar8_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar16_is_comparable (ar8_is_comparable memorytype_is_comparable))))))) ##]
  ##]
nqed.

unification hint 0 ≔ M:memory_impl ⊢ carr (chk_is_comparable M) ≡ aux_chk_type M.
