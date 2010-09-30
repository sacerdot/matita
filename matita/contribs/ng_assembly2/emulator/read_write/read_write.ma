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

include "emulator/read_write/RS08_read_write.ma".
include "emulator/read_write/IP2022_read_write.ma".

(* filtraggio avviene sempre sul segmento 0 *)

(* in caso di RS08/IP2022 si dirotta sul filtro, altrimenti si legge direttamente *)
ndefinition memory_filter_read ≝
λm:mcu_type.λt:memory_impl.match m return λm:mcu_type.any_status m t → word16 → option byte8 with
 [ HC05 ⇒ λs:any_status HC05 t.
  mem_read t (mem_desc … s) (chk_desc … s) o0
 | HC08 ⇒ λs:any_status HC08 t.
  mem_read t (mem_desc … s) (chk_desc … s) o0
 | HCS08 ⇒ λs:any_status HCS08 t.
  mem_read t (mem_desc … s) (chk_desc … s) o0
 | RS08 ⇒ RS08_memory_filter_read t
 | IP2022 ⇒ IP2022_memory_filter_read t
 ].

ndefinition memory_filter_read_bit ≝
λm:mcu_type.λt:memory_impl.match m return λm:mcu_type.any_status m t → word16 → oct → option bool with
 [ HC05 ⇒ λs:any_status HC05 t.
  mem_read_bit t (mem_desc … s) (chk_desc … s) o0
 | HC08 ⇒ λs:any_status HC08 t.
  mem_read_bit t (mem_desc … s) (chk_desc … s) o0
 | HCS08 ⇒ λs:any_status HCS08 t.
  mem_read_bit t (mem_desc … s) (chk_desc … s) o0
 | RS08 ⇒ RS08_memory_filter_read_bit t
 | IP2022 ⇒ IP2022_memory_filter_read_bit t
 ].

ndefinition memory_filter_write ≝
λm:mcu_type.λt:memory_impl.match m
 return λm:mcu_type.any_status m t → word16 → aux_mod_type → byte8 → option (any_status m t) with
 [ HC05 ⇒ λs:any_status HC05 t.λaddr:word16.λflag:aux_mod_type.λval:byte8.
  opt_map … (mem_update t (mem_desc … s) (chk_desc … s) o0 addr val)
   (λmem.Some ? (set_mem_desc … s mem))
 | HC08 ⇒ λs:any_status HC08 t.λaddr:word16.λflag:aux_mod_type.λval:byte8.
  opt_map … (mem_update t (mem_desc … s) (chk_desc … s) o0 addr val)
   (λmem.Some ? (set_mem_desc … s mem))
 | HCS08 ⇒ λs:any_status HCS08 t.λaddr:word16.λflag:aux_mod_type.λval:byte8.
  opt_map … (mem_update t (mem_desc … s) (chk_desc … s) o0 addr val)
   (λmem.Some ? (set_mem_desc … s mem))
 | RS08 ⇒ λs:any_status RS08 t.λaddr:word16.λflag:aux_mod_type.
  RS08_memory_filter_write t s addr
 | IP2022 ⇒ IP2022_memory_filter_write t
 ].

ndefinition memory_filter_write_bit ≝
λm:mcu_type.λt:memory_impl.match m
 return λm:mcu_type.any_status m t → word16 → oct → bool → option (any_status m t) with
 [ HC05 ⇒ λs:any_status HC05 t.λaddr:word16.λsub:oct.λval:bool.
  opt_map … (mem_update_bit t (mem_desc … s) (chk_desc … s) o0 addr sub val)
    (λmem.Some ? (set_mem_desc … s mem))
 | HC08 ⇒ λs:any_status HC08 t.λaddr:word16.λsub:oct.λval:bool.
  opt_map … (mem_update_bit t (mem_desc … s) (chk_desc … s) o0 addr sub val)
    (λmem.Some ? (set_mem_desc … s mem))
 | HCS08 ⇒ λs:any_status HCS08 t.λaddr:word16.λsub:oct.λval:bool.
  opt_map … (mem_update_bit t (mem_desc … s) (chk_desc … s) o0 addr sub val)
   (λmem.Some ? (set_mem_desc … s mem)) 
 | RS08 ⇒ RS08_memory_filter_write_bit t
 | IP2022 ⇒ IP2022_memory_filter_write_bit t
 ].
