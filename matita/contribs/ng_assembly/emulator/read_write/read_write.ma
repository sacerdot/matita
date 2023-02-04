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

(* in caso di RS08/IP2022 si dirotta sul filtro, altrimenti si legge direttamente *)
ndefinition memory_filter_read ≝
λm:mcu_type.λt:memory_impl.match m return λm:mcu_type.any_status m t → word32 → option byte8 with
 [ HC05 ⇒ λs:any_status HC05 t.λaddr:word32.
  mem_read t (mem_desc ? t s) (chk_desc ? t s) addr
 | HC08 ⇒ λs:any_status HC08 t.λaddr:word32.
  mem_read t (mem_desc ? t s) (chk_desc ? t s) addr
 | HCS08 ⇒ λs:any_status HCS08 t.λaddr:word32.
  mem_read t (mem_desc ? t s) (chk_desc ? t s) addr
 | RS08 ⇒ λs:any_status RS08 t.λaddr:word32.
  RS08_memory_filter_read t s addr
 | IP2022 ⇒ λs:any_status IP2022 t.λaddr:word32.
  IP2022_memory_filter_read t s addr
 ].

ndefinition memory_filter_read_bit ≝
λm:mcu_type.λt:memory_impl.match m return λm:mcu_type.any_status m t → word32 → oct → option bool with
 [ HC05 ⇒ λs:any_status HC05 t.λaddr:word32.λsub:oct.
  mem_read_bit t (mem_desc ? t s) (chk_desc ? t s) addr sub
 | HC08 ⇒ λs:any_status HC08 t.λaddr:word32.λsub:oct.
  mem_read_bit t (mem_desc ? t s) (chk_desc ? t s) addr sub
 | HCS08 ⇒ λs:any_status HCS08 t.λaddr:word32.λsub:oct.
  mem_read_bit t (mem_desc ? t s) (chk_desc ? t s) addr sub
 | RS08 ⇒ λs:any_status RS08 t.λaddr:word32.λsub:oct.
  RS08_memory_filter_read_bit t s addr sub
 | IP2022 ⇒ λs:any_status IP2022 t.λaddr:word32.λsub:oct.
  IP2022_memory_filter_read_bit t s addr sub
 ].

ndefinition memory_filter_write ≝
λm:mcu_type.λt:memory_impl.match m
 return λm:mcu_type.any_status m t → word32 → aux_mod_type → byte8 → option (any_status m t) with
 [ HC05 ⇒ λs:any_status HC05 t.λaddr:word32.λflag:aux_mod_type.λval:byte8.
  opt_map … (mem_update t (mem_desc ? t s) (chk_desc ? t s) addr val)
   (λmem.Some ? (set_mem_desc ? t s mem))
 | HC08 ⇒ λs:any_status HC08 t.λaddr:word32.λflag:aux_mod_type.λval:byte8.
  opt_map … (mem_update t (mem_desc ? t s) (chk_desc ? t s) addr val)
   (λmem.Some ? (set_mem_desc ? t s mem))
 | HCS08 ⇒ λs:any_status HCS08 t.λaddr:word32.λflag:aux_mod_type.λval:byte8.
  opt_map … (mem_update t (mem_desc ? t s) (chk_desc ? t s) addr val)
   (λmem.Some ? (set_mem_desc ? t s mem))
 | RS08 ⇒ λs:any_status RS08 t.λaddr:word32.λflag:aux_mod_type.λval:byte8.
  RS08_memory_filter_write t s addr val
 | IP2022 ⇒ λs:any_status IP2022 t.λaddr:word32.λflag:aux_mod_type.λval:byte8.
  IP2022_memory_filter_write t s addr flag val
 ].

ndefinition memory_filter_write_bit ≝
λm:mcu_type.λt:memory_impl.match m
 return λm:mcu_type.any_status m t → word32 → oct → bool → option (any_status m t) with
 [ HC05 ⇒ λs:any_status HC05 t.λaddr:word32.λsub:oct.λval:bool.
  opt_map … (mem_update_bit t (mem_desc ? t s) (chk_desc ? t s) addr sub val)
    (λmem.Some ? (set_mem_desc ? t s mem))
 | HC08 ⇒ λs:any_status HC08 t.λaddr:word32.λsub:oct.λval:bool.
  opt_map … (mem_update_bit t (mem_desc ? t s) (chk_desc ? t s) addr sub val)
    (λmem.Some ? (set_mem_desc ? t s mem))
 | HCS08 ⇒ λs:any_status HCS08 t.λaddr:word32.λsub:oct.λval:bool.
  opt_map … (mem_update_bit t (mem_desc ? t s) (chk_desc ? t s) addr sub val)
   (λmem.Some ? (set_mem_desc ? t s mem)) 
 | RS08 ⇒ λs:any_status RS08 t.λaddr:word32.λsub:oct.λval:bool.
  RS08_memory_filter_write_bit t s addr sub val
 | IP2022 ⇒ λs:any_status IP2022 t.λaddr:word32.λsub:oct.λval:bool.
  IP2022_memory_filter_write_bit t s addr sub val
 ].
