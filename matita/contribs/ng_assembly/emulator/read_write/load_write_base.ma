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

include "emulator/read_write/read_write.ma".

(* mattoni base *)
(* - incrementano l'indirizzo normalmente *)
(* - incrementano PC attraverso il filtro *)

(* lettura byte da addr *)
ndefinition loadb_from ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
λaddr:word32.λcur_pc:word16.λfetched:exadecim.
 opt_map … (memory_filter_read … s addr)
  (λb.Some ? (triple … s b (plus_w16_d_d cur_pc (extu2_w16 fetched)))).

(* lettura bit da addr *)
ndefinition loadbit_from ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
λaddr:word32.λsub:oct.λcur_pc:word16.λfetched:exadecim.
 opt_map … (memory_filter_read_bit … s addr sub)
  (λb.Some ? (triple … s b (plus_w16_d_d cur_pc (extu2_w16 fetched)))).

(* lettura word da addr *)
ndefinition loadw_from ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
λaddr:word32.λcur_pc:word16.λfetched:exadecim.
 opt_map … (memory_filter_read … s addr)
  (λbh.opt_map … (memory_filter_read … s (succ_w32 addr))
   (λbl.Some ? (triple … s 〈bh:bl〉 (plus_w16_d_d cur_pc (extu2_w16 fetched))))).

(* scrittura byte su addr *)
ndefinition writeb_to ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
λaddr:word32.λflag:aux_mod_type.λcur_pc:word16.λfetched:exadecim.λwriteb:byte8.
 opt_map … (memory_filter_write … s addr flag writeb)
  (λtmps.Some ? (pair … tmps (plus_w16_d_d cur_pc (extu2_w16 fetched)))).

(* scrittura bit su addr *)
ndefinition writebit_to ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
λaddr:word32.λsub:oct.λcur_pc:word16.λfetched:exadecim.λwriteb:bool.
 opt_map … (memory_filter_write_bit … s addr sub writeb)
  (λtmps.Some ? (pair … tmps (plus_w16_d_d cur_pc (extu2_w16 fetched)))).

(* scrittura word su addr *) 
ndefinition writew_to ≝
λm:mcu_type.λt:memory_impl.λs:any_status m t.
λaddr:word32.λflag:aux_mod_type.λcur_pc:word16.λfetched:exadecim.λwritew:word16.
 opt_map … (memory_filter_write … s addr auxMode_ok (cnH ? writew))
  (λtmps1.opt_map … (memory_filter_write … tmps1 (succ_w32 addr) auxMode_ok (cnL ? writew))
    (λtmps2.Some ? (pair … tmps2 (plus_w16_d_d cur_pc (extu2_w16 fetched))))).

(* ausiliari per definire i tipi e la lettura/scrittura *)

(* ausiliaria per definire il tipo di aux_load *)
ndefinition aux_load_typing ≝
λm:mcu_type.λt:memory_impl.λbyteflag:bool.
 any_status m t → word32 → word16 → exadecim →
 option (Prod3T (any_status m t) match byteflag with [ true ⇒ byte8 | false ⇒ word16 ] word16).

(* per non dover ramificare i vari load in byte/word *)
ndefinition aux_load ≝
λm:mcu_type.λt:memory_impl.λbyteflag:bool.match byteflag return aux_load_typing m t with
 [ true ⇒ loadb_from m t | false ⇒ loadw_from m t ].

(* ausiliaria per definire il tipo di aux_write *)
ndefinition aux_write_typing ≝
λm:mcu_type.λt:memory_impl.λbyteflag:bool.
 any_status m t → word32 → aux_mod_type → word16 → exadecim →
 match byteflag with [ true ⇒ byte8 | false ⇒ word16 ] →
 option (ProdT (any_status m t) word16).

(* per non dover ramificare i vari load in byte/word *)
ndefinition aux_write ≝
λm:mcu_type.λt:memory_impl.λbyteflag:bool.match byteflag return aux_write_typing m t with
 [ true ⇒ writeb_to m t | false ⇒ writew_to m t ].

ndefinition mem_read_s ≝
λm,t.λs:any_status m t.mem_read t (mem_desc … s) (chk_desc … s).

ndefinition mem_read_bit_s ≝
λm,t.λs:any_status m t.mem_read_bit t (mem_desc … s) (chk_desc … s).
