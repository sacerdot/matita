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

include "emulator/memory/memory_abs.ma".
include "emulator/status/HC05_status.ma".
include "emulator/status/HC08_status.ma".
include "emulator/status/RS08_status.ma".
include "emulator/status/IP2022_status.ma".
include "emulator/opcodes/pseudo.ma".

(* *********************************** *)
(* STATUS INTERNO DEL PROCESSORE (ALU) *)
(* *********************************** *)

(* descrittore del click = stato di avanzamento dell'esecuzione *)
(* 1) None = istruzione eseguita, attesa del fetch *)
(* 2) Some cur_clk,pseudo,mode,clks,cur_pc = fetch eseguito *)
ndefinition aux_clk_type ≝ λm:mcu_type.Prod5T byte8 (aux_pseudo_type m) (aux_im_type m) byte8 word16.

(* tipo processore dipendente dalla mcu, varia solo la ALU *)
nrecord any_status (mcu:mcu_type) (t:memory_impl): Type ≝
 {
 alu : match mcu with
  [ HC05 ⇒ alu_HC05 | HC08 ⇒ alu_HC08 | HCS08 ⇒ alu_HC08 | RS08 ⇒ alu_RS08
  | IP2022 ⇒ alu_IP2022 ];

 (* descritore della memoria *)
 mem_desc : aux_mem_type t;
 (* descrittore del tipo di memoria installata *)
 chk_desc : aux_chk_type t;
 (* descrittore del clik *)
 clk_desc : option (aux_clk_type mcu)
 }.

(* evitare di mostrare la memoria/descrittore che impalla il visualizzatore *)
notation > "{hvbox('Alu' ≝ alu ; break 'Clk' ≝ clk)}" non associative with precedence 80 
 for @{ 'mk_any_status $alu $mem $chk $clk }.
interpretation "mk_any_status" 'mk_any_status alu mem chk clk =
 (mk_any_status alu mem chk clk).

(* ******************** *)
(* CONFRONTO FRA STATUS *)
(* ******************** *)

ndefinition eq_alu ≝
λm:mcu_type.
 match m
  return λm.
   match m with
    [ HC05 ⇒ alu_HC05 | HC08 ⇒ alu_HC08 | HCS08 ⇒ alu_HC08 | RS08 ⇒ alu_RS08
    | IP2022 ⇒ alu_IP2022 ] →
   match m with
    [ HC05 ⇒ alu_HC05 | HC08 ⇒ alu_HC08 | HCS08 ⇒ alu_HC08 | RS08 ⇒ alu_RS08
    | IP2022 ⇒ alu_IP2022 ] →
   bool
 with
  [ HC05 ⇒ eq_HC05_alu
  | HC08 ⇒ eq_HC08_alu
  | HCS08 ⇒ eq_HC08_alu
  | RS08 ⇒ eq_RS08_alu
  | IP2022 ⇒ eq_IP2022_alu
  ].

(* confronto di una regione di memoria [addr1 ; ... ; addrn] *)
nlet rec forall_memory_ranged
 (t:memory_impl)
 (chk1:aux_chk_type t) (chk2:aux_chk_type t)
 (mem1:aux_mem_type t) (mem2:aux_mem_type t)
 (addrl:list word32) on addrl ≝
 match addrl return λ_.bool with
  [ nil ⇒ true
  | cons hd tl ⇒ (eq_option byte8 eq_b8 (mem_read t mem1 chk1 hd)
                                        (mem_read t mem2 chk2 hd)) ⊗
                 (forall_memory_ranged t chk1 chk2 mem1 mem2 tl)
  ].

ndefinition eq_clk ≝ λm.eq_option … (eq_quintuple … eq_b8 (eq_pseudo m) (eq_im m) eq_b8 eq_w16).

(* generalizzazione del confronto fra stati *)
ndefinition eq_anystatus ≝
λm:mcu_type.λt:memory_impl.λs1,s2:any_status m t.λaddrl:list word32.
 (* 1) confronto della ALU *)
 (eq_alu m (alu m t s1) (alu m t s2)) ⊗
 (* 2) confronto della memoria in [inf,inf+n] *)
 (forall_memory_ranged t (chk_desc m t s1) (chk_desc m t s2)
                         (mem_desc m t s1) (mem_desc m t s2) addrl) ⊗
 (* 3) confronto del clik *)
 (eq_clk m (clk_desc m t s1) (clk_desc m t s2)).
