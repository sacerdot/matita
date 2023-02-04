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
(* 2) Some cur_clk,clks,pseudo,mode,cur_pc = fetch eseguito *)
ndefinition aux_clk_type ≝ λm:mcu_type.Prod5T nat nat (aux_pseudo_type m) (aux_im_type m) word16.

nlemma clk_is_comparable : mcu_type → comparable.
 #m; @ (aux_clk_type m)
  ##[ napply (zeroc (quintuple_is_comparable nat_is_comparable nat_is_comparable (pseudo_is_comparable m) (im_is_comparable m) word16_is_comparable))
  ##| napply (forallc (quintuple_is_comparable nat_is_comparable nat_is_comparable (pseudo_is_comparable m) (im_is_comparable m) word16_is_comparable))
  ##| napply (eqc (quintuple_is_comparable nat_is_comparable nat_is_comparable (pseudo_is_comparable m) (im_is_comparable m) word16_is_comparable))
  ##| napply (eqc_to_eq (quintuple_is_comparable nat_is_comparable nat_is_comparable (pseudo_is_comparable m) (im_is_comparable m) word16_is_comparable))
  ##| napply (eq_to_eqc (quintuple_is_comparable nat_is_comparable nat_is_comparable (pseudo_is_comparable m) (im_is_comparable m) word16_is_comparable))
  ##| napply (neqc_to_neq (quintuple_is_comparable nat_is_comparable nat_is_comparable (pseudo_is_comparable m) (im_is_comparable m) word16_is_comparable))
  ##| napply (neq_to_neqc (quintuple_is_comparable nat_is_comparable nat_is_comparable (pseudo_is_comparable m) (im_is_comparable m) word16_is_comparable))
  ##| napply (decidable_c (quintuple_is_comparable nat_is_comparable nat_is_comparable (pseudo_is_comparable m) (im_is_comparable m) word16_is_comparable))
  ##| napply (symmetric_eqc (quintuple_is_comparable nat_is_comparable nat_is_comparable (pseudo_is_comparable m) (im_is_comparable m) word16_is_comparable))
  ##]
nqed.

unification hint 0 ≔ M:mcu_type ⊢ carr (clk_is_comparable M) ≡ aux_clk_type M.

(* descritture della alu *)
ndefinition aux_alu_type ≝
λm.match m with
 [ HC05 ⇒ alu_HC05
 | HC08 ⇒ alu_HC08
 | HCS08 ⇒ alu_HC08
 | RS08 ⇒ alu_RS08
 | IP2022 ⇒ alu_IP2022
 ].

nlemma alu_is_comparable : mcu_type → comparable.
 #m; @ (aux_alu_type m)
  ##[ nelim m;
      ##[ napply (zeroc aluHC05_is_comparable)
      ##| napply (zeroc aluHC08_is_comparable)
      ##| napply (zeroc aluHC08_is_comparable)
      ##| napply (zeroc aluRS08_is_comparable)
      ##| napply (zeroc aluIP2022_is_comparable) ##]
  ##| nelim m;
      ##[ napply (forallc aluHC05_is_comparable)
      ##| napply (forallc aluHC08_is_comparable)
      ##| napply (forallc aluHC08_is_comparable)
      ##| napply (forallc aluRS08_is_comparable)
      ##| napply (forallc aluIP2022_is_comparable) ##]
  ##| nelim m;
      ##[ napply (eqc aluHC05_is_comparable)
      ##| napply (eqc aluHC08_is_comparable)
      ##| napply (eqc aluHC08_is_comparable)
      ##| napply (eqc aluRS08_is_comparable)
      ##| napply (eqc aluIP2022_is_comparable) ##]
  ##| nelim m;
      ##[ napply (eqc_to_eq aluHC05_is_comparable)
      ##| napply (eqc_to_eq aluHC08_is_comparable)
      ##| napply (eqc_to_eq aluHC08_is_comparable)
      ##| napply (eqc_to_eq aluRS08_is_comparable)
      ##| napply (eqc_to_eq aluIP2022_is_comparable) ##]
  ##| nelim m;
      ##[ napply (eq_to_eqc aluHC05_is_comparable)
      ##| napply (eq_to_eqc aluHC08_is_comparable)
      ##| napply (eq_to_eqc aluHC08_is_comparable)
      ##| napply (eq_to_eqc aluRS08_is_comparable)
      ##| napply (eq_to_eqc aluIP2022_is_comparable) ##]
  ##| nelim m;
      ##[ napply (neqc_to_neq aluHC05_is_comparable)
      ##| napply (neqc_to_neq aluHC08_is_comparable)
      ##| napply (neqc_to_neq aluHC08_is_comparable)
      ##| napply (neqc_to_neq aluRS08_is_comparable)
      ##| napply (neqc_to_neq aluIP2022_is_comparable) ##]
  ##| nelim m;
      ##[ napply (neq_to_neqc aluHC05_is_comparable)
      ##| napply (neq_to_neqc aluHC08_is_comparable)
      ##| napply (neq_to_neqc aluHC08_is_comparable)
      ##| napply (neq_to_neqc aluRS08_is_comparable)
      ##| napply (neq_to_neqc aluIP2022_is_comparable) ##]
  ##| nelim m;
      ##[ napply (decidable_c aluHC05_is_comparable)
      ##| napply (decidable_c aluHC08_is_comparable)
      ##| napply (decidable_c aluHC08_is_comparable)
      ##| napply (decidable_c aluRS08_is_comparable)
      ##| napply (decidable_c aluIP2022_is_comparable) ##]
  ##| nelim m;
      ##[ napply (symmetric_eqc aluHC05_is_comparable)
      ##| napply (symmetric_eqc aluHC08_is_comparable)
      ##| napply (symmetric_eqc aluHC08_is_comparable)
      ##| napply (symmetric_eqc aluRS08_is_comparable)
      ##| napply (symmetric_eqc aluIP2022_is_comparable) ##]
  ##]
nqed.

unification hint 0 ≔ M:mcu_type ⊢ carr (alu_is_comparable M) ≡ aux_alu_type M.

(* tipo processore dipendente dalla mcu, varia solo la ALU *)
nrecord any_status (mcu:mcu_type) (t:memory_impl): Type ≝
 {
 (* descrittore della alu *)
 alu : aux_alu_type mcu;
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

ndefinition eq_anystatus ≝
λm,t.λs1,s2:any_status m t.
 (eqc ? (alu … s1) (alu … s2)) ⊗
 (eqc ? (mem_desc … s1) (mem_desc … s2)) ⊗
 (eqc ? (chk_desc … s1) (chk_desc … s2)) ⊗
 (eqc ? (clk_desc … s1) (clk_desc … s2)).

ndefinition forall_anystatus ≝ λm,t.λP:any_status m t → bool.
 forallc ? (λr1.forallc ? (λr2.
 forallc ? (λr3.forallc ? (λr4.
 P (mk_any_status m t r1 r2 r3 r4))))).

(* confronto di una regione di memoria [addr1 ; ... ; addrn] *)
nlet rec forall_memory_ranged
 (t:memory_impl)
 (chk1:aux_chk_type t) (chk2:aux_chk_type t)
 (mem1:aux_mem_type t) (mem2:aux_mem_type t)
 (sel:oct) (addrl:list word16) on addrl ≝
 match addrl return λ_.bool with
  [ nil ⇒ true
  | cons hd tl ⇒ (eqc ? (mem_read t mem1 chk1 sel hd) (mem_read t mem2 chk2 sel hd)) ⊗
                 (forall_memory_ranged t chk1 chk2 mem1 mem2 sel tl)
  ].
