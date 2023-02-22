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

include "emulator/status/HC05_status_lemmas.ma".
include "emulator/status/HC08_status_lemmas.ma".
include "emulator/status/RS08_status_lemmas.ma".
include "emulator/status/IP2022_status_lemmas.ma".
include "emulator/status/status.ma".
include "common/option_lemmas.ma".
include "common/prod_lemmas.ma".
include "emulator/opcodes/pseudo_lemmas.ma".

(* *********************************** *)
(* STATUS INTERNO DEL PROCESSORE (ALU) *)
(* *********************************** *)

nlemma symmetric_eqclk : ∀m.∀clk1,clk2.eq_clk m clk1 clk2 = eq_clk m clk2 clk1.
 #m;
 napply (symmetric_eqoption ? (eq_quintuple …) (symmetric_eqquintuple …));
 ##[ ##1: napply symmetric_eqw16
 ##| ##2: napply symmetric_eqb8
 ##| ##3: napply (symmetric_eqim m)
 ##| ##4: napply (symmetric_eqpseudo m)
 ##| ##5: napply symmetric_eqb8
 ##]
nqed.

nlemma eqclk_to_eq : ∀m.∀clk1,clk2.eq_clk m clk1 clk2 = true → clk1 = clk2.
 #m;
 napply (eqoption_to_eq ? (eq_quintuple …) (eqquintuple_to_eq …));
 ##[ ##1: napply eqw16_to_eq
 ##| ##2: napply eqb8_to_eq
 ##| ##3: napply (eqim_to_eq m)
 ##| ##4: napply (eqpseudo_to_eq m)
 ##| ##5: napply eqb8_to_eq
 ##]
nqed.

nlemma eq_to_eqclk : ∀m.∀clk1,clk2.(clk1 = clk2) → (eq_clk m clk1 clk2 = true).
 #m;
 napply (eq_to_eqoption ? (eq_quintuple …) (eq_to_eqquintuple …));
 ##[ ##1: napply eq_to_eqw16
 ##| ##2: napply eq_to_eqb8
 ##| ##3: napply (eq_to_eqim m)
 ##| ##4: napply (eq_to_eqpseudo m)
 ##| ##5: napply eq_to_eqb8
 ##]
nqed.

nlemma neqclk_to_neq : ∀m.∀clk1,clk2.eq_clk m clk1 clk2 = false → clk1 ≠ clk2.
 #m;
 napply (neqoption_to_neq ? (eq_quintuple …) (neqquintuple_to_neq …));
 ##[ ##1: napply neqw16_to_neq
 ##| ##2: napply neqb8_to_neq
 ##| ##3: napply (neqim_to_neq m)
 ##| ##4: napply (neqpseudo_to_neq m)
 ##| ##5: napply neqb8_to_neq
 ##]
nqed.

nlemma neq_to_neqclk : ∀m.∀clk1,clk2.(clk1 ≠ clk2) → (eq_clk m clk1 clk2 = false).
 #m;
 napply (neq_to_neqoption ? (eq_quintuple …) (neq_to_neqquintuple …));
 ##[ ##1: napply neq_to_neqw16
 ##| ##2: napply neq_to_neqb8
 ##| ##3: napply (neq_to_neqim m)
 ##| ##4: napply (neq_to_neqpseudo m)
 ##| ##5: napply neq_to_neqb8
 ##| ##6: napply decidable_w16
 ##| ##7: napply decidable_b8
 ##| ##8: napply (decidable_im m)
 ##| ##9: napply (decidable_pseudo m)
 ##| ##10: napply decidable_b8
 ##]
nqed.

nlemma decidable_clk : ∀m.∀clk1,clk2:option (aux_clk_type m).decidable (clk1 = clk2).
 #m;
 napply (decidable_option ? (decidable_quintuple …));
 ##[ ##1: napply decidable_w16
 ##| ##2: napply decidable_b8
 ##| ##3: napply (decidable_im m)
 ##| ##4: napply (decidable_pseudo m)
 ##| ##5: napply decidable_b8
 ##]
nqed.

nlemma symmetric_forallmemoryranged :
∀t.∀chk1,chk2:aux_chk_type t.∀mem1,mem2:aux_mem_type t.∀addrl.
 forall_memory_ranged t chk1 chk2 mem1 mem2 addrl =
 forall_memory_ranged t chk2 chk1 mem2 mem1 addrl.
 #t; #chk1; #chk2; #mem1; #mem2; #addrl;
 nelim addrl;
 ##[ ##1: nnormalize; napply refl_eq
 ##| ##2: #a; #l; #H;
          nchange with (
           ((eq_option byte8 eq_b8 (mem_read t mem1 chk1 a)
                                   (mem_read t mem2 chk2 a)) ⊗
           (forall_memory_ranged t chk1 chk2 mem1 mem2 l)) =
           ((eq_option byte8 eq_b8 (mem_read t mem2 chk2 a)
                                   (mem_read t mem1 chk1 a)) ⊗
           (forall_memory_ranged t chk2 chk1 mem2 mem1 l)));
           nrewrite > H;
           nrewrite > (symmetric_eqoption ? eq_b8 symmetric_eqb8 (mem_read t mem1 chk1 a) (mem_read t mem2 chk2 a));
           napply refl_eq
 ##]
nqed.

nlemma anystatus_destruct_1 :
∀m,t.∀x1,x2,x3,x4,y1,y2,y3,y4.
 mk_any_status m t x1 x2 x3 x4 = mk_any_status m t y1 y2 y3 y4 →
 x1 = y1.
 #m; #t;
 #x1; #x2; #x3; #x4;
 #y1; #y2; #y3; #y4; #H;
 nchange with (match mk_any_status m t y1 y2 y3 y4
                with [ mk_any_status a _ _ _ ⇒ x1 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma anystatus_destruct_2 :
∀m,t.∀x1,x2,x3,x4,y1,y2,y3,y4.
 mk_any_status m t x1 x2 x3 x4 = mk_any_status m t y1 y2 y3 y4 →
 x2 = y2.
 #m; #t;
 #x1; #x2; #x3; #x4;
 #y1; #y2; #y3; #y4; #H;
 nchange with (match mk_any_status m t y1 y2 y3 y4
                with [ mk_any_status _ a _ _ ⇒ x2 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma anystatus_destruct_3 :
∀m,t.∀x1,x2,x3,x4,y1,y2,y3,y4.
 mk_any_status m t x1 x2 x3 x4 = mk_any_status m t y1 y2 y3 y4 →
 x3 = y3.
 #m; #t;
 #x1; #x2; #x3; #x4;
 #y1; #y2; #y3; #y4; #H;
 nchange with (match mk_any_status m t y1 y2 y3 y4
                with [ mk_any_status _ _ a _ ⇒ x3 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

nlemma anystatus_destruct_4 :
∀m,t.∀x1,x2,x3,x4,y1,y2,y3,y4.
 mk_any_status m t x1 x2 x3 x4 = mk_any_status m t y1 y2 y3 y4 →
 x4 = y4.
 #m; #t;
 #x1; #x2; #x3; #x4;
 #y1; #y2; #y3; #y4; #H;
 nchange with (match mk_any_status m t y1 y2 y3 y4
                with [ mk_any_status _ _ _ a ⇒ x4 = a ]);
 nrewrite < H;
 nnormalize;
 napply refl_eq.
nqed.

naxiom symmetric_eqanystatus :
∀addrl:list word32.∀m:mcu_type.∀t:memory_impl.∀s1,s2:any_status m t.
 eq_anystatus m t s1 s2 addrl = eq_anystatus m t s2 s1 addrl.
(* !!! si blocca su symmetric_eqalu_HC05 *)
(* #addrl; #m; ncases m; #t; #s1;
 ##[ ##1: nelim s1; #x1; #x2; #x3; #x4;
          #s2; nelim s2; #y1; #y2; #y3; #y4;
          nchange with (
           ((eq_HC05_alu x1 y1) ⊗ (forall_memory_ranged t x3 y3 x2 y2 addrl) ⊗ (eq_clk HC05 x4 y4)) =
           ((eq_HC05_alu y1 x1) ⊗ (forall_memory_ranged t y3 x3 y2 x2 addrl) ⊗ (eq_clk HC05 y4 x4)));
           nrewrite > (symmetric_eqaluHC05 x1 y1)
 ##| ##2,3: ncases s1; #x1; #x2; #x3; #x4;
          #s2; ncases s2; #y1; #y2; #y3; #y4;
          nchange with (
           ((eq_aluHC08 x1 y1) ⊗ (forall_memory_ranged t x3 y3 x2 y2 addrl) ⊗ (eq_clk ? x4 y4)) =
           ((eq_aluHC08 y1 x1) ⊗ (forall_memory_ranged t y3 x3 y2 x2 addrl) ⊗ (eq_clk ? y4 x4)));
           nrewrite > (symmetric_eqaluHC08 x1 y1)
 ##| ##4: ncases s1; #x1; #x2; #x3; #x4;
          #s2; ncases s2; #y1; #y2; #y3; #y4;
          nchange with (
           ((eq_aluRS08 x1 y1) ⊗ (forall_memory_ranged t x3 y3 x2 y2 addrl) ⊗ (eq_clk RS08 x4 y4)) =
           ((eq_aluRS08 y1 x1) ⊗ (forall_memory_ranged t y3 x3 y2 x2 addrl) ⊗ (eq_clk RS08 y4 x4)));
           nrewrite > (symmetric_eqaluRS08 x1 y1)
 ##| ##5: ...
 ##]
 nrewrite > (symmetric_forallmemoryranged t x3 y3 x2 y2 addrl);
 nrewrite > (symmetric_eqclk ? x4 y4);
 napply refl_eq.
nqed.*)

nlemma eqanystatus_to_eq :
∀addrl:list word32.∀m:mcu_type.∀t:memory_impl.∀s1,s2:any_status m t.
 (eq_anystatus m t s1 s2 addrl = true) →
  And3 (alu m t s1 = alu m t s2) 
       (clk_desc m t s1 = clk_desc m t s2)
       ((forall_memory_ranged t (chk_desc m t s1) (chk_desc m t s2)
                                (mem_desc m t s1) (mem_desc m t s2) addrl) = true).
 #addrl; #m; #t;
 ncases m; #s1;
 ncases s1; #x1; #x2; #x3; #x4;
          #s2; ncases s2; #y1; #y2; #y3; #y4; #H;
 ##[ ##1: nchange in H:(%) with (
           ((eq_HC05_alu x1 y1) ⊗ (forall_memory_ranged t x3 y3 x2 y2 addrl) ⊗ (eq_clk ? x4 y4)) = true);
           nrewrite > (eqaluHC05_to_eq … (andb_true_true_l … (andb_true_true_l … H)))
 ##| ##2,3: nchange in H:(%) with (
            ((eq_HC08_alu x1 y1) ⊗ (forall_memory_ranged t x3 y3 x2 y2 addrl) ⊗ (eq_clk ? x4 y4)) = true);
            nrewrite > (eqaluHC08_to_eq … (andb_true_true_l … (andb_true_true_l … H)))
 ##| ##4: nchange in H:(%) with (
           ((eq_RS08_alu x1 y1) ⊗ (forall_memory_ranged t x3 y3 x2 y2 addrl) ⊗ (eq_clk ? x4 y4)) = true);
          nrewrite > (eqaluRS08_to_eq … (andb_true_true_l … (andb_true_true_l … H)))
 ##| ##5: nchange in H:(%) with (
           ((eq_IP2022_alu x1 y1) ⊗ (forall_memory_ranged t x3 y3 x2 y2 addrl) ⊗ (eq_clk ? x4 y4)) = true);
          nrewrite > (eqaluIP2022_to_eq … (andb_true_true_l … (andb_true_true_l … H)))
 ##]
 nchange with (And3 (y1 = y1) (x4 = y4) (forall_memory_ranged t x3 y3 x2 y2 addrl = true));
 nrewrite > (andb_true_true_r … (andb_true_true_l … H));
 nrewrite > (eqclk_to_eq … (andb_true_true_r … H));
 napply (conj3 … (refl_eq ? y1) (refl_eq ? y4) (refl_eq ? true)).
nqed.

naxiom eq_to_eqanystatus :
∀addrl:list word32.∀m:mcu_type.∀t:memory_impl.∀s1,s2:any_status m t.
 (alu m t s1 = alu m t s2) →
 (clk_desc m t s1 = clk_desc m t s2) →
 ((forall_memory_ranged t (chk_desc m t s1) (chk_desc m t s2)
                            (mem_desc m t s1) (mem_desc m t s2) addrl) = true) →
 (eq_anystatus m t s1 s2 addrl = true).
(* !!! si blocca su symmetric_eqalu_HC05 *)
(* #addrl; #m; #t;
 ncases m; #s1; ncases s1; #x1; #x2; #x3; #x4;
 #s2; ncases s2; #y1; #y2; #y3; #y4; #H; #H1; #H2;
 ##[ ##1: nchange with (((eq_HC05_alu x1 y1) ⊗ (forall_memory_ranged t x3 y3 x2 y2 addrl) ⊗ (eq_clk ? x4 y4)) = true);
          nchange in H:(%) with (x1 = y1);
          nrewrite > H; 
          nrewrite > (eq_to_eqaluHC05 y1 y1 (refl_eq …))
 ##| ##2,3: nchange with (((eq_HC08_alu x1 y1) ⊗ (forall_memory_ranged t x3 y3 x2 y2 addrl) ⊗ (eq_clk ? x4 y4)) = true);
            nchange in H:(%) with (x1 = y1);
            nrewrite > H; 
            nrewrite > (eq_to_eqaluHC08 y1 y1 (refl_eq …))
 ##| ##4: nchange with (((eq_RS08_alu x1 y1) ⊗ (forall_memory_ranged t x3 y3 x2 y2 addrl) ⊗ (eq_clk ? x4 y4)) = true);
          nchange in H:(%) with (x1 = y1);
          nrewrite > H; 
          nrewrite > (eq_to_eqaluRS08 y1 y1 (refl_eq …))
 ##| ##5: ...
 ##]
 nchange in H2:(%) with (forall_memory_ranged t x3 y3 x2 y2 addrl = true);
 nrewrite > H2;
 nchange in H1:(%) with (x4 = y4);
 nrewrite > H1;
 nrewrite > (eq_to_eqclk ? y4 y4 (refl_eq …));
 nnormalize;
 napply refl_eq.
nqed.*)
