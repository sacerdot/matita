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

include "emulator/status/status_base.ma".

(* *********************************** *)
(* STATUS INTERNO DEL PROCESSORE (ALU) *)
(* *********************************** *)

nlemma symmetric_forallmemoryranged :
∀t.∀chk1,chk2:aux_chk_type t.∀mem1,mem2:aux_mem_type t.∀sel.∀addrl.
 forall_memory_ranged t chk1 chk2 mem1 mem2 sel addrl =
 forall_memory_ranged t chk2 chk1 mem2 mem1 sel addrl.
 #t; #chk1; #chk2; #mem1; #mem2; #sel; #addrl;
 nelim addrl;
 ##[ ##1: nnormalize; napply refl_eq
 ##| ##2: #a; #l; #H;
          nchange with (
           ((eqc ? (mem_read t mem1 chk1 sel a)
                   (mem_read t mem2 chk2 sel a)) ⊗
           (forall_memory_ranged t chk1 chk2 mem1 mem2 sel l)) =
           ((eqc ? (mem_read t mem2 chk2 sel a)
                   (mem_read t mem1 chk1 sel a)) ⊗
           (forall_memory_ranged t chk2 chk1 mem2 mem1 sel l)));
           nrewrite > H;
           nrewrite > (symmetric_eqc ? … (mem_read t mem1 chk1 sel a) (mem_read t mem2 chk2 sel a));
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

nlemma eq_to_eqanystatus : ∀m,t.∀s1,s2:any_status m t.s1 = s2 → eq_anystatus m t s1 s2 = true.
 #m; #t;
 #s1; ncases s1; #alu1; #mem1; #chk1; #clk1;
 #s2; ncases s2; #alu2; #mem2; #chk2; #clk2;
 #H;
 nrewrite > (anystatus_destruct_1 … H);
 nrewrite > (anystatus_destruct_2 … H);
 nrewrite > (anystatus_destruct_3 … H);
 nrewrite > (anystatus_destruct_4 … H);
 nchange with (
 ((eqc ? alu2 alu2) ⊗ (eqc ? mem2 mem2) ⊗ (eqc ? chk2 chk2) ⊗ (eqc ? clk2 clk2)) = true);
 nrewrite > (eq_to_eqc ? alu2 alu2 (refl_eq …));
 nrewrite > (eq_to_eqc ? mem2 mem2 (refl_eq …));
 nrewrite > (eq_to_eqc ? chk2 chk2 (refl_eq …));
 nrewrite > (eq_to_eqc ? clk2 clk2 (refl_eq …));
 napply refl_eq.
nqed.

nlemma neqanystatus_to_neq : ∀m,t.∀s1,s2:any_status m t.eq_anystatus m t s1 s2 = false → s1 ≠ s2.
 #m; #t; #s1; #s2; #H;
 napply (not_to_not (s1 = s2) (eq_anystatus m t s1 s2 = true) …);
 ##[ ##1: napply (eq_to_eqanystatus m t s1 s2)
 ##| ##2: napply (eqfalse_to_neqtrue … H)
 ##]
nqed.

nlemma eqanystatus_to_eq : ∀m,t.∀s1,s2:any_status m t.eq_anystatus m t s1 s2 = true → s1 = s2.
 #m; #t;
 #s1; ncases s1; #alu1; #mem1; #chk1; #clk1;
 #s2; ncases s2; #alu2; #mem2; #chk2; #clk2;
 nchange with (
 ((eqc ? alu1 alu2) ⊗ (eqc ? mem1 mem2) ⊗ (eqc ? chk1 chk2) ⊗ (eqc ? clk1 clk2)) = true → ?);
 #H;
 nrewrite > (eqc_to_eq … (andb_true_true_r … H));
 nletin H1 ≝ (andb_true_true_l … H);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H1));
 nletin H2 ≝ (andb_true_true_l … H1);
 nrewrite > (eqc_to_eq … (andb_true_true_r … H2));
 nrewrite > (eqc_to_eq … (andb_true_true_l … H2));
 napply refl_eq.
nqed.

nlemma neq_to_neqanystatus : ∀m,t.∀s1,s2:any_status m t.s1 ≠ s2 → eq_anystatus m t s1 s2 = false.
 #m; #t; #s1; #s2; #H;
 napply (neqtrue_to_eqfalse (eq_anystatus m t s1 s2));
 napply (not_to_not (eq_anystatus m t s1 s2 = true) (s1 = s2) ? H);
 napply (eqanystatus_to_eq m t s1 s2).
nqed.

nlemma decidable_anystatus : ∀m,t.∀x,y:any_status m t.decidable (x = y).
 #m; #t; #x; #y; nnormalize;
 napply (or2_elim (eq_anystatus m t x y = true) (eq_anystatus m t x y = false) ? (decidable_bexpr ?));
 ##[ ##1: #H; napply (or2_intro1 (x = y) (x ≠ y) (eqanystatus_to_eq … H))
 ##| ##2: #H; napply (or2_intro2 (x = y) (x ≠ y) (neqanystatus_to_neq … H))
 ##]
nqed.

nlemma symmetric_eqanystatus : ∀m,t.symmetricT (any_status m t) bool (eq_anystatus m t).
 #m; #t;
 #s1; ncases s1; #alu1; #mem1; #chk1; #clk1;
 #s2; ncases s2; #alu2; #mem2; #chk2; #clk2;
 nchange with (
 ((eqc ? alu1 alu2) ⊗ (eqc ? mem1 mem2) ⊗ (eqc ? chk1 chk2) ⊗ (eqc ? clk1 clk2)) =
 ((eqc ? alu2 alu1) ⊗ (eqc ? mem2 mem1) ⊗ (eqc ? chk2 chk1) ⊗ (eqc ? clk2 clk1)));
 nrewrite > (symmetric_eqc … alu1 alu2);
 nrewrite > (symmetric_eqc … mem1 mem2);
 nrewrite > (symmetric_eqc … chk1 chk2);
 nrewrite > (symmetric_eqc … clk1 clk2);
 napply refl_eq.
nqed.

nlemma anystatus_is_comparable : mcu_type → memory_impl → comparable.
 #m; #t; @ (any_status m t)
  ##[ napply (mk_any_status m t (zeroc ?) (zeroc ?) (zeroc ?) (zeroc ?))
  ##| napply forall_anystatus
  ##| napply eq_anystatus
  ##| napply eqanystatus_to_eq
  ##| napply eq_to_eqanystatus
  ##| napply neqanystatus_to_neq
  ##| napply neq_to_neqanystatus
  ##| napply decidable_anystatus
  ##| napply symmetric_eqanystatus
  ##]
nqed.

unification hint 0 ≔ M:mcu_type, T:memory_impl ⊢
 carr (anystatus_is_comparable M T) ≡ any_status M T.
