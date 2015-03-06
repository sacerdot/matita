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

(* This file was automatically generated: do not edit *********************)

include "basic_1/tlist/defs.ma".

theorem theads_tapp:
 \forall (k: K).(\forall (v: T).(\forall (t: T).(\forall (vs: TList).(eq T 
(THeads k (TApp vs v) t) (THeads k vs (THead k v t))))))
\def
 \lambda (k: K).(\lambda (v: T).(\lambda (t: T).(\lambda (vs: 
TList).(TList_ind (\lambda (t0: TList).(eq T (THeads k (TApp t0 v) t) (THeads 
k t0 (THead k v t)))) (refl_equal T (THead k v t)) (\lambda (t0: T).(\lambda 
(t1: TList).(\lambda (H: (eq T (THeads k (TApp t1 v) t) (THeads k t1 (THead k 
v t)))).(eq_ind T (THeads k (TApp t1 v) t) (\lambda (t2: T).(eq T (THead k t0 
(THeads k (TApp t1 v) t)) (THead k t0 t2))) (refl_equal T (THead k t0 (THeads 
k (TApp t1 v) t))) (THeads k t1 (THead k v t)) H)))) vs)))).

theorem tcons_tapp_ex:
 \forall (ts1: TList).(\forall (t1: T).(ex2_2 TList T (\lambda (ts2: 
TList).(\lambda (t2: T).(eq TList (TCons t1 ts1) (TApp ts2 t2)))) (\lambda 
(ts2: TList).(\lambda (_: T).(eq nat (tslen ts1) (tslen ts2))))))
\def
 \lambda (ts1: TList).(TList_ind (\lambda (t: TList).(\forall (t1: T).(ex2_2 
TList T (\lambda (ts2: TList).(\lambda (t2: T).(eq TList (TCons t1 t) (TApp 
ts2 t2)))) (\lambda (ts2: TList).(\lambda (_: T).(eq nat (tslen t) (tslen 
ts2))))))) (\lambda (t1: T).(ex2_2_intro TList T (\lambda (ts2: 
TList).(\lambda (t2: T).(eq TList (TCons t1 TNil) (TApp ts2 t2)))) (\lambda 
(ts2: TList).(\lambda (_: T).(eq nat O (tslen ts2)))) TNil t1 (refl_equal 
TList (TApp TNil t1)) (refl_equal nat (tslen TNil)))) (\lambda (t: 
T).(\lambda (t0: TList).(\lambda (H: ((\forall (t1: T).(ex2_2 TList T 
(\lambda (ts2: TList).(\lambda (t2: T).(eq TList (TCons t1 t0) (TApp ts2 
t2)))) (\lambda (ts2: TList).(\lambda (_: T).(eq nat (tslen t0) (tslen 
ts2)))))))).(\lambda (t1: T).(let H_x \def (H t) in (let H0 \def H_x in 
(ex2_2_ind TList T (\lambda (ts2: TList).(\lambda (t2: T).(eq TList (TCons t 
t0) (TApp ts2 t2)))) (\lambda (ts2: TList).(\lambda (_: T).(eq nat (tslen t0) 
(tslen ts2)))) (ex2_2 TList T (\lambda (ts2: TList).(\lambda (t2: T).(eq 
TList (TCons t1 (TCons t t0)) (TApp ts2 t2)))) (\lambda (ts2: TList).(\lambda 
(_: T).(eq nat (S (tslen t0)) (tslen ts2))))) (\lambda (x0: TList).(\lambda 
(x1: T).(\lambda (H1: (eq TList (TCons t t0) (TApp x0 x1))).(\lambda (H2: (eq 
nat (tslen t0) (tslen x0))).(eq_ind_r TList (TApp x0 x1) (\lambda (t2: 
TList).(ex2_2 TList T (\lambda (ts2: TList).(\lambda (t3: T).(eq TList (TCons 
t1 t2) (TApp ts2 t3)))) (\lambda (ts2: TList).(\lambda (_: T).(eq nat (S 
(tslen t0)) (tslen ts2)))))) (eq_ind_r nat (tslen x0) (\lambda (n: 
nat).(ex2_2 TList T (\lambda (ts2: TList).(\lambda (t2: T).(eq TList (TCons 
t1 (TApp x0 x1)) (TApp ts2 t2)))) (\lambda (ts2: TList).(\lambda (_: T).(eq 
nat (S n) (tslen ts2)))))) (ex2_2_intro TList T (\lambda (ts2: 
TList).(\lambda (t2: T).(eq TList (TCons t1 (TApp x0 x1)) (TApp ts2 t2)))) 
(\lambda (ts2: TList).(\lambda (_: T).(eq nat (S (tslen x0)) (tslen ts2)))) 
(TCons t1 x0) x1 (refl_equal TList (TApp (TCons t1 x0) x1)) (refl_equal nat 
(tslen (TCons t1 x0)))) (tslen t0) H2) (TCons t t0) H1))))) H0))))))) ts1).

