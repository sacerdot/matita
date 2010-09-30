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

include "Basic-1/tlist/defs.ma".

theorem tslt_wf__q_ind:
 \forall (P: ((TList \to Prop))).(((\forall (n: nat).((\lambda (P0: ((TList 
\to Prop))).(\lambda (n0: nat).(\forall (ts: TList).((eq nat (tslen ts) n0) 
\to (P0 ts))))) P n))) \to (\forall (ts: TList).(P ts)))
\def
 let Q \def (\lambda (P: ((TList \to Prop))).(\lambda (n: nat).(\forall (ts: 
TList).((eq nat (tslen ts) n) \to (P ts))))) in (\lambda (P: ((TList \to 
Prop))).(\lambda (H: ((\forall (n: nat).(\forall (ts: TList).((eq nat (tslen 
ts) n) \to (P ts)))))).(\lambda (ts: TList).(H (tslen ts) ts (refl_equal nat 
(tslen ts)))))).
(* COMMENTS
Initial nodes: 61
END *)

theorem tslt_wf_ind:
 \forall (P: ((TList \to Prop))).(((\forall (ts2: TList).(((\forall (ts1: 
TList).((tslt ts1 ts2) \to (P ts1)))) \to (P ts2)))) \to (\forall (ts: 
TList).(P ts)))
\def
 let Q \def (\lambda (P: ((TList \to Prop))).(\lambda (n: nat).(\forall (ts: 
TList).((eq nat (tslen ts) n) \to (P ts))))) in (\lambda (P: ((TList \to 
Prop))).(\lambda (H: ((\forall (ts2: TList).(((\forall (ts1: TList).((lt 
(tslen ts1) (tslen ts2)) \to (P ts1)))) \to (P ts2))))).(\lambda (ts: 
TList).(tslt_wf__q_ind (\lambda (t: TList).(P t)) (\lambda (n: 
nat).(lt_wf_ind n (Q (\lambda (t: TList).(P t))) (\lambda (n0: nat).(\lambda 
(H0: ((\forall (m: nat).((lt m n0) \to (Q (\lambda (t: TList).(P t)) 
m))))).(\lambda (ts0: TList).(\lambda (H1: (eq nat (tslen ts0) n0)).(let H2 
\def (eq_ind_r nat n0 (\lambda (n1: nat).(\forall (m: nat).((lt m n1) \to 
(\forall (ts1: TList).((eq nat (tslen ts1) m) \to (P ts1)))))) H0 (tslen ts0) 
H1) in (H ts0 (\lambda (ts1: TList).(\lambda (H3: (lt (tslen ts1) (tslen 
ts0))).(H2 (tslen ts1) H3 ts1 (refl_equal nat (tslen ts1))))))))))))) ts)))).
(* COMMENTS
Initial nodes: 179
END *)

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
(* COMMENTS
Initial nodes: 175
END *)

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
(* COMMENTS
Initial nodes: 503
END *)

theorem tlist_ind_rev:
 \forall (P: ((TList \to Prop))).((P TNil) \to (((\forall (ts: 
TList).(\forall (t: T).((P ts) \to (P (TApp ts t)))))) \to (\forall (ts: 
TList).(P ts))))
\def
 \lambda (P: ((TList \to Prop))).(\lambda (H: (P TNil)).(\lambda (H0: 
((\forall (ts: TList).(\forall (t: T).((P ts) \to (P (TApp ts 
t))))))).(\lambda (ts: TList).(tslt_wf_ind (\lambda (t: TList).(P t)) 
(\lambda (ts2: TList).(TList_ind (\lambda (t: TList).(((\forall (ts1: 
TList).((tslt ts1 t) \to (P ts1)))) \to (P t))) (\lambda (_: ((\forall (ts1: 
TList).((tslt ts1 TNil) \to (P ts1))))).H) (\lambda (t: T).(\lambda (t0: 
TList).(\lambda (_: ((((\forall (ts1: TList).((tslt ts1 t0) \to (P ts1)))) 
\to (P t0)))).(\lambda (H2: ((\forall (ts1: TList).((tslt ts1 (TCons t t0)) 
\to (P ts1))))).(let H_x \def (tcons_tapp_ex t0 t) in (let H3 \def H_x in 
(ex2_2_ind TList T (\lambda (ts3: TList).(\lambda (t2: T).(eq TList (TCons t 
t0) (TApp ts3 t2)))) (\lambda (ts3: TList).(\lambda (_: T).(eq nat (tslen t0) 
(tslen ts3)))) (P (TCons t t0)) (\lambda (x0: TList).(\lambda (x1: 
T).(\lambda (H4: (eq TList (TCons t t0) (TApp x0 x1))).(\lambda (H5: (eq nat 
(tslen t0) (tslen x0))).(eq_ind_r TList (TApp x0 x1) (\lambda (t1: TList).(P 
t1)) (H0 x0 x1 (H2 x0 (eq_ind nat (tslen t0) (\lambda (n: nat).(lt n (tslen 
(TCons t t0)))) (le_n (tslen (TCons t t0))) (tslen x0) H5))) (TCons t t0) 
H4))))) H3))))))) ts2)) ts)))).
(* COMMENTS
Initial nodes: 273
END *)

