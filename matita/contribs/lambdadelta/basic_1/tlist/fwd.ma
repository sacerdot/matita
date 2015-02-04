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

include "basic_1/tlist/props.ma".

theorem tslt_wf__q_ind:
 \forall (P: ((TList \to Prop))).(((\forall (n: nat).((\lambda (P0: ((TList 
\to Prop))).(\lambda (n0: nat).(\forall (ts: TList).((eq nat (tslen ts) n0) 
\to (P0 ts))))) P n))) \to (\forall (ts: TList).(P ts)))
\def
 let Q \def (\lambda (P: ((TList \to Prop))).(\lambda (n: nat).(\forall (ts: 
TList).((eq nat (tslen ts) n) \to (P ts))))) in (\lambda (P: ((TList \to 
Prop))).(\lambda (H: ((\forall (n: nat).(\forall (ts: TList).((eq nat (tslen 
ts) n) \to (P ts)))))).(\lambda (ts: TList).(let TMP_1 \def (tslen ts) in 
(let TMP_2 \def (tslen ts) in (let TMP_3 \def (refl_equal nat TMP_2) in (H 
TMP_1 ts TMP_3))))))).

theorem tslt_wf_ind:
 \forall (P: ((TList \to Prop))).(((\forall (ts2: TList).(((\forall (ts1: 
TList).((tslt ts1 ts2) \to (P ts1)))) \to (P ts2)))) \to (\forall (ts: 
TList).(P ts)))
\def
 let Q \def (\lambda (P: ((TList \to Prop))).(\lambda (n: nat).(\forall (ts: 
TList).((eq nat (tslen ts) n) \to (P ts))))) in (\lambda (P: ((TList \to 
Prop))).(\lambda (H: ((\forall (ts2: TList).(((\forall (ts1: TList).((lt 
(tslen ts1) (tslen ts2)) \to (P ts1)))) \to (P ts2))))).(\lambda (ts: 
TList).(let TMP_1 \def (\lambda (t: TList).(P t)) in (let TMP_11 \def 
(\lambda (n: nat).(let TMP_2 \def (\lambda (t: TList).(P t)) in (let TMP_3 
\def (Q TMP_2) in (let TMP_10 \def (\lambda (n0: nat).(\lambda (H0: ((\forall 
(m: nat).((lt m n0) \to (Q (\lambda (t: TList).(P t)) m))))).(\lambda (ts0: 
TList).(\lambda (H1: (eq nat (tslen ts0) n0)).(let TMP_4 \def (\lambda (n1: 
nat).(\forall (m: nat).((lt m n1) \to (\forall (ts1: TList).((eq nat (tslen 
ts1) m) \to (P ts1)))))) in (let TMP_5 \def (tslen ts0) in (let H2 \def 
(eq_ind_r nat n0 TMP_4 H0 TMP_5 H1) in (let TMP_9 \def (\lambda (ts1: 
TList).(\lambda (H3: (lt (tslen ts1) (tslen ts0))).(let TMP_6 \def (tslen 
ts1) in (let TMP_7 \def (tslen ts1) in (let TMP_8 \def (refl_equal nat TMP_7) 
in (H2 TMP_6 H3 ts1 TMP_8)))))) in (H ts0 TMP_9))))))))) in (lt_wf_ind n 
TMP_3 TMP_10))))) in (tslt_wf__q_ind TMP_1 TMP_11 ts)))))).

theorem tlist_ind_rev:
 \forall (P: ((TList \to Prop))).((P TNil) \to (((\forall (ts: 
TList).(\forall (t: T).((P ts) \to (P (TApp ts t)))))) \to (\forall (ts: 
TList).(P ts))))
\def
 \lambda (P: ((TList \to Prop))).(\lambda (H: (P TNil)).(\lambda (H0: 
((\forall (ts: TList).(\forall (t: T).((P ts) \to (P (TApp ts 
t))))))).(\lambda (ts: TList).(let TMP_1 \def (\lambda (t: TList).(P t)) in 
(let TMP_28 \def (\lambda (ts2: TList).(let TMP_2 \def (\lambda (t: 
TList).(((\forall (ts1: TList).((tslt ts1 t) \to (P ts1)))) \to (P t))) in 
(let TMP_3 \def (\lambda (_: ((\forall (ts1: TList).((tslt ts1 TNil) \to (P 
ts1))))).H) in (let TMP_27 \def (\lambda (t: T).(\lambda (t0: TList).(\lambda 
(_: ((((\forall (ts1: TList).((tslt ts1 t0) \to (P ts1)))) \to (P 
t0)))).(\lambda (H2: ((\forall (ts1: TList).((tslt ts1 (TCons t t0)) \to (P 
ts1))))).(let H_x \def (tcons_tapp_ex t0 t) in (let H3 \def H_x in (let TMP_6 
\def (\lambda (ts3: TList).(\lambda (t2: T).(let TMP_4 \def (TCons t t0) in 
(let TMP_5 \def (TApp ts3 t2) in (eq TList TMP_4 TMP_5))))) in (let TMP_9 
\def (\lambda (ts3: TList).(\lambda (_: T).(let TMP_7 \def (tslen t0) in (let 
TMP_8 \def (tslen ts3) in (eq nat TMP_7 TMP_8))))) in (let TMP_10 \def (TCons 
t t0) in (let TMP_11 \def (P TMP_10) in (let TMP_26 \def (\lambda (x0: 
TList).(\lambda (x1: T).(\lambda (H4: (eq TList (TCons t t0) (TApp x0 
x1))).(\lambda (H5: (eq nat (tslen t0) (tslen x0))).(let TMP_12 \def (TApp x0 
x1) in (let TMP_13 \def (\lambda (t1: TList).(P t1)) in (let TMP_14 \def 
(tslen t0) in (let TMP_17 \def (\lambda (n: nat).(let TMP_15 \def (TCons t 
t0) in (let TMP_16 \def (tslen TMP_15) in (lt n TMP_16)))) in (let TMP_18 
\def (TCons t t0) in (let TMP_19 \def (tslen TMP_18) in (let TMP_20 \def 
(le_n TMP_19) in (let TMP_21 \def (tslen x0) in (let TMP_22 \def (eq_ind nat 
TMP_14 TMP_17 TMP_20 TMP_21 H5) in (let TMP_23 \def (H2 x0 TMP_22) in (let 
TMP_24 \def (H0 x0 x1 TMP_23) in (let TMP_25 \def (TCons t t0) in (eq_ind_r 
TList TMP_12 TMP_13 TMP_24 TMP_25 H4))))))))))))))))) in (ex2_2_ind TList T 
TMP_6 TMP_9 TMP_11 TMP_26 H3)))))))))))) in (TList_ind TMP_2 TMP_3 TMP_27 
ts2))))) in (tslt_wf_ind TMP_1 TMP_28 ts)))))).

