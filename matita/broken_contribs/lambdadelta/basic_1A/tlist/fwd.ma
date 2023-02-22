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

include "basic_1A/tlist/props.ma".

fact tslt_wf__q_ind:
 \forall (P: ((TList \to Prop))).(((\forall (n: nat).((\lambda (P0: ((TList 
\to Prop))).(\lambda (n0: nat).(\forall (ts: TList).((eq nat (tslen ts) n0) 
\to (P0 ts))))) P n))) \to (\forall (ts: TList).(P ts)))
\def
 let Q \def (\lambda (P: ((TList \to Prop))).(\lambda (n: nat).(\forall (ts: 
TList).((eq nat (tslen ts) n) \to (P ts))))) in (\lambda (P: ((TList \to 
Prop))).(\lambda (H: ((\forall (n: nat).(\forall (ts: TList).((eq nat (tslen 
ts) n) \to (P ts)))))).(\lambda (ts: TList).(H (tslen ts) ts (refl_equal nat 
(tslen ts)))))).

lemma tslt_wf_ind:
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

lemma tlist_ind_rev:
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

