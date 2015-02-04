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

include "basic_1/tlt/defs.ma".

theorem tlt_wf__q_ind:
 \forall (P: ((T \to Prop))).(((\forall (n: nat).((\lambda (P0: ((T \to 
Prop))).(\lambda (n0: nat).(\forall (t: T).((eq nat (weight t) n0) \to (P0 
t))))) P n))) \to (\forall (t: T).(P t)))
\def
 let Q \def (\lambda (P: ((T \to Prop))).(\lambda (n: nat).(\forall (t: 
T).((eq nat (weight t) n) \to (P t))))) in (\lambda (P: ((T \to 
Prop))).(\lambda (H: ((\forall (n: nat).(\forall (t: T).((eq nat (weight t) 
n) \to (P t)))))).(\lambda (t: T).(let TMP_1 \def (weight t) in (let TMP_2 
\def (weight t) in (let TMP_3 \def (refl_equal nat TMP_2) in (H TMP_1 t 
TMP_3))))))).

theorem tlt_wf_ind:
 \forall (P: ((T \to Prop))).(((\forall (t: T).(((\forall (v: T).((tlt v t) 
\to (P v)))) \to (P t)))) \to (\forall (t: T).(P t)))
\def
 let Q \def (\lambda (P: ((T \to Prop))).(\lambda (n: nat).(\forall (t: 
T).((eq nat (weight t) n) \to (P t))))) in (\lambda (P: ((T \to 
Prop))).(\lambda (H: ((\forall (t: T).(((\forall (v: T).((lt (weight v) 
(weight t)) \to (P v)))) \to (P t))))).(\lambda (t: T).(let TMP_1 \def 
(\lambda (t0: T).(P t0)) in (let TMP_11 \def (\lambda (n: nat).(let TMP_2 
\def (\lambda (t0: T).(P t0)) in (let TMP_3 \def (Q TMP_2) in (let TMP_10 
\def (\lambda (n0: nat).(\lambda (H0: ((\forall (m: nat).((lt m n0) \to (Q 
(\lambda (t0: T).(P t0)) m))))).(\lambda (t0: T).(\lambda (H1: (eq nat 
(weight t0) n0)).(let TMP_4 \def (\lambda (n1: nat).(\forall (m: nat).((lt m 
n1) \to (\forall (t1: T).((eq nat (weight t1) m) \to (P t1)))))) in (let 
TMP_5 \def (weight t0) in (let H2 \def (eq_ind_r nat n0 TMP_4 H0 TMP_5 H1) in 
(let TMP_9 \def (\lambda (v: T).(\lambda (H3: (lt (weight v) (weight 
t0))).(let TMP_6 \def (weight v) in (let TMP_7 \def (weight v) in (let TMP_8 
\def (refl_equal nat TMP_7) in (H2 TMP_6 H3 v TMP_8)))))) in (H t0 
TMP_9))))))))) in (lt_wf_ind n TMP_3 TMP_10))))) in (tlt_wf__q_ind TMP_1 
TMP_11 t)))))).

