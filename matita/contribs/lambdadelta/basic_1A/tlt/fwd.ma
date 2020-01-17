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

include "basic_1A/tlt/defs.ma".

fact tlt_wf__q_ind:
 \forall (P: ((T \to Prop))).(((\forall (n: nat).((\lambda (P0: ((T \to 
Prop))).(\lambda (n0: nat).(\forall (t: T).((eq nat (weight t) n0) \to (P0 
t))))) P n))) \to (\forall (t: T).(P t)))
\def
 let Q \def (\lambda (P: ((T \to Prop))).(\lambda (n: nat).(\forall (t: 
T).((eq nat (weight t) n) \to (P t))))) in (\lambda (P: ((T \to 
Prop))).(\lambda (H: ((\forall (n: nat).(\forall (t: T).((eq nat (weight t) 
n) \to (P t)))))).(\lambda (t: T).(H (weight t) t (refl_equal nat (weight 
t)))))).

lemma tlt_wf_ind:
 \forall (P: ((T \to Prop))).(((\forall (t: T).(((\forall (v: T).((tlt v t) 
\to (P v)))) \to (P t)))) \to (\forall (t: T).(P t)))
\def
 let Q \def (\lambda (P: ((T \to Prop))).(\lambda (n: nat).(\forall (t: 
T).((eq nat (weight t) n) \to (P t))))) in (\lambda (P: ((T \to 
Prop))).(\lambda (H: ((\forall (t: T).(((\forall (v: T).((lt (weight v) 
(weight t)) \to (P v)))) \to (P t))))).(\lambda (t: T).(tlt_wf__q_ind 
(\lambda (t0: T).(P t0)) (\lambda (n: nat).(lt_wf_ind n (Q (\lambda (t0: 
T).(P t0))) (\lambda (n0: nat).(\lambda (H0: ((\forall (m: nat).((lt m n0) 
\to (Q (\lambda (t0: T).(P t0)) m))))).(\lambda (t0: T).(\lambda (H1: (eq nat 
(weight t0) n0)).(let H2 \def (eq_ind_r nat n0 (\lambda (n1: nat).(\forall 
(m: nat).((lt m n1) \to (\forall (t1: T).((eq nat (weight t1) m) \to (P 
t1)))))) H0 (weight t0) H1) in (H t0 (\lambda (v: T).(\lambda (H3: (lt 
(weight v) (weight t0))).(H2 (weight v) H3 v (refl_equal nat (weight 
v))))))))))))) t)))).

