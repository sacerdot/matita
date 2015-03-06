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

include "basic_1/flt/defs.ma".

theorem flt_wf__q_ind:
 \forall (P: ((C \to (T \to Prop)))).(((\forall (n: nat).((\lambda (P0: ((C 
\to (T \to Prop)))).(\lambda (n0: nat).(\forall (c: C).(\forall (t: T).((eq 
nat (fweight c t) n0) \to (P0 c t)))))) P n))) \to (\forall (c: C).(\forall 
(t: T).(P c t))))
\def
 let Q \def (\lambda (P: ((C \to (T \to Prop)))).(\lambda (n: nat).(\forall 
(c: C).(\forall (t: T).((eq nat (fweight c t) n) \to (P c t)))))) in (\lambda 
(P: ((C \to (T \to Prop)))).(\lambda (H: ((\forall (n: nat).(\forall (c: 
C).(\forall (t: T).((eq nat (fweight c t) n) \to (P c t))))))).(\lambda (c: 
C).(\lambda (t: T).(H (fweight c t) c t (refl_equal nat (fweight c t))))))).

theorem flt_wf_ind:
 \forall (P: ((C \to (T \to Prop)))).(((\forall (c2: C).(\forall (t2: 
T).(((\forall (c1: C).(\forall (t1: T).((flt c1 t1 c2 t2) \to (P c1 t1))))) 
\to (P c2 t2))))) \to (\forall (c: C).(\forall (t: T).(P c t))))
\def
 let Q \def (\lambda (P: ((C \to (T \to Prop)))).(\lambda (n: nat).(\forall 
(c: C).(\forall (t: T).((eq nat (fweight c t) n) \to (P c t)))))) in (\lambda 
(P: ((C \to (T \to Prop)))).(\lambda (H: ((\forall (c2: C).(\forall (t2: 
T).(((\forall (c1: C).(\forall (t1: T).((flt c1 t1 c2 t2) \to (P c1 t1))))) 
\to (P c2 t2)))))).(\lambda (c: C).(\lambda (t: T).(flt_wf__q_ind P (\lambda 
(n: nat).(lt_wf_ind n (Q P) (\lambda (n0: nat).(\lambda (H0: ((\forall (m: 
nat).((lt m n0) \to (Q P m))))).(\lambda (c0: C).(\lambda (t0: T).(\lambda 
(H1: (eq nat (fweight c0 t0) n0)).(let H2 \def (eq_ind_r nat n0 (\lambda (n1: 
nat).(\forall (m: nat).((lt m n1) \to (\forall (c1: C).(\forall (t1: T).((eq 
nat (fweight c1 t1) m) \to (P c1 t1))))))) H0 (fweight c0 t0) H1) in (H c0 t0 
(\lambda (c1: C).(\lambda (t1: T).(\lambda (H3: (flt c1 t1 c0 t0)).(H2 
(fweight c1 t1) H3 c1 t1 (refl_equal nat (fweight c1 t1))))))))))))))) c 
t))))).

