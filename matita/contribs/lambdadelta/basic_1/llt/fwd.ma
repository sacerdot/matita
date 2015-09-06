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

include "basic_1/llt/defs.ma".

fact llt_wf__q_ind:
 \forall (P: ((A \to Prop))).(((\forall (n: nat).((\lambda (P0: ((A \to 
Prop))).(\lambda (n0: nat).(\forall (a: A).((eq nat (lweight a) n0) \to (P0 
a))))) P n))) \to (\forall (a: A).(P a)))
\def
 let Q \def (\lambda (P: ((A \to Prop))).(\lambda (n: nat).(\forall (a: 
A).((eq nat (lweight a) n) \to (P a))))) in (\lambda (P: ((A \to 
Prop))).(\lambda (H: ((\forall (n: nat).(\forall (a: A).((eq nat (lweight a) 
n) \to (P a)))))).(\lambda (a: A).(H (lweight a) a (refl_equal nat (lweight 
a)))))).

lemma llt_wf_ind:
 \forall (P: ((A \to Prop))).(((\forall (a2: A).(((\forall (a1: A).((llt a1 
a2) \to (P a1)))) \to (P a2)))) \to (\forall (a: A).(P a)))
\def
 let Q \def (\lambda (P: ((A \to Prop))).(\lambda (n: nat).(\forall (a: 
A).((eq nat (lweight a) n) \to (P a))))) in (\lambda (P: ((A \to 
Prop))).(\lambda (H: ((\forall (a2: A).(((\forall (a1: A).((lt (lweight a1) 
(lweight a2)) \to (P a1)))) \to (P a2))))).(\lambda (a: A).(llt_wf__q_ind 
(\lambda (a0: A).(P a0)) (\lambda (n: nat).(lt_wf_ind n (Q (\lambda (a0: 
A).(P a0))) (\lambda (n0: nat).(\lambda (H0: ((\forall (m: nat).((lt m n0) 
\to (Q (\lambda (a0: A).(P a0)) m))))).(\lambda (a0: A).(\lambda (H1: (eq nat 
(lweight a0) n0)).(let H2 \def (eq_ind_r nat n0 (\lambda (n1: nat).(\forall 
(m: nat).((lt m n1) \to (\forall (a1: A).((eq nat (lweight a1) m) \to (P 
a1)))))) H0 (lweight a0) H1) in (H a0 (\lambda (a1: A).(\lambda (H3: (lt 
(lweight a1) (lweight a0))).(H2 (lweight a1) H3 a1 (refl_equal nat (lweight 
a1))))))))))))) a)))).

