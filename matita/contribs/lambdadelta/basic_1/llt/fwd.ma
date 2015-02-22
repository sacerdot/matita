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

theorem llt_wf__q_ind:
 \forall (P: ((A \to Prop))).(((\forall (n: nat).((\lambda (P0: ((A \to 
Prop))).(\lambda (n0: nat).(\forall (a: A).((eq nat (lweight a) n0) \to (P0 
a))))) P n))) \to (\forall (a: A).(P a)))
\def
 let Q \def (\lambda (P: ((A \to Prop))).(\lambda (n: nat).(\forall (a: 
A).((eq nat (lweight a) n) \to (P a))))) in (\lambda (P: ((A \to 
Prop))).(\lambda (H: ((\forall (n: nat).(\forall (a: A).((eq nat (lweight a) 
n) \to (P a)))))).(\lambda (a: A).(let TMP_1 \def (lweight a) in (let TMP_2 
\def (lweight a) in (let TMP_3 \def (refl_equal nat TMP_2) in (H TMP_1 a 
TMP_3))))))).

theorem llt_wf_ind:
 \forall (P: ((A \to Prop))).(((\forall (a2: A).(((\forall (a1: A).((llt a1 
a2) \to (P a1)))) \to (P a2)))) \to (\forall (a: A).(P a)))
\def
 let Q \def (\lambda (P: ((A \to Prop))).(\lambda (n: nat).(\forall (a: 
A).((eq nat (lweight a) n) \to (P a))))) in (\lambda (P: ((A \to 
Prop))).(\lambda (H: ((\forall (a2: A).(((\forall (a1: A).((lt (lweight a1) 
(lweight a2)) \to (P a1)))) \to (P a2))))).(\lambda (a: A).(let TMP_1 \def 
(\lambda (a0: A).(P a0)) in (let TMP_11 \def (\lambda (n: nat).(let TMP_2 
\def (\lambda (a0: A).(P a0)) in (let TMP_3 \def (Q TMP_2) in (let TMP_10 
\def (\lambda (n0: nat).(\lambda (H0: ((\forall (m: nat).((lt m n0) \to (Q 
(\lambda (a0: A).(P a0)) m))))).(\lambda (a0: A).(\lambda (H1: (eq nat 
(lweight a0) n0)).(let TMP_4 \def (\lambda (n1: nat).(\forall (m: nat).((lt m 
n1) \to (\forall (a1: A).((eq nat (lweight a1) m) \to (P a1)))))) in (let 
TMP_5 \def (lweight a0) in (let H2 \def (eq_ind_r nat n0 TMP_4 H0 TMP_5 H1) 
in (let TMP_9 \def (\lambda (a1: A).(\lambda (H3: (lt (lweight a1) (lweight 
a0))).(let TMP_6 \def (lweight a1) in (let TMP_7 \def (lweight a1) in (let 
TMP_8 \def (refl_equal nat TMP_7) in (H2 TMP_6 H3 a1 TMP_8)))))) in (H a0 
TMP_9))))))))) in (lt_wf_ind n TMP_3 TMP_10))))) in (llt_wf__q_ind TMP_1 
TMP_11 a)))))).

