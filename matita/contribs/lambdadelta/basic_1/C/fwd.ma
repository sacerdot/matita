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

include "basic_1/C/defs.ma".

let rec C_rect (P: (C \to Type[0])) (f: (\forall (n: nat).(P (CSort n)))) 
(f0: (\forall (c: C).((P c) \to (\forall (k: K).(\forall (t: T).(P (CHead c k 
t))))))) (c: C) on c: P c \def match c with [(CSort n) \Rightarrow (f n) | 
(CHead c0 k t) \Rightarrow (let TMP_1 \def ((C_rect P f f0) c0) in (f0 c0 
TMP_1 k t))].

theorem C_ind:
 \forall (P: ((C \to Prop))).(((\forall (n: nat).(P (CSort n)))) \to 
(((\forall (c: C).((P c) \to (\forall (k: K).(\forall (t: T).(P (CHead c k 
t))))))) \to (\forall (c: C).(P c))))
\def
 \lambda (P: ((C \to Prop))).(C_rect P).

theorem clt_wf__q_ind:
 \forall (P: ((C \to Prop))).(((\forall (n: nat).((\lambda (P0: ((C \to 
Prop))).(\lambda (n0: nat).(\forall (c: C).((eq nat (cweight c) n0) \to (P0 
c))))) P n))) \to (\forall (c: C).(P c)))
\def
 let Q \def (\lambda (P: ((C \to Prop))).(\lambda (n: nat).(\forall (c: 
C).((eq nat (cweight c) n) \to (P c))))) in (\lambda (P: ((C \to 
Prop))).(\lambda (H: ((\forall (n: nat).(\forall (c: C).((eq nat (cweight c) 
n) \to (P c)))))).(\lambda (c: C).(let TMP_1 \def (cweight c) in (let TMP_2 
\def (cweight c) in (let TMP_3 \def (refl_equal nat TMP_2) in (H TMP_1 c 
TMP_3))))))).

theorem clt_wf_ind:
 \forall (P: ((C \to Prop))).(((\forall (c: C).(((\forall (d: C).((clt d c) 
\to (P d)))) \to (P c)))) \to (\forall (c: C).(P c)))
\def
 let Q \def (\lambda (P: ((C \to Prop))).(\lambda (n: nat).(\forall (c: 
C).((eq nat (cweight c) n) \to (P c))))) in (\lambda (P: ((C \to 
Prop))).(\lambda (H: ((\forall (c: C).(((\forall (d: C).((lt (cweight d) 
(cweight c)) \to (P d)))) \to (P c))))).(\lambda (c: C).(let TMP_1 \def 
(\lambda (c0: C).(P c0)) in (let TMP_11 \def (\lambda (n: nat).(let TMP_2 
\def (\lambda (c0: C).(P c0)) in (let TMP_3 \def (Q TMP_2) in (let TMP_10 
\def (\lambda (n0: nat).(\lambda (H0: ((\forall (m: nat).((lt m n0) \to (Q 
(\lambda (c0: C).(P c0)) m))))).(\lambda (c0: C).(\lambda (H1: (eq nat 
(cweight c0) n0)).(let TMP_4 \def (\lambda (n1: nat).(\forall (m: nat).((lt m 
n1) \to (\forall (c1: C).((eq nat (cweight c1) m) \to (P c1)))))) in (let 
TMP_5 \def (cweight c0) in (let H2 \def (eq_ind_r nat n0 TMP_4 H0 TMP_5 H1) 
in (let TMP_9 \def (\lambda (d: C).(\lambda (H3: (lt (cweight d) (cweight 
c0))).(let TMP_6 \def (cweight d) in (let TMP_7 \def (cweight d) in (let 
TMP_8 \def (refl_equal nat TMP_7) in (H2 TMP_6 H3 d TMP_8)))))) in (H c0 
TMP_9))))))))) in (lt_wf_ind n TMP_3 TMP_10))))) in (clt_wf__q_ind TMP_1 
TMP_11 c)))))).

