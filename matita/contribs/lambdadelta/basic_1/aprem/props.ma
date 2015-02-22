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

include "basic_1/aprem/fwd.ma".

include "basic_1/leq/fwd.ma".

theorem aprem_repl:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).((leq g a1 a2) \to (\forall 
(i: nat).(\forall (b2: A).((aprem i a2 b2) \to (ex2 A (\lambda (b1: A).(leq g 
b1 b2)) (\lambda (b1: A).(aprem i a1 b1)))))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq g a1 
a2)).(let TMP_3 \def (\lambda (a: A).(\lambda (a0: A).(\forall (i: 
nat).(\forall (b2: A).((aprem i a0 b2) \to (let TMP_1 \def (\lambda (b1: 
A).(leq g b1 b2)) in (let TMP_2 \def (\lambda (b1: A).(aprem i a b1)) in (ex2 
A TMP_1 TMP_2)))))))) in (let TMP_8 \def (\lambda (h1: nat).(\lambda (h2: 
nat).(\lambda (n1: nat).(\lambda (n2: nat).(\lambda (k: nat).(\lambda (_: (eq 
A (aplus g (ASort h1 n1) k) (aplus g (ASort h2 n2) k))).(\lambda (i: 
nat).(\lambda (b2: A).(\lambda (H1: (aprem i (ASort h2 n2) b2)).(let H_x \def 
(aprem_gen_sort b2 i h2 n2 H1) in (let H2 \def H_x in (let TMP_4 \def 
(\lambda (b1: A).(leq g b1 b2)) in (let TMP_6 \def (\lambda (b1: A).(let 
TMP_5 \def (ASort h1 n1) in (aprem i TMP_5 b1))) in (let TMP_7 \def (ex2 A 
TMP_4 TMP_6) in (False_ind TMP_7 H2))))))))))))))) in (let TMP_37 \def 
(\lambda (a0: A).(\lambda (a3: A).(\lambda (H0: (leq g a0 a3)).(\lambda (_: 
((\forall (i: nat).(\forall (b2: A).((aprem i a3 b2) \to (ex2 A (\lambda (b1: 
A).(leq g b1 b2)) (\lambda (b1: A).(aprem i a0 b1)))))))).(\lambda (a4: 
A).(\lambda (a5: A).(\lambda (_: (leq g a4 a5)).(\lambda (H3: ((\forall (i: 
nat).(\forall (b2: A).((aprem i a5 b2) \to (ex2 A (\lambda (b1: A).(leq g b1 
b2)) (\lambda (b1: A).(aprem i a4 b1)))))))).(\lambda (i: nat).(\lambda (b2: 
A).(\lambda (H4: (aprem i (AHead a3 a5) b2)).(let TMP_12 \def (\lambda (n: 
nat).((aprem n (AHead a3 a5) b2) \to (let TMP_9 \def (\lambda (b1: A).(leq g 
b1 b2)) in (let TMP_11 \def (\lambda (b1: A).(let TMP_10 \def (AHead a0 a4) 
in (aprem n TMP_10 b1))) in (ex2 A TMP_9 TMP_11))))) in (let TMP_22 \def 
(\lambda (H5: (aprem O (AHead a3 a5) b2)).(let H_y \def (aprem_gen_head_O a3 
a5 b2 H5) in (let TMP_16 \def (\lambda (a: A).(let TMP_13 \def (\lambda (b1: 
A).(leq g b1 a)) in (let TMP_15 \def (\lambda (b1: A).(let TMP_14 \def (AHead 
a0 a4) in (aprem O TMP_14 b1))) in (ex2 A TMP_13 TMP_15)))) in (let TMP_17 
\def (\lambda (b1: A).(leq g b1 a3)) in (let TMP_19 \def (\lambda (b1: 
A).(let TMP_18 \def (AHead a0 a4) in (aprem O TMP_18 b1))) in (let TMP_20 
\def (aprem_zero a0 a4) in (let TMP_21 \def (ex_intro2 A TMP_17 TMP_19 a0 H0 
TMP_20) in (eq_ind_r A a3 TMP_16 TMP_21 b2 H_y)))))))) in (let TMP_36 \def 
(\lambda (i0: nat).(\lambda (_: (((aprem i0 (AHead a3 a5) b2) \to (ex2 A 
(\lambda (b1: A).(leq g b1 b2)) (\lambda (b1: A).(aprem i0 (AHead a0 a4) 
b1)))))).(\lambda (H5: (aprem (S i0) (AHead a3 a5) b2)).(let H_y \def 
(aprem_gen_head_S a3 a5 b2 i0 H5) in (let H_x \def (H3 i0 b2 H_y) in (let H6 
\def H_x in (let TMP_23 \def (\lambda (b1: A).(leq g b1 b2)) in (let TMP_24 
\def (\lambda (b1: A).(aprem i0 a4 b1)) in (let TMP_25 \def (\lambda (b1: 
A).(leq g b1 b2)) in (let TMP_28 \def (\lambda (b1: A).(let TMP_26 \def (S 
i0) in (let TMP_27 \def (AHead a0 a4) in (aprem TMP_26 TMP_27 b1)))) in (let 
TMP_29 \def (ex2 A TMP_25 TMP_28) in (let TMP_35 \def (\lambda (x: 
A).(\lambda (H7: (leq g x b2)).(\lambda (H8: (aprem i0 a4 x)).(let TMP_30 
\def (\lambda (b1: A).(leq g b1 b2)) in (let TMP_33 \def (\lambda (b1: 
A).(let TMP_31 \def (S i0) in (let TMP_32 \def (AHead a0 a4) in (aprem TMP_31 
TMP_32 b1)))) in (let TMP_34 \def (aprem_succ a4 x i0 H8 a0) in (ex_intro2 A 
TMP_30 TMP_33 x H7 TMP_34))))))) in (ex2_ind A TMP_23 TMP_24 TMP_29 TMP_35 
H6))))))))))))) in (nat_ind TMP_12 TMP_22 TMP_36 i H4))))))))))))))) in 
(leq_ind g TMP_3 TMP_8 TMP_37 a1 a2 H))))))).

theorem aprem_asucc:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (i: nat).((aprem i 
a1 a2) \to (aprem i (asucc g a1) a2)))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (i: nat).(\lambda 
(H: (aprem i a1 a2)).(let TMP_2 \def (\lambda (n: nat).(\lambda (a: 
A).(\lambda (a0: A).(let TMP_1 \def (asucc g a) in (aprem n TMP_1 a0))))) in 
(let TMP_4 \def (\lambda (a0: A).(\lambda (a3: A).(let TMP_3 \def (asucc g 
a3) in (aprem_zero a0 TMP_3)))) in (let TMP_6 \def (\lambda (a0: A).(\lambda 
(a: A).(\lambda (i0: nat).(\lambda (_: (aprem i0 a0 a)).(\lambda (H1: (aprem 
i0 (asucc g a0) a)).(\lambda (a3: A).(let TMP_5 \def (asucc g a0) in 
(aprem_succ TMP_5 a i0 H1 a3)))))))) in (aprem_ind TMP_2 TMP_4 TMP_6 i a1 a2 
H)))))))).

