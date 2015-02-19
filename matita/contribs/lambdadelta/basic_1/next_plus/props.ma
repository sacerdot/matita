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

include "basic_1/next_plus/defs.ma".

theorem next_plus_assoc:
 \forall (g: G).(\forall (n: nat).(\forall (h1: nat).(\forall (h2: nat).(eq 
nat (next_plus g (next_plus g n h1) h2) (next_plus g n (plus h1 h2))))))
\def
 \lambda (g: G).(\lambda (n: nat).(\lambda (h1: nat).(let TMP_5 \def (\lambda 
(n0: nat).(\forall (h2: nat).(let TMP_1 \def (next_plus g n n0) in (let TMP_2 
\def (next_plus g TMP_1 h2) in (let TMP_3 \def (plus n0 h2) in (let TMP_4 
\def (next_plus g n TMP_3) in (eq nat TMP_2 TMP_4))))))) in (let TMP_7 \def 
(\lambda (h2: nat).(let TMP_6 \def (next_plus g n h2) in (refl_equal nat 
TMP_6))) in (let TMP_47 \def (\lambda (n0: nat).(\lambda (_: ((\forall (h2: 
nat).(eq nat (next_plus g (next_plus g n n0) h2) (next_plus g n (plus n0 
h2)))))).(\lambda (h2: nat).(let TMP_14 \def (\lambda (n1: nat).(let TMP_8 
\def (next_plus g n n0) in (let TMP_9 \def (next g TMP_8) in (let TMP_10 \def 
(next_plus g TMP_9 n1) in (let TMP_11 \def (plus n0 n1) in (let TMP_12 \def 
(next_plus g n TMP_11) in (let TMP_13 \def (next g TMP_12) in (eq nat TMP_10 
TMP_13)))))))) in (let TMP_19 \def (\lambda (n1: nat).(let TMP_15 \def 
(next_plus g n n0) in (let TMP_16 \def (next g TMP_15) in (let TMP_17 \def 
(next_plus g n n1) in (let TMP_18 \def (next g TMP_17) in (eq nat TMP_16 
TMP_18)))))) in (let TMP_20 \def (next_plus g n n0) in (let TMP_21 \def (next 
g TMP_20) in (let TMP_22 \def (refl_equal nat TMP_21) in (let TMP_23 \def 
(plus n0 O) in (let TMP_24 \def (plus_n_O n0) in (let TMP_25 \def (eq_ind nat 
n0 TMP_19 TMP_22 TMP_23 TMP_24) in (let TMP_46 \def (\lambda (n1: 
nat).(\lambda (H0: (eq nat (next_plus g (next g (next_plus g n n0)) n1) (next 
g (next_plus g n (plus n0 n1))))).(let TMP_26 \def (plus n0 n1) in (let 
TMP_27 \def (S TMP_26) in (let TMP_34 \def (\lambda (n2: nat).(let TMP_28 
\def (next_plus g n n0) in (let TMP_29 \def (next g TMP_28) in (let TMP_30 
\def (next_plus g TMP_29 n1) in (let TMP_31 \def (next g TMP_30) in (let 
TMP_32 \def (next_plus g n n2) in (let TMP_33 \def (next g TMP_32) in (eq nat 
TMP_31 TMP_33)))))))) in (let TMP_35 \def (next g) in (let TMP_36 \def 
(next_plus g n n0) in (let TMP_37 \def (next g TMP_36) in (let TMP_38 \def 
(next_plus g TMP_37 n1) in (let TMP_39 \def (plus n0 n1) in (let TMP_40 \def 
(next_plus g n TMP_39) in (let TMP_41 \def (next g TMP_40) in (let TMP_42 
\def (f_equal nat nat TMP_35 TMP_38 TMP_41 H0) in (let TMP_43 \def (S n1) in 
(let TMP_44 \def (plus n0 TMP_43) in (let TMP_45 \def (plus_n_Sm n0 n1) in 
(eq_ind nat TMP_27 TMP_34 TMP_42 TMP_44 TMP_45))))))))))))))))) in (nat_ind 
TMP_14 TMP_25 TMP_46 h2))))))))))))) in (nat_ind TMP_5 TMP_7 TMP_47 h1)))))).

theorem next_plus_next:
 \forall (g: G).(\forall (n: nat).(\forall (h: nat).(eq nat (next_plus g 
(next g n) h) (next g (next_plus g n h)))))
\def
 \lambda (g: G).(\lambda (n: nat).(\lambda (h: nat).(let TMP_1 \def (S O) in 
(let TMP_2 \def (plus TMP_1 h) in (let TMP_3 \def (next_plus g n TMP_2) in 
(let TMP_6 \def (\lambda (n0: nat).(let TMP_4 \def (next_plus g n h) in (let 
TMP_5 \def (next g TMP_4) in (eq nat n0 TMP_5)))) in (let TMP_7 \def 
(next_plus g n h) in (let TMP_8 \def (next g TMP_7) in (let TMP_9 \def 
(refl_equal nat TMP_8) in (let TMP_10 \def (S O) in (let TMP_11 \def 
(next_plus g n TMP_10) in (let TMP_12 \def (next_plus g TMP_11 h) in (let 
TMP_13 \def (S O) in (let TMP_14 \def (next_plus_assoc g n TMP_13 h) in 
(eq_ind_r nat TMP_3 TMP_6 TMP_9 TMP_12 TMP_14))))))))))))))).

theorem next_plus_lt:
 \forall (g: G).(\forall (h: nat).(\forall (n: nat).(lt n (next_plus g (next 
g n) h))))
\def
 \lambda (g: G).(\lambda (h: nat).(let TMP_3 \def (\lambda (n: nat).(\forall 
(n0: nat).(let TMP_1 \def (next g n0) in (let TMP_2 \def (next_plus g TMP_1 
n) in (lt n0 TMP_2))))) in (let TMP_4 \def (\lambda (n: nat).(next_lt g n)) 
in (let TMP_22 \def (\lambda (n: nat).(\lambda (H: ((\forall (n0: nat).(lt n0 
(next_plus g (next g n0) n))))).(\lambda (n0: nat).(let TMP_5 \def (next g 
n0) in (let TMP_6 \def (next g TMP_5) in (let TMP_7 \def (next_plus g TMP_6 
n) in (let TMP_8 \def (\lambda (n1: nat).(lt n0 n1)) in (let TMP_9 \def (next 
g n0) in (let TMP_10 \def (next g n0) in (let TMP_11 \def (next g TMP_10) in 
(let TMP_12 \def (next_plus g TMP_11 n) in (let TMP_13 \def (next_lt g n0) in 
(let TMP_14 \def (next g n0) in (let TMP_15 \def (H TMP_14) in (let TMP_16 
\def (lt_trans n0 TMP_9 TMP_12 TMP_13 TMP_15) in (let TMP_17 \def (next g n0) 
in (let TMP_18 \def (next_plus g TMP_17 n) in (let TMP_19 \def (next g 
TMP_18) in (let TMP_20 \def (next g n0) in (let TMP_21 \def (next_plus_next g 
TMP_20 n) in (eq_ind nat TMP_7 TMP_8 TMP_16 TMP_19 
TMP_21))))))))))))))))))))) in (nat_ind TMP_3 TMP_4 TMP_22 h))))).

