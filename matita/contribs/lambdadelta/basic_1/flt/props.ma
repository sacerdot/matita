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

include "basic_1/C/props.ma".

theorem flt_thead_sx:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).(flt c u c 
(THead k u t)))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(let TMP_1 
\def (tweight u) in (let TMP_2 \def (tweight u) in (let TMP_3 \def (tweight 
t) in (let TMP_4 \def (plus TMP_2 TMP_3) in (let TMP_5 \def (S TMP_4) in (let 
TMP_6 \def (cweight c) in (let TMP_7 \def (tweight u) in (let TMP_8 \def 
(tweight u) in (let TMP_9 \def (tweight t) in (let TMP_10 \def (plus TMP_8 
TMP_9) in (let TMP_11 \def (tweight u) in (let TMP_12 \def (tweight t) in 
(let TMP_13 \def (le_plus_l TMP_11 TMP_12) in (let TMP_14 \def (le_n_S TMP_7 
TMP_10 TMP_13) in (lt_reg_l TMP_1 TMP_5 TMP_6 TMP_14)))))))))))))))))).

theorem flt_thead_dx:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).(flt c t c 
(THead k u t)))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(let TMP_1 
\def (tweight t) in (let TMP_2 \def (tweight u) in (let TMP_3 \def (tweight 
t) in (let TMP_4 \def (plus TMP_2 TMP_3) in (let TMP_5 \def (S TMP_4) in (let 
TMP_6 \def (cweight c) in (let TMP_7 \def (tweight t) in (let TMP_8 \def 
(tweight u) in (let TMP_9 \def (tweight t) in (let TMP_10 \def (plus TMP_8 
TMP_9) in (let TMP_11 \def (tweight u) in (let TMP_12 \def (tweight t) in 
(let TMP_13 \def (le_plus_r TMP_11 TMP_12) in (let TMP_14 \def (le_n_S TMP_7 
TMP_10 TMP_13) in (lt_reg_l TMP_1 TMP_5 TMP_6 TMP_14)))))))))))))))))).

theorem flt_shift:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(\forall (t: T).(flt (CHead c 
k u) t c (THead k u t)))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(let TMP_1 
\def (cweight c) in (let TMP_2 \def (tweight u) in (let TMP_3 \def (tweight 
t) in (let TMP_4 \def (plus TMP_2 TMP_3) in (let TMP_5 \def (plus TMP_1 
TMP_4) in (let TMP_6 \def (S TMP_5) in (let TMP_12 \def (\lambda (n: 
nat).(let TMP_7 \def (cweight c) in (let TMP_8 \def (tweight u) in (let TMP_9 
\def (plus TMP_7 TMP_8) in (let TMP_10 \def (tweight t) in (let TMP_11 \def 
(plus TMP_9 TMP_10) in (lt TMP_11 n))))))) in (let TMP_13 \def (cweight c) in 
(let TMP_14 \def (tweight u) in (let TMP_15 \def (plus TMP_13 TMP_14) in (let 
TMP_16 \def (tweight t) in (let TMP_17 \def (plus TMP_15 TMP_16) in (let 
TMP_24 \def (\lambda (n: nat).(let TMP_18 \def (cweight c) in (let TMP_19 
\def (tweight u) in (let TMP_20 \def (plus TMP_18 TMP_19) in (let TMP_21 \def 
(tweight t) in (let TMP_22 \def (plus TMP_20 TMP_21) in (let TMP_23 \def (S 
n) in (lt TMP_22 TMP_23)))))))) in (let TMP_25 \def (cweight c) in (let 
TMP_26 \def (tweight u) in (let TMP_27 \def (plus TMP_25 TMP_26) in (let 
TMP_28 \def (tweight t) in (let TMP_29 \def (plus TMP_27 TMP_28) in (let 
TMP_30 \def (S TMP_29) in (let TMP_31 \def (le_n TMP_30) in (let TMP_32 \def 
(cweight c) in (let TMP_33 \def (tweight u) in (let TMP_34 \def (tweight t) 
in (let TMP_35 \def (plus TMP_33 TMP_34) in (let TMP_36 \def (plus TMP_32 
TMP_35) in (let TMP_37 \def (cweight c) in (let TMP_38 \def (tweight u) in 
(let TMP_39 \def (tweight t) in (let TMP_40 \def (plus_assoc_l TMP_37 TMP_38 
TMP_39) in (let TMP_41 \def (eq_ind_r nat TMP_17 TMP_24 TMP_31 TMP_36 TMP_40) 
in (let TMP_42 \def (cweight c) in (let TMP_43 \def (tweight u) in (let 
TMP_44 \def (tweight t) in (let TMP_45 \def (plus TMP_43 TMP_44) in (let 
TMP_46 \def (S TMP_45) in (let TMP_47 \def (plus TMP_42 TMP_46) in (let 
TMP_48 \def (cweight c) in (let TMP_49 \def (tweight u) in (let TMP_50 \def 
(tweight t) in (let TMP_51 \def (plus TMP_49 TMP_50) in (let TMP_52 \def 
(plus_n_Sm TMP_48 TMP_51) in (eq_ind nat TMP_6 TMP_12 TMP_41 TMP_47 
TMP_52))))))))))))))))))))))))))))))))))))))))))))).

theorem flt_arith0:
 \forall (k: K).(\forall (c: C).(\forall (t: T).(\forall (i: nat).(flt c t 
(CHead c k t) (TLRef i)))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (t: T).(\lambda (_: nat).(let TMP_1 
\def (cweight c) in (let TMP_2 \def (tweight t) in (let TMP_3 \def (plus 
TMP_1 TMP_2) in (lt_x_plus_x_Sy TMP_3 O))))))).

theorem flt_arith1:
 \forall (k1: K).(\forall (c1: C).(\forall (c2: C).(\forall (t1: T).((cle 
(CHead c1 k1 t1) c2) \to (\forall (k2: K).(\forall (t2: T).(\forall (i: 
nat).(flt c1 t1 (CHead c2 k2 t2) (TLRef i)))))))))
\def
 \lambda (_: K).(\lambda (c1: C).(\lambda (c2: C).(\lambda (t1: T).(\lambda 
(H: (le (plus (cweight c1) (tweight t1)) (cweight c2))).(\lambda (_: 
K).(\lambda (t2: T).(\lambda (_: nat).(let TMP_1 \def (cweight c1) in (let 
TMP_2 \def (tweight t1) in (let TMP_3 \def (plus TMP_1 TMP_2) in (let TMP_4 
\def (cweight c2) in (let TMP_5 \def (cweight c2) in (let TMP_6 \def (tweight 
t2) in (let TMP_7 \def (plus TMP_5 TMP_6) in (let TMP_8 \def (S O) in (let 
TMP_9 \def (plus TMP_7 TMP_8) in (let TMP_10 \def (S O) in (let TMP_11 \def 
(cweight c2) in (let TMP_12 \def (tweight t2) in (let TMP_13 \def (plus 
TMP_11 TMP_12) in (let TMP_14 \def (plus TMP_10 TMP_13) in (let TMP_16 \def 
(\lambda (n: nat).(let TMP_15 \def (cweight c2) in (lt TMP_15 n))) in (let 
TMP_17 \def (cweight c2) in (let TMP_18 \def (cweight c2) in (let TMP_19 \def 
(tweight t2) in (let TMP_20 \def (plus TMP_18 TMP_19) in (let TMP_21 \def 
(cweight c2) in (let TMP_22 \def (tweight t2) in (let TMP_23 \def (le_plus_l 
TMP_21 TMP_22) in (let TMP_24 \def (le_lt_n_Sm TMP_17 TMP_20 TMP_23) in (let 
TMP_25 \def (cweight c2) in (let TMP_26 \def (tweight t2) in (let TMP_27 \def 
(plus TMP_25 TMP_26) in (let TMP_28 \def (S O) in (let TMP_29 \def (plus 
TMP_27 TMP_28) in (let TMP_30 \def (cweight c2) in (let TMP_31 \def (tweight 
t2) in (let TMP_32 \def (plus TMP_30 TMP_31) in (let TMP_33 \def (S O) in 
(let TMP_34 \def (plus_sym TMP_32 TMP_33) in (let TMP_35 \def (eq_ind_r nat 
TMP_14 TMP_16 TMP_24 TMP_29 TMP_34) in (le_lt_trans TMP_3 TMP_4 TMP_9 H 
TMP_35)))))))))))))))))))))))))))))))))))))))))).

theorem flt_arith2:
 \forall (c1: C).(\forall (c2: C).(\forall (t1: T).(\forall (i: nat).((flt c1 
t1 c2 (TLRef i)) \to (\forall (k2: K).(\forall (t2: T).(\forall (j: nat).(flt 
c1 t1 (CHead c2 k2 t2) (TLRef j)))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (t1: T).(\lambda (_: nat).(\lambda 
(H: (lt (plus (cweight c1) (tweight t1)) (plus (cweight c2) (S O)))).(\lambda 
(_: K).(\lambda (t2: T).(\lambda (_: nat).(let TMP_1 \def (cweight c1) in 
(let TMP_2 \def (tweight t1) in (let TMP_3 \def (plus TMP_1 TMP_2) in (let 
TMP_4 \def (cweight c2) in (let TMP_5 \def (S O) in (let TMP_6 \def (plus 
TMP_4 TMP_5) in (let TMP_7 \def (cweight c2) in (let TMP_8 \def (tweight t2) 
in (let TMP_9 \def (plus TMP_7 TMP_8) in (let TMP_10 \def (S O) in (let 
TMP_11 \def (plus TMP_9 TMP_10) in (let TMP_12 \def (cweight c2) in (let 
TMP_13 \def (cweight c2) in (let TMP_14 \def (tweight t2) in (let TMP_15 \def 
(plus TMP_13 TMP_14) in (let TMP_16 \def (S O) in (let TMP_17 \def (S O) in 
(let TMP_18 \def (cweight c2) in (let TMP_19 \def (tweight t2) in (let TMP_20 
\def (le_plus_l TMP_18 TMP_19) in (let TMP_21 \def (S O) in (let TMP_22 \def 
(le_n TMP_21) in (let TMP_23 \def (le_plus_plus TMP_12 TMP_15 TMP_16 TMP_17 
TMP_20 TMP_22) in (lt_le_trans TMP_3 TMP_6 TMP_11 H 
TMP_23))))))))))))))))))))))))))))))).

theorem cle_flt_trans:
 \forall (c1: C).(\forall (c2: C).((cle c1 c2) \to (\forall (c3: C).(\forall 
(u2: T).(\forall (u3: T).((flt c2 u2 c3 u3) \to (flt c1 u2 c3 u3)))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (le (cweight c1) (cweight 
c2))).(\lambda (c3: C).(\lambda (u2: T).(\lambda (u3: T).(\lambda (H0: (lt 
(plus (cweight c2) (tweight u2)) (plus (cweight c3) (tweight u3)))).(let 
TMP_1 \def (cweight c1) in (let TMP_2 \def (tweight u2) in (let TMP_3 \def 
(plus TMP_1 TMP_2) in (let TMP_4 \def (cweight c2) in (let TMP_5 \def 
(tweight u2) in (let TMP_6 \def (plus TMP_4 TMP_5) in (let TMP_7 \def 
(cweight c3) in (let TMP_8 \def (tweight u3) in (let TMP_9 \def (plus TMP_7 
TMP_8) in (let TMP_10 \def (cweight c1) in (let TMP_11 \def (cweight c2) in 
(let TMP_12 \def (tweight u2) in (let TMP_13 \def (tweight u2) in (let TMP_14 
\def (tweight u2) in (let TMP_15 \def (le_n TMP_14) in (let TMP_16 \def 
(le_plus_plus TMP_10 TMP_11 TMP_12 TMP_13 H TMP_15) in (le_lt_trans TMP_3 
TMP_6 TMP_9 TMP_16 H0))))))))))))))))))))))).

theorem flt_trans:
 \forall (c1: C).(\forall (c2: C).(\forall (t1: T).(\forall (t2: T).((flt c1 
t1 c2 t2) \to (\forall (c3: C).(\forall (t3: T).((flt c2 t2 c3 t3) \to (flt 
c1 t1 c3 t3))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (lt (fweight c1 t1) (fweight c2 t2))).(\lambda (c3: C).(\lambda (t3: 
T).(\lambda (H0: (lt (fweight c2 t2) (fweight c3 t3))).(let TMP_1 \def 
(fweight c1 t1) in (let TMP_2 \def (fweight c2 t2) in (let TMP_3 \def 
(fweight c3 t3) in (lt_trans TMP_1 TMP_2 TMP_3 H H0))))))))))).

