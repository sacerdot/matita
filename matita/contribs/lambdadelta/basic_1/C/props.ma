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

include "basic_1/C/fwd.ma".

include "basic_1/T/props.ma".

theorem cle_r:
 \forall (c: C).(cle c c)
\def
 \lambda (c: C).(let TMP_3 \def (\lambda (c0: C).(let TMP_1 \def (cweight c0) 
in (let TMP_2 \def (cweight c0) in (le TMP_1 TMP_2)))) in (let TMP_4 \def 
(\lambda (_: nat).(le_O_n O)) in (let TMP_8 \def (\lambda (c0: C).(\lambda 
(_: (le (cweight c0) (cweight c0))).(\lambda (_: K).(\lambda (t: T).(let 
TMP_5 \def (cweight c0) in (let TMP_6 \def (tweight t) in (let TMP_7 \def 
(plus TMP_5 TMP_6) in (le_n TMP_7)))))))) in (C_ind TMP_3 TMP_4 TMP_8 c)))).

theorem cle_head:
 \forall (c1: C).(\forall (c2: C).((cle c1 c2) \to (\forall (u1: T).(\forall 
(u2: T).((tle u1 u2) \to (\forall (k: K).(cle (CHead c1 k u1) (CHead c2 k 
u2))))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (le (cweight c1) (cweight 
c2))).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H0: (le (tweight u1) 
(tweight u2))).(\lambda (_: K).(let TMP_1 \def (cweight c1) in (let TMP_2 
\def (cweight c2) in (let TMP_3 \def (tweight u1) in (let TMP_4 \def (tweight 
u2) in (le_plus_plus TMP_1 TMP_2 TMP_3 TMP_4 H H0))))))))))).

theorem cle_trans_head:
 \forall (c1: C).(\forall (c2: C).((cle c1 c2) \to (\forall (k: K).(\forall 
(u: T).(cle c1 (CHead c2 k u))))))
\def
 \lambda (c1: C).(\lambda (c2: C).(\lambda (H: (le (cweight c1) (cweight 
c2))).(\lambda (_: K).(\lambda (u: T).(let TMP_1 \def (cweight c1) in (let 
TMP_2 \def (cweight c2) in (let TMP_3 \def (tweight u) in (le_plus_trans 
TMP_1 TMP_2 TMP_3 H)))))))).

theorem clt_cong:
 \forall (c: C).(\forall (d: C).((clt c d) \to (\forall (k: K).(\forall (t: 
T).(clt (CHead c k t) (CHead d k t))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (H: (lt (cweight c) (cweight 
d))).(\lambda (_: K).(\lambda (t: T).(let TMP_1 \def (cweight c) in (let 
TMP_2 \def (cweight d) in (let TMP_3 \def (tweight t) in (lt_reg_r TMP_1 
TMP_2 TMP_3 H)))))))).

theorem clt_head:
 \forall (k: K).(\forall (c: C).(\forall (u: T).(clt c (CHead c k u))))
\def
 \lambda (_: K).(\lambda (c: C).(\lambda (u: T).(let TMP_1 \def (cweight c) 
in (let TMP_2 \def (plus TMP_1 O) in (let TMP_6 \def (\lambda (n: nat).(let 
TMP_3 \def (cweight c) in (let TMP_4 \def (tweight u) in (let TMP_5 \def 
(plus TMP_3 TMP_4) in (lt n TMP_5))))) in (let TMP_7 \def (tweight u) in (let 
TMP_8 \def (cweight c) in (let TMP_9 \def (tweight_lt u) in (let TMP_10 \def 
(lt_reg_l O TMP_7 TMP_8 TMP_9) in (let TMP_11 \def (cweight c) in (let TMP_12 
\def (cweight c) in (let TMP_13 \def (plus_n_O TMP_12) in (eq_ind_r nat TMP_2 
TMP_6 TMP_10 TMP_11 TMP_13))))))))))))).

theorem chead_ctail:
 \forall (c: C).(\forall (t: T).(\forall (k: K).(ex_3 K C T (\lambda (h: 
K).(\lambda (d: C).(\lambda (u: T).(eq C (CHead c k t) (CTail h u d))))))))
\def
 \lambda (c: C).(let TMP_4 \def (\lambda (c0: C).(\forall (t: T).(\forall (k: 
K).(let TMP_3 \def (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(let TMP_1 
\def (CHead c0 k t) in (let TMP_2 \def (CTail h u d) in (eq C TMP_1 
TMP_2)))))) in (ex_3 K C T TMP_3))))) in (let TMP_13 \def (\lambda (n: 
nat).(\lambda (t: T).(\lambda (k: K).(let TMP_8 \def (\lambda (h: K).(\lambda 
(d: C).(\lambda (u: T).(let TMP_5 \def (CSort n) in (let TMP_6 \def (CHead 
TMP_5 k t) in (let TMP_7 \def (CTail h u d) in (eq C TMP_6 TMP_7))))))) in 
(let TMP_9 \def (CSort n) in (let TMP_10 \def (CSort n) in (let TMP_11 \def 
(CHead TMP_10 k t) in (let TMP_12 \def (refl_equal C TMP_11) in (ex_3_intro K 
C T TMP_8 k TMP_9 t TMP_12))))))))) in (let TMP_38 \def (\lambda (c0: 
C).(\lambda (H: ((\forall (t: T).(\forall (k: K).(ex_3 K C T (\lambda (h: 
K).(\lambda (d: C).(\lambda (u: T).(eq C (CHead c0 k t) (CTail h u 
d)))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (t0: T).(\lambda (k0: 
K).(let H_x \def (H t k) in (let H0 \def H_x in (let TMP_16 \def (\lambda (h: 
K).(\lambda (d: C).(\lambda (u: T).(let TMP_14 \def (CHead c0 k t) in (let 
TMP_15 \def (CTail h u d) in (eq C TMP_14 TMP_15)))))) in (let TMP_20 \def 
(\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(let TMP_17 \def (CHead c0 k 
t) in (let TMP_18 \def (CHead TMP_17 k0 t0) in (let TMP_19 \def (CTail h u d) 
in (eq C TMP_18 TMP_19))))))) in (let TMP_21 \def (ex_3 K C T TMP_20) in (let 
TMP_37 \def (\lambda (x0: K).(\lambda (x1: C).(\lambda (x2: T).(\lambda (H1: 
(eq C (CHead c0 k t) (CTail x0 x2 x1))).(let TMP_22 \def (CTail x0 x2 x1) in 
(let TMP_26 \def (\lambda (c1: C).(let TMP_25 \def (\lambda (h: K).(\lambda 
(d: C).(\lambda (u: T).(let TMP_23 \def (CHead c1 k0 t0) in (let TMP_24 \def 
(CTail h u d) in (eq C TMP_23 TMP_24)))))) in (ex_3 K C T TMP_25))) in (let 
TMP_30 \def (\lambda (h: K).(\lambda (d: C).(\lambda (u: T).(let TMP_27 \def 
(CTail x0 x2 x1) in (let TMP_28 \def (CHead TMP_27 k0 t0) in (let TMP_29 \def 
(CTail h u d) in (eq C TMP_28 TMP_29))))))) in (let TMP_31 \def (CHead x1 k0 
t0) in (let TMP_32 \def (CTail x0 x2 x1) in (let TMP_33 \def (CHead TMP_32 k0 
t0) in (let TMP_34 \def (refl_equal C TMP_33) in (let TMP_35 \def (ex_3_intro 
K C T TMP_30 x0 TMP_31 x2 TMP_34) in (let TMP_36 \def (CHead c0 k t) in 
(eq_ind_r C TMP_22 TMP_26 TMP_35 TMP_36 H1)))))))))))))) in (ex_3_ind K C T 
TMP_16 TMP_21 TMP_37 H0))))))))))))) in (C_ind TMP_4 TMP_13 TMP_38 c)))).

theorem clt_thead:
 \forall (k: K).(\forall (u: T).(\forall (c: C).(clt c (CTail k u c))))
\def
 \lambda (k: K).(\lambda (u: T).(\lambda (c: C).(let TMP_2 \def (\lambda (c0: 
C).(let TMP_1 \def (CTail k u c0) in (clt c0 TMP_1))) in (let TMP_4 \def 
(\lambda (n: nat).(let TMP_3 \def (CSort n) in (clt_head k TMP_3 u))) in (let 
TMP_6 \def (\lambda (c0: C).(\lambda (H: (clt c0 (CTail k u c0))).(\lambda 
(k0: K).(\lambda (t: T).(let TMP_5 \def (CTail k u c0) in (clt_cong c0 TMP_5 
H k0 t)))))) in (C_ind TMP_2 TMP_4 TMP_6 c)))))).

theorem c_tail_ind:
 \forall (P: ((C \to Prop))).(((\forall (n: nat).(P (CSort n)))) \to 
(((\forall (c: C).((P c) \to (\forall (k: K).(\forall (t: T).(P (CTail k t 
c))))))) \to (\forall (c: C).(P c))))
\def
 \lambda (P: ((C \to Prop))).(\lambda (H: ((\forall (n: nat).(P (CSort 
n))))).(\lambda (H0: ((\forall (c: C).((P c) \to (\forall (k: K).(\forall (t: 
T).(P (CTail k t c)))))))).(\lambda (c: C).(let TMP_1 \def (\lambda (c0: 
C).(P c0)) in (let TMP_20 \def (\lambda (c0: C).(let TMP_2 \def (\lambda (c1: 
C).(((\forall (d: C).((clt d c1) \to (P d)))) \to (P c1))) in (let TMP_3 \def 
(\lambda (n: nat).(\lambda (_: ((\forall (d: C).((clt d (CSort n)) \to (P 
d))))).(H n))) in (let TMP_19 \def (\lambda (c1: C).(\lambda (_: ((((\forall 
(d: C).((clt d c1) \to (P d)))) \to (P c1)))).(\lambda (k: K).(\lambda (t: 
T).(\lambda (H2: ((\forall (d: C).((clt d (CHead c1 k t)) \to (P d))))).(let 
H_x \def (chead_ctail c1 t k) in (let H3 \def H_x in (let TMP_6 \def (\lambda 
(h: K).(\lambda (d: C).(\lambda (u: T).(let TMP_4 \def (CHead c1 k t) in (let 
TMP_5 \def (CTail h u d) in (eq C TMP_4 TMP_5)))))) in (let TMP_7 \def (CHead 
c1 k t) in (let TMP_8 \def (P TMP_7) in (let TMP_18 \def (\lambda (x0: 
K).(\lambda (x1: C).(\lambda (x2: T).(\lambda (H4: (eq C (CHead c1 k t) 
(CTail x0 x2 x1))).(let TMP_9 \def (CTail x0 x2 x1) in (let TMP_10 \def 
(\lambda (c2: C).(P c2)) in (let TMP_11 \def (CHead c1 k t) in (let TMP_12 
\def (\lambda (c2: C).(\forall (d: C).((clt d c2) \to (P d)))) in (let TMP_13 
\def (CTail x0 x2 x1) in (let H5 \def (eq_ind C TMP_11 TMP_12 H2 TMP_13 H4) 
in (let TMP_14 \def (clt_thead x0 x2 x1) in (let TMP_15 \def (H5 x1 TMP_14) 
in (let TMP_16 \def (H0 x1 TMP_15 x0 x2) in (let TMP_17 \def (CHead c1 k t) 
in (eq_ind_r C TMP_9 TMP_10 TMP_16 TMP_17 H4))))))))))))))) in (ex_3_ind K C 
T TMP_6 TMP_8 TMP_18 H3)))))))))))) in (C_ind TMP_2 TMP_3 TMP_19 c0))))) in 
(clt_wf_ind TMP_1 TMP_20 c)))))).

