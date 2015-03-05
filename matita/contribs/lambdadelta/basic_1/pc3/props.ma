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

include "basic_1/pc3/defs.ma".

include "basic_1/pr3/pr3.ma".

theorem clear_pc3_trans:
 \forall (c2: C).(\forall (t1: T).(\forall (t2: T).((pc3 c2 t1 t2) \to 
(\forall (c1: C).((clear c1 c2) \to (pc3 c1 t1 t2))))))
\def
 \lambda (c2: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc3 c2 t1 
t2)).(\lambda (c1: C).(\lambda (H0: (clear c1 c2)).(let H1 \def H in (let 
TMP_1 \def (\lambda (t: T).(pr3 c2 t1 t)) in (let TMP_2 \def (\lambda (t: 
T).(pr3 c2 t2 t)) in (let TMP_3 \def (pc3 c1 t1 t2) in (let TMP_8 \def 
(\lambda (x: T).(\lambda (H2: (pr3 c2 t1 x)).(\lambda (H3: (pr3 c2 t2 
x)).(let TMP_4 \def (\lambda (t: T).(pr3 c1 t1 t)) in (let TMP_5 \def 
(\lambda (t: T).(pr3 c1 t2 t)) in (let TMP_6 \def (clear_pr3_trans c2 t1 x H2 
c1 H0) in (let TMP_7 \def (clear_pr3_trans c2 t2 x H3 c1 H0) in (ex_intro2 T 
TMP_4 TMP_5 x TMP_6 TMP_7)))))))) in (ex2_ind T TMP_1 TMP_2 TMP_3 TMP_8 
H1))))))))))).

theorem pc3_pr2_r:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (pc3 c 
t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr2 c t1 
t2)).(let TMP_1 \def (\lambda (t: T).(pr3 c t1 t)) in (let TMP_2 \def 
(\lambda (t: T).(pr3 c t2 t)) in (let TMP_3 \def (pr3_pr2 c t1 t2 H) in (let 
TMP_4 \def (pr3_refl c t2) in (ex_intro2 T TMP_1 TMP_2 t2 TMP_3 TMP_4)))))))).

theorem pc3_pr2_x:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t2 t1) \to (pc3 c 
t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr2 c t2 
t1)).(let TMP_1 \def (\lambda (t: T).(pr3 c t1 t)) in (let TMP_2 \def 
(\lambda (t: T).(pr3 c t2 t)) in (let TMP_3 \def (pr3_refl c t1) in (let 
TMP_4 \def (pr3_pr2 c t2 t1 H) in (ex_intro2 T TMP_1 TMP_2 t1 TMP_3 
TMP_4)))))))).

theorem pc3_pr3_r:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t1 t2) \to (pc3 c 
t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr3 c t1 
t2)).(let TMP_1 \def (\lambda (t: T).(pr3 c t1 t)) in (let TMP_2 \def 
(\lambda (t: T).(pr3 c t2 t)) in (let TMP_3 \def (pr3_refl c t2) in 
(ex_intro2 T TMP_1 TMP_2 t2 H TMP_3))))))).

theorem pc3_pr3_x:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr3 c t2 t1) \to (pc3 c 
t1 t2))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr3 c t2 
t1)).(let TMP_1 \def (\lambda (t: T).(pr3 c t1 t)) in (let TMP_2 \def 
(\lambda (t: T).(pr3 c t2 t)) in (let TMP_3 \def (pr3_refl c t1) in 
(ex_intro2 T TMP_1 TMP_2 t1 TMP_3 H))))))).

theorem pc3_pr3_t:
 \forall (c: C).(\forall (t1: T).(\forall (t0: T).((pr3 c t1 t0) \to (\forall 
(t2: T).((pr3 c t2 t0) \to (pc3 c t1 t2))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t0: T).(\lambda (H: (pr3 c t1 
t0)).(\lambda (t2: T).(\lambda (H0: (pr3 c t2 t0)).(let TMP_1 \def (\lambda 
(t: T).(pr3 c t1 t)) in (let TMP_2 \def (\lambda (t: T).(pr3 c t2 t)) in 
(ex_intro2 T TMP_1 TMP_2 t0 H H0)))))))).

theorem pc3_refl:
 \forall (c: C).(\forall (t: T).(pc3 c t t))
\def
 \lambda (c: C).(\lambda (t: T).(let TMP_1 \def (\lambda (t0: T).(pr3 c t 
t0)) in (let TMP_2 \def (\lambda (t0: T).(pr3 c t t0)) in (let TMP_3 \def 
(pr3_refl c t) in (let TMP_4 \def (pr3_refl c t) in (ex_intro2 T TMP_1 TMP_2 
t TMP_3 TMP_4)))))).

theorem pc3_s:
 \forall (c: C).(\forall (t2: T).(\forall (t1: T).((pc3 c t1 t2) \to (pc3 c 
t2 t1))))
\def
 \lambda (c: C).(\lambda (t2: T).(\lambda (t1: T).(\lambda (H: (pc3 c t1 
t2)).(let H0 \def H in (let TMP_1 \def (\lambda (t: T).(pr3 c t1 t)) in (let 
TMP_2 \def (\lambda (t: T).(pr3 c t2 t)) in (let TMP_3 \def (pc3 c t2 t1) in 
(let TMP_6 \def (\lambda (x: T).(\lambda (H1: (pr3 c t1 x)).(\lambda (H2: 
(pr3 c t2 x)).(let TMP_4 \def (\lambda (t: T).(pr3 c t2 t)) in (let TMP_5 
\def (\lambda (t: T).(pr3 c t1 t)) in (ex_intro2 T TMP_4 TMP_5 x H2 H1)))))) 
in (ex2_ind T TMP_1 TMP_2 TMP_3 TMP_6 H0))))))))).

theorem pc3_thin_dx:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pc3 c t1 t2) \to (\forall 
(u: T).(\forall (f: F).(pc3 c (THead (Flat f) u t1) (THead (Flat f) u 
t2)))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pc3 c t1 
t2)).(\lambda (u: T).(\lambda (f: F).(let H0 \def H in (let TMP_1 \def 
(\lambda (t: T).(pr3 c t1 t)) in (let TMP_2 \def (\lambda (t: T).(pr3 c t2 
t)) in (let TMP_3 \def (Flat f) in (let TMP_4 \def (THead TMP_3 u t1) in (let 
TMP_5 \def (Flat f) in (let TMP_6 \def (THead TMP_5 u t2) in (let TMP_7 \def 
(pc3 c TMP_4 TMP_6) in (let TMP_18 \def (\lambda (x: T).(\lambda (H1: (pr3 c 
t1 x)).(\lambda (H2: (pr3 c t2 x)).(let TMP_10 \def (\lambda (t: T).(let 
TMP_8 \def (Flat f) in (let TMP_9 \def (THead TMP_8 u t1) in (pr3 c TMP_9 
t)))) in (let TMP_13 \def (\lambda (t: T).(let TMP_11 \def (Flat f) in (let 
TMP_12 \def (THead TMP_11 u t2) in (pr3 c TMP_12 t)))) in (let TMP_14 \def 
(Flat f) in (let TMP_15 \def (THead TMP_14 u x) in (let TMP_16 \def 
(pr3_thin_dx c t1 x H1 u f) in (let TMP_17 \def (pr3_thin_dx c t2 x H2 u f) 
in (ex_intro2 T TMP_10 TMP_13 TMP_15 TMP_16 TMP_17)))))))))) in (ex2_ind T 
TMP_1 TMP_2 TMP_7 TMP_18 H0))))))))))))))).

theorem pc3_head_1:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pc3 c u1 u2) \to (\forall 
(k: K).(\forall (t: T).(pc3 c (THead k u1 t) (THead k u2 t)))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pc3 c u1 
u2)).(\lambda (k: K).(\lambda (t: T).(let H0 \def H in (let TMP_1 \def 
(\lambda (t0: T).(pr3 c u1 t0)) in (let TMP_2 \def (\lambda (t0: T).(pr3 c u2 
t0)) in (let TMP_3 \def (THead k u1 t) in (let TMP_4 \def (THead k u2 t) in 
(let TMP_5 \def (pc3 c TMP_3 TMP_4) in (let TMP_17 \def (\lambda (x: 
T).(\lambda (H1: (pr3 c u1 x)).(\lambda (H2: (pr3 c u2 x)).(let TMP_7 \def 
(\lambda (t0: T).(let TMP_6 \def (THead k u1 t) in (pr3 c TMP_6 t0))) in (let 
TMP_9 \def (\lambda (t0: T).(let TMP_8 \def (THead k u2 t) in (pr3 c TMP_8 
t0))) in (let TMP_10 \def (THead k x t) in (let TMP_11 \def (CHead c k x) in 
(let TMP_12 \def (pr3_refl TMP_11 t) in (let TMP_13 \def (pr3_head_12 c u1 x 
H1 k t t TMP_12) in (let TMP_14 \def (CHead c k x) in (let TMP_15 \def 
(pr3_refl TMP_14 t) in (let TMP_16 \def (pr3_head_12 c u2 x H2 k t t TMP_15) 
in (ex_intro2 T TMP_7 TMP_9 TMP_10 TMP_13 TMP_16))))))))))))) in (ex2_ind T 
TMP_1 TMP_2 TMP_5 TMP_17 H0))))))))))))).

theorem pc3_head_2:
 \forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall (t2: T).(\forall 
(k: K).((pc3 (CHead c k u) t1 t2) \to (pc3 c (THead k u t1) (THead k u 
t2)))))))
\def
 \lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(k: K).(\lambda (H: (pc3 (CHead c k u) t1 t2)).(let H0 \def H in (let TMP_2 
\def (\lambda (t: T).(let TMP_1 \def (CHead c k u) in (pr3 TMP_1 t1 t))) in 
(let TMP_4 \def (\lambda (t: T).(let TMP_3 \def (CHead c k u) in (pr3 TMP_3 
t2 t))) in (let TMP_5 \def (THead k u t1) in (let TMP_6 \def (THead k u t2) 
in (let TMP_7 \def (pc3 c TMP_5 TMP_6) in (let TMP_17 \def (\lambda (x: 
T).(\lambda (H1: (pr3 (CHead c k u) t1 x)).(\lambda (H2: (pr3 (CHead c k u) 
t2 x)).(let TMP_9 \def (\lambda (t: T).(let TMP_8 \def (THead k u t1) in (pr3 
c TMP_8 t))) in (let TMP_11 \def (\lambda (t: T).(let TMP_10 \def (THead k u 
t2) in (pr3 c TMP_10 t))) in (let TMP_12 \def (THead k u x) in (let TMP_13 
\def (pr3_refl c u) in (let TMP_14 \def (pr3_head_12 c u u TMP_13 k t1 x H1) 
in (let TMP_15 \def (pr3_refl c u) in (let TMP_16 \def (pr3_head_12 c u u 
TMP_15 k t2 x H2) in (ex_intro2 T TMP_9 TMP_11 TMP_12 TMP_14 
TMP_16))))))))))) in (ex2_ind T TMP_2 TMP_4 TMP_7 TMP_17 H0))))))))))))).

theorem pc3_pr2_u:
 \forall (c: C).(\forall (t2: T).(\forall (t1: T).((pr2 c t1 t2) \to (\forall 
(t3: T).((pc3 c t2 t3) \to (pc3 c t1 t3))))))
\def
 \lambda (c: C).(\lambda (t2: T).(\lambda (t1: T).(\lambda (H: (pr2 c t1 
t2)).(\lambda (t3: T).(\lambda (H0: (pc3 c t2 t3)).(let H1 \def H0 in (let 
TMP_1 \def (\lambda (t: T).(pr3 c t2 t)) in (let TMP_2 \def (\lambda (t: 
T).(pr3 c t3 t)) in (let TMP_3 \def (pc3 c t1 t3) in (let TMP_7 \def (\lambda 
(x: T).(\lambda (H2: (pr3 c t2 x)).(\lambda (H3: (pr3 c t3 x)).(let TMP_4 
\def (\lambda (t: T).(pr3 c t1 t)) in (let TMP_5 \def (\lambda (t: T).(pr3 c 
t3 t)) in (let TMP_6 \def (pr3_sing c t2 t1 H x H2) in (ex_intro2 T TMP_4 
TMP_5 x TMP_6 H3))))))) in (ex2_ind T TMP_1 TMP_2 TMP_3 TMP_7 H1))))))))))).

theorem pc3_t:
 \forall (t2: T).(\forall (c: C).(\forall (t1: T).((pc3 c t1 t2) \to (\forall 
(t3: T).((pc3 c t2 t3) \to (pc3 c t1 t3))))))
\def
 \lambda (t2: T).(\lambda (c: C).(\lambda (t1: T).(\lambda (H: (pc3 c t1 
t2)).(\lambda (t3: T).(\lambda (H0: (pc3 c t2 t3)).(let H1 \def H0 in (let 
TMP_1 \def (\lambda (t: T).(pr3 c t2 t)) in (let TMP_2 \def (\lambda (t: 
T).(pr3 c t3 t)) in (let TMP_3 \def (pc3 c t1 t3) in (let TMP_15 \def 
(\lambda (x: T).(\lambda (H2: (pr3 c t2 x)).(\lambda (H3: (pr3 c t3 x)).(let 
H4 \def H in (let TMP_4 \def (\lambda (t: T).(pr3 c t1 t)) in (let TMP_5 \def 
(\lambda (t: T).(pr3 c t2 t)) in (let TMP_6 \def (pc3 c t1 t3) in (let TMP_14 
\def (\lambda (x0: T).(\lambda (H5: (pr3 c t1 x0)).(\lambda (H6: (pr3 c t2 
x0)).(let TMP_7 \def (\lambda (t: T).(pr3 c x0 t)) in (let TMP_8 \def 
(\lambda (t: T).(pr3 c x t)) in (let TMP_9 \def (pc3 c t1 t3) in (let TMP_12 
\def (\lambda (x1: T).(\lambda (H7: (pr3 c x0 x1)).(\lambda (H8: (pr3 c x 
x1)).(let TMP_10 \def (pr3_t x0 t1 c H5 x1 H7) in (let TMP_11 \def (pr3_t x 
t3 c H3 x1 H8) in (pc3_pr3_t c t1 x1 TMP_10 t3 TMP_11)))))) in (let TMP_13 
\def (pr3_confluence c t2 x0 H6 x H2) in (ex2_ind T TMP_7 TMP_8 TMP_9 TMP_12 
TMP_13))))))))) in (ex2_ind T TMP_4 TMP_5 TMP_6 TMP_14 H4))))))))) in 
(ex2_ind T TMP_1 TMP_2 TMP_3 TMP_15 H1))))))))))).

theorem pc3_pr2_u2:
 \forall (c: C).(\forall (t0: T).(\forall (t1: T).((pr2 c t0 t1) \to (\forall 
(t2: T).((pc3 c t0 t2) \to (pc3 c t1 t2))))))
\def
 \lambda (c: C).(\lambda (t0: T).(\lambda (t1: T).(\lambda (H: (pr2 c t0 
t1)).(\lambda (t2: T).(\lambda (H0: (pc3 c t0 t2)).(let TMP_1 \def (pc3_pr2_x 
c t1 t0 H) in (pc3_t t0 c t1 TMP_1 t2 H0))))))).

theorem pc3_pr3_conf:
 \forall (c: C).(\forall (t: T).(\forall (t1: T).((pc3 c t t1) \to (\forall 
(t2: T).((pr3 c t t2) \to (pc3 c t2 t1))))))
\def
 \lambda (c: C).(\lambda (t: T).(\lambda (t1: T).(\lambda (H: (pc3 c t 
t1)).(\lambda (t2: T).(\lambda (H0: (pr3 c t t2)).(let TMP_1 \def (pc3_pr3_x 
c t2 t H0) in (pc3_t t c t2 TMP_1 t1 H))))))).

theorem pc3_head_12:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pc3 c u1 u2) \to (\forall 
(k: K).(\forall (t1: T).(\forall (t2: T).((pc3 (CHead c k u2) t1 t2) \to (pc3 
c (THead k u1 t1) (THead k u2 t2)))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pc3 c u1 
u2)).(\lambda (k: K).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pc3 
(CHead c k u2) t1 t2)).(let TMP_1 \def (THead k u2 t1) in (let TMP_2 \def 
(THead k u1 t1) in (let TMP_3 \def (pc3_head_1 c u1 u2 H k t1) in (let TMP_4 
\def (THead k u2 t2) in (let TMP_5 \def (pc3_head_2 c u2 t1 t2 k H0) in 
(pc3_t TMP_1 c TMP_2 TMP_3 TMP_4 TMP_5))))))))))))).

theorem pc3_head_21:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pc3 c u1 u2) \to (\forall 
(k: K).(\forall (t1: T).(\forall (t2: T).((pc3 (CHead c k u1) t1 t2) \to (pc3 
c (THead k u1 t1) (THead k u2 t2)))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pc3 c u1 
u2)).(\lambda (k: K).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pc3 
(CHead c k u1) t1 t2)).(let TMP_1 \def (THead k u1 t2) in (let TMP_2 \def 
(THead k u1 t1) in (let TMP_3 \def (pc3_head_2 c u1 t1 t2 k H0) in (let TMP_4 
\def (THead k u2 t2) in (let TMP_5 \def (pc3_head_1 c u1 u2 H k t2) in (pc3_t 
TMP_1 c TMP_2 TMP_3 TMP_4 TMP_5))))))))))))).

theorem pc3_pr0_pr2_t:
 \forall (u1: T).(\forall (u2: T).((pr0 u2 u1) \to (\forall (c: C).(\forall 
(t1: T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c k u2) t1 t2) \to (pc3 
(CHead c k u1) t1 t2))))))))
\def
 \lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr0 u2 u1)).(\lambda (c: 
C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (k: K).(\lambda (H0: (pr2 
(CHead c k u2) t1 t2)).(let TMP_1 \def (CHead c k u2) in (let TMP_2 \def 
(\lambda (c0: C).(pr2 c0 t1 t2)) in (let TMP_4 \def (\lambda (_: C).(let 
TMP_3 \def (CHead c k u1) in (pc3 TMP_3 t1 t2))) in (let TMP_125 \def 
(\lambda (y: C).(\lambda (H1: (pr2 y t1 t2)).(let TMP_6 \def (\lambda (c0: 
C).(\lambda (t: T).(\lambda (t0: T).((eq C c0 (CHead c k u2)) \to (let TMP_5 
\def (CHead c k u1) in (pc3 TMP_5 t t0)))))) in (let TMP_12 \def (\lambda 
(c0: C).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H2: (pr0 t3 t4)).(\lambda 
(H3: (eq C c0 (CHead c k u2))).(let TMP_7 \def (\lambda (e: C).e) in (let 
TMP_8 \def (CHead c k u2) in (let H4 \def (f_equal C C TMP_7 c0 TMP_8 H3) in 
(let TMP_9 \def (CHead c k u1) in (let TMP_10 \def (CHead c k u1) in (let 
TMP_11 \def (pr2_free TMP_10 t3 t4 H2) in (pc3_pr2_r TMP_9 t3 t4 
TMP_11)))))))))))) in (let TMP_124 \def (\lambda (c0: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H2: (getl i c0 (CHead d (Bind 
Abbr) u))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H3: (pr0 t3 
t4)).(\lambda (t: T).(\lambda (H4: (subst0 i u t4 t)).(\lambda (H5: (eq C c0 
(CHead c k u2))).(let TMP_13 \def (\lambda (e: C).e) in (let TMP_14 \def 
(CHead c k u2) in (let H6 \def (f_equal C C TMP_13 c0 TMP_14 H5) in (let 
TMP_17 \def (\lambda (c1: C).(let TMP_15 \def (Bind Abbr) in (let TMP_16 \def 
(CHead d TMP_15 u) in (getl i c1 TMP_16)))) in (let TMP_18 \def (CHead c k 
u2) in (let H7 \def (eq_ind C c0 TMP_17 H2 TMP_18 H6) in (let TMP_20 \def 
(\lambda (n: nat).((getl n (CHead c k u2) (CHead d (Bind Abbr) u)) \to 
((subst0 n u t4 t) \to (let TMP_19 \def (CHead c k u1) in (pc3 TMP_19 t3 
t))))) in (let TMP_99 \def (\lambda (H8: (getl O (CHead c k u2) (CHead d 
(Bind Abbr) u))).(\lambda (H9: (subst0 O u t4 t)).(let TMP_22 \def (\lambda 
(k0: K).((clear (CHead c k0 u2) (CHead d (Bind Abbr) u)) \to (let TMP_21 \def 
(CHead c k0 u1) in (pc3 TMP_21 t3 t)))) in (let TMP_76 \def (\lambda (b: 
B).(\lambda (H10: (clear (CHead c (Bind b) u2) (CHead d (Bind Abbr) u))).(let 
TMP_23 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow d | (CHead 
c1 _ _) \Rightarrow c1])) in (let TMP_24 \def (Bind Abbr) in (let TMP_25 \def 
(CHead d TMP_24 u) in (let TMP_26 \def (Bind b) in (let TMP_27 \def (CHead c 
TMP_26 u2) in (let TMP_28 \def (Bind Abbr) in (let TMP_29 \def (CHead d 
TMP_28 u) in (let TMP_30 \def (clear_gen_bind b c TMP_29 u2 H10) in (let H11 
\def (f_equal C C TMP_23 TMP_25 TMP_27 TMP_30) in (let TMP_31 \def (\lambda 
(e: C).(match e with [(CSort _) \Rightarrow Abbr | (CHead _ k0 _) \Rightarrow 
(match k0 with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) in 
(let TMP_32 \def (Bind Abbr) in (let TMP_33 \def (CHead d TMP_32 u) in (let 
TMP_34 \def (Bind b) in (let TMP_35 \def (CHead c TMP_34 u2) in (let TMP_36 
\def (Bind Abbr) in (let TMP_37 \def (CHead d TMP_36 u) in (let TMP_38 \def 
(clear_gen_bind b c TMP_37 u2 H10) in (let H12 \def (f_equal C B TMP_31 
TMP_33 TMP_35 TMP_38) in (let TMP_39 \def (\lambda (e: C).(match e with 
[(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) in (let TMP_40 
\def (Bind Abbr) in (let TMP_41 \def (CHead d TMP_40 u) in (let TMP_42 \def 
(Bind b) in (let TMP_43 \def (CHead c TMP_42 u2) in (let TMP_44 \def (Bind 
Abbr) in (let TMP_45 \def (CHead d TMP_44 u) in (let TMP_46 \def 
(clear_gen_bind b c TMP_45 u2 H10) in (let H13 \def (f_equal C T TMP_39 
TMP_41 TMP_43 TMP_46) in (let TMP_74 \def (\lambda (H14: (eq B Abbr 
b)).(\lambda (_: (eq C d c)).(let TMP_47 \def (\lambda (t0: T).(subst0 O t0 
t4 t)) in (let H16 \def (eq_ind T u TMP_47 H9 u2 H13) in (let TMP_50 \def 
(\lambda (b0: B).(let TMP_48 \def (Bind b0) in (let TMP_49 \def (CHead c 
TMP_48 u1) in (pc3 TMP_49 t3 t)))) in (let TMP_51 \def (\lambda (t0: 
T).(subst0 O u1 t4 t0)) in (let TMP_52 \def (\lambda (t0: T).(pr0 t t0)) in 
(let TMP_53 \def (Bind Abbr) in (let TMP_54 \def (CHead c TMP_53 u1) in (let 
TMP_55 \def (pc3 TMP_54 t3 t) in (let TMP_71 \def (\lambda (x: T).(\lambda 
(H17: (subst0 O u1 t4 x)).(\lambda (H18: (pr0 t x)).(let TMP_56 \def (Bind 
Abbr) in (let TMP_57 \def (CHead c TMP_56 u1) in (let TMP_58 \def (Bind Abbr) 
in (let TMP_59 \def (CHead c TMP_58 u1) in (let TMP_60 \def (Bind Abbr) in 
(let TMP_61 \def (CHead c TMP_60 u1) in (let TMP_62 \def (getl_refl Abbr c 
u1) in (let TMP_63 \def (pr2_delta TMP_61 c u1 O TMP_62 t3 t4 H3 x H17) in 
(let TMP_64 \def (pr3_pr2 TMP_59 t3 x TMP_63) in (let TMP_65 \def (Bind Abbr) 
in (let TMP_66 \def (CHead c TMP_65 u1) in (let TMP_67 \def (Bind Abbr) in 
(let TMP_68 \def (CHead c TMP_67 u1) in (let TMP_69 \def (pr2_free TMP_68 t x 
H18) in (let TMP_70 \def (pr3_pr2 TMP_66 t x TMP_69) in (pc3_pr3_t TMP_57 t3 
x TMP_64 t TMP_70))))))))))))))))))) in (let TMP_72 \def (pr0_subst0_fwd u2 
t4 t O H16 u1 H) in (let TMP_73 \def (ex2_ind T TMP_51 TMP_52 TMP_55 TMP_71 
TMP_72) in (eq_ind B Abbr TMP_50 TMP_73 b H14)))))))))))))) in (let TMP_75 
\def (TMP_74 H12) in (TMP_75 H11)))))))))))))))))))))))))))))))) in (let 
TMP_94 \def (\lambda (f: F).(\lambda (H10: (clear (CHead c (Flat f) u2) 
(CHead d (Bind Abbr) u))).(let TMP_77 \def (Bind Abbr) in (let TMP_78 \def 
(CHead d TMP_77 u) in (let TMP_79 \def (Bind Abbr) in (let TMP_80 \def (CHead 
d TMP_79 u) in (let TMP_81 \def (Bind Abbr) in (let TMP_82 \def (CHead d 
TMP_81 u) in (let TMP_83 \def (getl_refl Abbr d u) in (let TMP_84 \def 
(pr2_delta TMP_82 d u O TMP_83 t3 t4 H3 t H9) in (let TMP_85 \def (pc3_pr2_r 
TMP_80 t3 t TMP_84) in (let TMP_86 \def (Flat f) in (let TMP_87 \def (CHead c 
TMP_86 u1) in (let TMP_88 \def (Bind Abbr) in (let TMP_89 \def (CHead d 
TMP_88 u) in (let TMP_90 \def (Bind Abbr) in (let TMP_91 \def (CHead d TMP_90 
u) in (let TMP_92 \def (clear_gen_flat f c TMP_91 u2 H10) in (let TMP_93 \def 
(clear_flat c TMP_89 TMP_92 f u1) in (clear_pc3_trans TMP_78 t3 t TMP_85 
TMP_87 TMP_93)))))))))))))))))))) in (let TMP_95 \def (CHead c k u2) in (let 
TMP_96 \def (Bind Abbr) in (let TMP_97 \def (CHead d TMP_96 u) in (let TMP_98 
\def (getl_gen_O TMP_95 TMP_97 H8) in (K_ind TMP_22 TMP_76 TMP_94 k 
TMP_98)))))))))) in (let TMP_123 \def (\lambda (i0: nat).(\lambda (IHi: 
(((getl i0 (CHead c k u2) (CHead d (Bind Abbr) u)) \to ((subst0 i0 u t4 t) 
\to (pc3 (CHead c k u1) t3 t))))).(\lambda (H8: (getl (S i0) (CHead c k u2) 
(CHead d (Bind Abbr) u))).(\lambda (H9: (subst0 (S i0) u t4 t)).(let TMP_101 
\def (\lambda (k0: K).((((getl i0 (CHead c k0 u2) (CHead d (Bind Abbr) u)) 
\to ((subst0 i0 u t4 t) \to (pc3 (CHead c k0 u1) t3 t)))) \to ((getl (r k0 
i0) c (CHead d (Bind Abbr) u)) \to (let TMP_100 \def (CHead c k0 u1) in (pc3 
TMP_100 t3 t))))) in (let TMP_112 \def (\lambda (b: B).(\lambda (_: (((getl 
i0 (CHead c (Bind b) u2) (CHead d (Bind Abbr) u)) \to ((subst0 i0 u t4 t) \to 
(pc3 (CHead c (Bind b) u1) t3 t))))).(\lambda (H10: (getl (r (Bind b) i0) c 
(CHead d (Bind Abbr) u))).(let TMP_102 \def (Bind b) in (let TMP_103 \def 
(CHead c TMP_102 u1) in (let TMP_104 \def (Bind b) in (let TMP_105 \def 
(CHead c TMP_104 u1) in (let TMP_106 \def (S i0) in (let TMP_107 \def (Bind 
b) in (let TMP_108 \def (Bind Abbr) in (let TMP_109 \def (CHead d TMP_108 u) 
in (let TMP_110 \def (getl_head TMP_107 i0 c TMP_109 H10 u1) in (let TMP_111 
\def (pr2_delta TMP_105 d u TMP_106 TMP_110 t3 t4 H3 t H9) in (pc3_pr2_r 
TMP_103 t3 t TMP_111)))))))))))))) in (let TMP_119 \def (\lambda (f: 
F).(\lambda (_: (((getl i0 (CHead c (Flat f) u2) (CHead d (Bind Abbr) u)) \to 
((subst0 i0 u t4 t) \to (pc3 (CHead c (Flat f) u1) t3 t))))).(\lambda (H10: 
(getl (r (Flat f) i0) c (CHead d (Bind Abbr) u))).(let TMP_113 \def (Flat f) 
in (let TMP_114 \def (CHead c TMP_113 u1) in (let TMP_115 \def (Flat f) in 
(let TMP_116 \def (r TMP_115 i0) in (let TMP_117 \def (pr2_delta c d u 
TMP_116 H10 t3 t4 H3 t H9) in (let TMP_118 \def (pr2_cflat c t3 t TMP_117 f 
u1) in (pc3_pr2_r TMP_114 t3 t TMP_118)))))))))) in (let TMP_120 \def (Bind 
Abbr) in (let TMP_121 \def (CHead d TMP_120 u) in (let TMP_122 \def 
(getl_gen_S k c TMP_121 u2 i0 H8) in (K_ind TMP_101 TMP_112 TMP_119 k IHi 
TMP_122))))))))))) in (nat_ind TMP_20 TMP_99 TMP_123 i H7 
H4))))))))))))))))))))) in (pr2_ind TMP_6 TMP_12 TMP_124 y t1 t2 H1)))))) in 
(insert_eq C TMP_1 TMP_2 TMP_4 TMP_125 H0)))))))))))).

theorem pc3_pr2_pr2_t:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr2 c u2 u1) \to (\forall 
(t1: T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c k u2) t1 t2) \to (pc3 
(CHead c k u1) t1 t2))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr2 c u2 
u1)).(let TMP_2 \def (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: 
T).(\forall (t1: T).(\forall (t2: T).(\forall (k: K).((pr2 (CHead c0 k t) t1 
t2) \to (let TMP_1 \def (CHead c0 k t0) in (pc3 TMP_1 t1 t2))))))))) in (let 
TMP_3 \def (\lambda (c0: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: 
(pr0 t1 t2)).(\lambda (t0: T).(\lambda (t3: T).(\lambda (k: K).(\lambda (H1: 
(pr2 (CHead c0 k t1) t0 t3)).(pc3_pr0_pr2_t t2 t1 H0 c0 t0 t3 k H1))))))))) 
in (let TMP_144 \def (\lambda (c0: C).(\lambda (d: C).(\lambda (u: 
T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind Abbr) 
u))).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H1: (pr0 t1 t2)).(\lambda 
(t: T).(\lambda (H2: (subst0 i u t2 t)).(\lambda (t0: T).(\lambda (t3: 
T).(\lambda (k: K).(\lambda (H3: (pr2 (CHead c0 k t1) t0 t3)).(let TMP_4 \def 
(CHead c0 k t1) in (let TMP_5 \def (\lambda (c1: C).(pr2 c1 t0 t3)) in (let 
TMP_7 \def (\lambda (_: C).(let TMP_6 \def (CHead c0 k t) in (pc3 TMP_6 t0 
t3))) in (let TMP_143 \def (\lambda (y: C).(\lambda (H4: (pr2 y t0 t3)).(let 
TMP_9 \def (\lambda (c1: C).(\lambda (t4: T).(\lambda (t5: T).((eq C c1 
(CHead c0 k t1)) \to (let TMP_8 \def (CHead c0 k t) in (pc3 TMP_8 t4 t5)))))) 
in (let TMP_13 \def (\lambda (c1: C).(\lambda (t4: T).(\lambda (t5: 
T).(\lambda (H5: (pr0 t4 t5)).(\lambda (_: (eq C c1 (CHead c0 k t1))).(let 
TMP_10 \def (CHead c0 k t) in (let TMP_11 \def (CHead c0 k t) in (let TMP_12 
\def (pr2_free TMP_11 t4 t5 H5) in (pc3_pr2_r TMP_10 t4 t5 TMP_12))))))))) in 
(let TMP_142 \def (\lambda (c1: C).(\lambda (d0: C).(\lambda (u0: T).(\lambda 
(i0: nat).(\lambda (H5: (getl i0 c1 (CHead d0 (Bind Abbr) u0))).(\lambda (t4: 
T).(\lambda (t5: T).(\lambda (H6: (pr0 t4 t5)).(\lambda (t6: T).(\lambda (H7: 
(subst0 i0 u0 t5 t6)).(\lambda (H8: (eq C c1 (CHead c0 k t1))).(let TMP_16 
\def (\lambda (c2: C).(let TMP_14 \def (Bind Abbr) in (let TMP_15 \def (CHead 
d0 TMP_14 u0) in (getl i0 c2 TMP_15)))) in (let TMP_17 \def (CHead c0 k t1) 
in (let H9 \def (eq_ind C c1 TMP_16 H5 TMP_17 H8) in (let TMP_19 \def 
(\lambda (n: nat).((getl n (CHead c0 k t1) (CHead d0 (Bind Abbr) u0)) \to 
((subst0 n u0 t5 t6) \to (let TMP_18 \def (CHead c0 k t) in (pc3 TMP_18 t4 
t6))))) in (let TMP_117 \def (\lambda (H10: (getl O (CHead c0 k t1) (CHead d0 
(Bind Abbr) u0))).(\lambda (H11: (subst0 O u0 t5 t6)).(let TMP_21 \def 
(\lambda (k0: K).((clear (CHead c0 k0 t1) (CHead d0 (Bind Abbr) u0)) \to (let 
TMP_20 \def (CHead c0 k0 t) in (pc3 TMP_20 t4 t6)))) in (let TMP_94 \def 
(\lambda (b: B).(\lambda (H12: (clear (CHead c0 (Bind b) t1) (CHead d0 (Bind 
Abbr) u0))).(let TMP_22 \def (\lambda (e: C).(match e with [(CSort _) 
\Rightarrow d0 | (CHead c2 _ _) \Rightarrow c2])) in (let TMP_23 \def (Bind 
Abbr) in (let TMP_24 \def (CHead d0 TMP_23 u0) in (let TMP_25 \def (Bind b) 
in (let TMP_26 \def (CHead c0 TMP_25 t1) in (let TMP_27 \def (Bind Abbr) in 
(let TMP_28 \def (CHead d0 TMP_27 u0) in (let TMP_29 \def (clear_gen_bind b 
c0 TMP_28 t1 H12) in (let H13 \def (f_equal C C TMP_22 TMP_24 TMP_26 TMP_29) 
in (let TMP_30 \def (\lambda (e: C).(match e with [(CSort _) \Rightarrow Abbr 
| (CHead _ k0 _) \Rightarrow (match k0 with [(Bind b0) \Rightarrow b0 | (Flat 
_) \Rightarrow Abbr])])) in (let TMP_31 \def (Bind Abbr) in (let TMP_32 \def 
(CHead d0 TMP_31 u0) in (let TMP_33 \def (Bind b) in (let TMP_34 \def (CHead 
c0 TMP_33 t1) in (let TMP_35 \def (Bind Abbr) in (let TMP_36 \def (CHead d0 
TMP_35 u0) in (let TMP_37 \def (clear_gen_bind b c0 TMP_36 t1 H12) in (let 
H14 \def (f_equal C B TMP_30 TMP_32 TMP_34 TMP_37) in (let TMP_38 \def 
(\lambda (e: C).(match e with [(CSort _) \Rightarrow u0 | (CHead _ _ t7) 
\Rightarrow t7])) in (let TMP_39 \def (Bind Abbr) in (let TMP_40 \def (CHead 
d0 TMP_39 u0) in (let TMP_41 \def (Bind b) in (let TMP_42 \def (CHead c0 
TMP_41 t1) in (let TMP_43 \def (Bind Abbr) in (let TMP_44 \def (CHead d0 
TMP_43 u0) in (let TMP_45 \def (clear_gen_bind b c0 TMP_44 t1 H12) in (let 
H15 \def (f_equal C T TMP_38 TMP_40 TMP_42 TMP_45) in (let TMP_92 \def 
(\lambda (H16: (eq B Abbr b)).(\lambda (_: (eq C d0 c0)).(let TMP_46 \def 
(\lambda (t7: T).(subst0 O t7 t5 t6)) in (let H18 \def (eq_ind T u0 TMP_46 
H11 t1 H15) in (let TMP_49 \def (\lambda (b0: B).(let TMP_47 \def (Bind b0) 
in (let TMP_48 \def (CHead c0 TMP_47 t) in (pc3 TMP_48 t4 t6)))) in (let 
TMP_50 \def (\lambda (t7: T).(subst0 O t2 t5 t7)) in (let TMP_51 \def 
(\lambda (t7: T).(pr0 t6 t7)) in (let TMP_52 \def (Bind Abbr) in (let TMP_53 
\def (CHead c0 TMP_52 t) in (let TMP_54 \def (pc3 TMP_53 t4 t6) in (let 
TMP_89 \def (\lambda (x: T).(\lambda (H19: (subst0 O t2 t5 x)).(\lambda (H20: 
(pr0 t6 x)).(let TMP_55 \def (\lambda (t7: T).(subst0 O t t5 t7)) in (let 
TMP_58 \def (\lambda (t7: T).(let TMP_56 \def (plus i O) in (let TMP_57 \def 
(S TMP_56) in (subst0 TMP_57 u x t7)))) in (let TMP_59 \def (Bind Abbr) in 
(let TMP_60 \def (CHead c0 TMP_59 t) in (let TMP_61 \def (pc3 TMP_60 t4 t6) 
in (let TMP_87 \def (\lambda (x0: T).(\lambda (H21: (subst0 O t t5 
x0)).(\lambda (H22: (subst0 (S (plus i O)) u x x0)).(let TMP_62 \def (plus i 
O) in (let TMP_63 \def (plus i O) in (let TMP_64 \def (plus_n_O i) in (let 
TMP_65 \def (sym_eq nat i TMP_63 TMP_64) in (let H23 \def (f_equal nat nat S 
TMP_62 i TMP_65) in (let TMP_66 \def (plus i O) in (let TMP_67 \def (S 
TMP_66) in (let TMP_68 \def (\lambda (n: nat).(subst0 n u x x0)) in (let 
TMP_69 \def (S i) in (let H24 \def (eq_ind nat TMP_67 TMP_68 H22 TMP_69 H23) 
in (let TMP_70 \def (Bind Abbr) in (let TMP_71 \def (CHead c0 TMP_70 t) in 
(let TMP_72 \def (Bind Abbr) in (let TMP_73 \def (CHead c0 TMP_72 t) in (let 
TMP_74 \def (getl_refl Abbr c0 t) in (let TMP_75 \def (pr2_delta TMP_73 c0 t 
O TMP_74 t4 t5 H6 x0 H21) in (let TMP_76 \def (Bind Abbr) in (let TMP_77 \def 
(CHead c0 TMP_76 t) in (let TMP_78 \def (Bind Abbr) in (let TMP_79 \def 
(CHead c0 TMP_78 t) in (let TMP_80 \def (S i) in (let TMP_81 \def (Bind Abbr) 
in (let TMP_82 \def (Bind Abbr) in (let TMP_83 \def (CHead d TMP_82 u) in 
(let TMP_84 \def (getl_head TMP_81 i c0 TMP_83 H0 t) in (let TMP_85 \def 
(pr2_delta TMP_79 d u TMP_80 TMP_84 t6 x H20 x0 H24) in (let TMP_86 \def 
(pc3_pr2_x TMP_77 x0 t6 TMP_85) in (pc3_pr2_u TMP_71 x0 t4 TMP_75 t6 
TMP_86))))))))))))))))))))))))))))))) in (let TMP_88 \def (subst0_subst0_back 
t5 x t2 O H19 t u i H2) in (ex2_ind T TMP_55 TMP_58 TMP_61 TMP_87 
TMP_88))))))))))) in (let TMP_90 \def (pr0_subst0_fwd t1 t5 t6 O H18 t2 H1) 
in (let TMP_91 \def (ex2_ind T TMP_50 TMP_51 TMP_54 TMP_89 TMP_90) in (eq_ind 
B Abbr TMP_49 TMP_91 b H16)))))))))))))) in (let TMP_93 \def (TMP_92 H14) in 
(TMP_93 H13)))))))))))))))))))))))))))))))) in (let TMP_112 \def (\lambda (f: 
F).(\lambda (H12: (clear (CHead c0 (Flat f) t1) (CHead d0 (Bind Abbr) 
u0))).(let TMP_95 \def (Bind Abbr) in (let TMP_96 \def (CHead d0 TMP_95 u0) 
in (let TMP_97 \def (Bind Abbr) in (let TMP_98 \def (CHead d0 TMP_97 u0) in 
(let TMP_99 \def (Bind Abbr) in (let TMP_100 \def (CHead d0 TMP_99 u0) in 
(let TMP_101 \def (getl_refl Abbr d0 u0) in (let TMP_102 \def (pr2_delta 
TMP_100 d0 u0 O TMP_101 t4 t5 H6 t6 H11) in (let TMP_103 \def (pc3_pr2_r 
TMP_98 t4 t6 TMP_102) in (let TMP_104 \def (Flat f) in (let TMP_105 \def 
(CHead c0 TMP_104 t) in (let TMP_106 \def (Bind Abbr) in (let TMP_107 \def 
(CHead d0 TMP_106 u0) in (let TMP_108 \def (Bind Abbr) in (let TMP_109 \def 
(CHead d0 TMP_108 u0) in (let TMP_110 \def (clear_gen_flat f c0 TMP_109 t1 
H12) in (let TMP_111 \def (clear_flat c0 TMP_107 TMP_110 f t) in 
(clear_pc3_trans TMP_96 t4 t6 TMP_103 TMP_105 TMP_111)))))))))))))))))))) in 
(let TMP_113 \def (CHead c0 k t1) in (let TMP_114 \def (Bind Abbr) in (let 
TMP_115 \def (CHead d0 TMP_114 u0) in (let TMP_116 \def (getl_gen_O TMP_113 
TMP_115 H10) in (K_ind TMP_21 TMP_94 TMP_112 k TMP_116)))))))))) in (let 
TMP_141 \def (\lambda (i1: nat).(\lambda (_: (((getl i1 (CHead c0 k t1) 
(CHead d0 (Bind Abbr) u0)) \to ((subst0 i1 u0 t5 t6) \to (pc3 (CHead c0 k t) 
t4 t6))))).(\lambda (H10: (getl (S i1) (CHead c0 k t1) (CHead d0 (Bind Abbr) 
u0))).(\lambda (H11: (subst0 (S i1) u0 t5 t6)).(let TMP_119 \def (\lambda 
(k0: K).((getl (r k0 i1) c0 (CHead d0 (Bind Abbr) u0)) \to (let TMP_118 \def 
(CHead c0 k0 t) in (pc3 TMP_118 t4 t6)))) in (let TMP_130 \def (\lambda (b: 
B).(\lambda (H12: (getl (r (Bind b) i1) c0 (CHead d0 (Bind Abbr) u0))).(let 
TMP_120 \def (Bind b) in (let TMP_121 \def (CHead c0 TMP_120 t) in (let 
TMP_122 \def (Bind b) in (let TMP_123 \def (CHead c0 TMP_122 t) in (let 
TMP_124 \def (S i1) in (let TMP_125 \def (Bind b) in (let TMP_126 \def (Bind 
Abbr) in (let TMP_127 \def (CHead d0 TMP_126 u0) in (let TMP_128 \def 
(getl_head TMP_125 i1 c0 TMP_127 H12 t) in (let TMP_129 \def (pr2_delta 
TMP_123 d0 u0 TMP_124 TMP_128 t4 t5 H6 t6 H11) in (pc3_pr2_r TMP_121 t4 t6 
TMP_129))))))))))))) in (let TMP_137 \def (\lambda (f: F).(\lambda (H12: 
(getl (r (Flat f) i1) c0 (CHead d0 (Bind Abbr) u0))).(let TMP_131 \def (Flat 
f) in (let TMP_132 \def (CHead c0 TMP_131 t) in (let TMP_133 \def (Flat f) in 
(let TMP_134 \def (r TMP_133 i1) in (let TMP_135 \def (pr2_delta c0 d0 u0 
TMP_134 H12 t4 t5 H6 t6 H11) in (let TMP_136 \def (pr2_cflat c0 t4 t6 TMP_135 
f t) in (pc3_pr2_r TMP_132 t4 t6 TMP_136))))))))) in (let TMP_138 \def (Bind 
Abbr) in (let TMP_139 \def (CHead d0 TMP_138 u0) in (let TMP_140 \def 
(getl_gen_S k c0 TMP_139 t1 i1 H10) in (K_ind TMP_119 TMP_130 TMP_137 k 
TMP_140))))))))))) in (nat_ind TMP_19 TMP_117 TMP_141 i0 H9 
H7)))))))))))))))))) in (pr2_ind TMP_9 TMP_13 TMP_142 y t0 t3 H4)))))) in 
(insert_eq C TMP_4 TMP_5 TMP_7 TMP_143 H3))))))))))))))))))) in (pr2_ind 
TMP_2 TMP_3 TMP_144 c u2 u1 H))))))).

theorem pc3_pr2_pr3_t:
 \forall (c: C).(\forall (u2: T).(\forall (t1: T).(\forall (t2: T).(\forall 
(k: K).((pr3 (CHead c k u2) t1 t2) \to (\forall (u1: T).((pr2 c u2 u1) \to 
(pc3 (CHead c k u1) t1 t2))))))))
\def
 \lambda (c: C).(\lambda (u2: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(k: K).(\lambda (H: (pr3 (CHead c k u2) t1 t2)).(let TMP_1 \def (CHead c k 
u2) in (let TMP_3 \def (\lambda (t: T).(\lambda (t0: T).(\forall (u1: 
T).((pr2 c u2 u1) \to (let TMP_2 \def (CHead c k u1) in (pc3 TMP_2 t t0)))))) 
in (let TMP_5 \def (\lambda (t: T).(\lambda (u1: T).(\lambda (_: (pr2 c u2 
u1)).(let TMP_4 \def (CHead c k u1) in (pc3_refl TMP_4 t))))) in (let TMP_9 
\def (\lambda (t0: T).(\lambda (t3: T).(\lambda (H0: (pr2 (CHead c k u2) t3 
t0)).(\lambda (t4: T).(\lambda (_: (pr3 (CHead c k u2) t0 t4)).(\lambda (H2: 
((\forall (u1: T).((pr2 c u2 u1) \to (pc3 (CHead c k u1) t0 t4))))).(\lambda 
(u1: T).(\lambda (H3: (pr2 c u2 u1)).(let TMP_6 \def (CHead c k u1) in (let 
TMP_7 \def (pc3_pr2_pr2_t c u1 u2 H3 t3 t0 k H0) in (let TMP_8 \def (H2 u1 
H3) in (pc3_t t0 TMP_6 t3 TMP_7 t4 TMP_8)))))))))))) in (pr3_ind TMP_1 TMP_3 
TMP_5 TMP_9 t1 t2 H)))))))))).

theorem pc3_pr3_pc3_t:
 \forall (c: C).(\forall (u1: T).(\forall (u2: T).((pr3 c u2 u1) \to (\forall 
(t1: T).(\forall (t2: T).(\forall (k: K).((pc3 (CHead c k u2) t1 t2) \to (pc3 
(CHead c k u1) t1 t2))))))))
\def
 \lambda (c: C).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr3 c u2 
u1)).(let TMP_2 \def (\lambda (t: T).(\lambda (t0: T).(\forall (t1: 
T).(\forall (t2: T).(\forall (k: K).((pc3 (CHead c k t) t1 t2) \to (let TMP_1 
\def (CHead c k t0) in (pc3 TMP_1 t1 t2)))))))) in (let TMP_3 \def (\lambda 
(t: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (k: K).(\lambda (H0: (pc3 
(CHead c k t) t1 t2)).H0))))) in (let TMP_17 \def (\lambda (t2: T).(\lambda 
(t1: T).(\lambda (H0: (pr2 c t1 t2)).(\lambda (t3: T).(\lambda (_: (pr3 c t2 
t3)).(\lambda (H2: ((\forall (t4: T).(\forall (t5: T).(\forall (k: K).((pc3 
(CHead c k t2) t4 t5) \to (pc3 (CHead c k t3) t4 t5))))))).(\lambda (t0: 
T).(\lambda (t4: T).(\lambda (k: K).(\lambda (H3: (pc3 (CHead c k t1) t0 
t4)).(let H4 \def H3 in (let TMP_5 \def (\lambda (t: T).(let TMP_4 \def 
(CHead c k t1) in (pr3 TMP_4 t0 t))) in (let TMP_7 \def (\lambda (t: T).(let 
TMP_6 \def (CHead c k t1) in (pr3 TMP_6 t4 t))) in (let TMP_8 \def (CHead c k 
t2) in (let TMP_9 \def (pc3 TMP_8 t0 t4) in (let TMP_15 \def (\lambda (x: 
T).(\lambda (H5: (pr3 (CHead c k t1) t0 x)).(\lambda (H6: (pr3 (CHead c k t1) 
t4 x)).(let TMP_10 \def (CHead c k t2) in (let TMP_11 \def (pc3_pr2_pr3_t c 
t1 t0 x k H5 t2 H0) in (let TMP_12 \def (CHead c k t2) in (let TMP_13 \def 
(pc3_pr2_pr3_t c t1 t4 x k H6 t2 H0) in (let TMP_14 \def (pc3_s TMP_12 x t4 
TMP_13) in (pc3_t x TMP_10 t0 TMP_11 t4 TMP_14))))))))) in (let TMP_16 \def 
(ex2_ind T TMP_5 TMP_7 TMP_9 TMP_15 H4) in (H2 t0 t4 k 
TMP_16)))))))))))))))))) in (pr3_ind c TMP_2 TMP_3 TMP_17 u2 u1 H))))))).

theorem pc3_lift:
 \forall (c: C).(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h 
d c e) \to (\forall (t1: T).(\forall (t2: T).((pc3 e t1 t2) \to (pc3 c (lift 
h d t1) (lift h d t2)))))))))
\def
 \lambda (c: C).(\lambda (e: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda 
(H: (drop h d c e)).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H0: (pc3 e t1 
t2)).(let H1 \def H0 in (let TMP_1 \def (\lambda (t: T).(pr3 e t1 t)) in (let 
TMP_2 \def (\lambda (t: T).(pr3 e t2 t)) in (let TMP_3 \def (lift h d t1) in 
(let TMP_4 \def (lift h d t2) in (let TMP_5 \def (pc3 c TMP_3 TMP_4) in (let 
TMP_11 \def (\lambda (x: T).(\lambda (H2: (pr3 e t1 x)).(\lambda (H3: (pr3 e 
t2 x)).(let TMP_6 \def (lift h d t1) in (let TMP_7 \def (lift h d x) in (let 
TMP_8 \def (pr3_lift c e h d H t1 x H2) in (let TMP_9 \def (lift h d t2) in 
(let TMP_10 \def (pr3_lift c e h d H t2 x H3) in (pc3_pr3_t c TMP_6 TMP_7 
TMP_8 TMP_9 TMP_10))))))))) in (ex2_ind T TMP_1 TMP_2 TMP_5 TMP_11 
H1))))))))))))))).

theorem pc3_eta:
 \forall (c: C).(\forall (t: T).(\forall (w: T).(\forall (u: T).((pc3 c t 
(THead (Bind Abst) w u)) \to (\forall (v: T).((pc3 c v w) \to (pc3 c (THead 
(Bind Abst) v (THead (Flat Appl) (TLRef O) (lift (S O) O t))) t)))))))
\def
 \lambda (c: C).(\lambda (t: T).(\lambda (w: T).(\lambda (u: T).(\lambda (H: 
(pc3 c t (THead (Bind Abst) w u))).(\lambda (v: T).(\lambda (H0: (pc3 c v 
w)).(let TMP_1 \def (Bind Abst) in (let TMP_2 \def (Flat Appl) in (let TMP_3 
\def (TLRef O) in (let TMP_4 \def (S O) in (let TMP_5 \def (Bind Abst) in 
(let TMP_6 \def (THead TMP_5 w u) in (let TMP_7 \def (lift TMP_4 O TMP_6) in 
(let TMP_8 \def (THead TMP_2 TMP_3 TMP_7) in (let TMP_9 \def (THead TMP_1 w 
TMP_8) in (let TMP_10 \def (Bind Abst) in (let TMP_11 \def (Flat Appl) in 
(let TMP_12 \def (TLRef O) in (let TMP_13 \def (S O) in (let TMP_14 \def 
(lift TMP_13 O t) in (let TMP_15 \def (THead TMP_11 TMP_12 TMP_14) in (let 
TMP_16 \def (THead TMP_10 v TMP_15) in (let TMP_17 \def (Bind Abst) in (let 
TMP_18 \def (Flat Appl) in (let TMP_19 \def (TLRef O) in (let TMP_20 \def (S 
O) in (let TMP_21 \def (lift TMP_20 O t) in (let TMP_22 \def (THead TMP_18 
TMP_19 TMP_21) in (let TMP_23 \def (Flat Appl) in (let TMP_24 \def (TLRef O) 
in (let TMP_25 \def (S O) in (let TMP_26 \def (Bind Abst) in (let TMP_27 \def 
(THead TMP_26 w u) in (let TMP_28 \def (lift TMP_25 O TMP_27) in (let TMP_29 
\def (THead TMP_23 TMP_24 TMP_28) in (let TMP_30 \def (Bind Abst) in (let 
TMP_31 \def (CHead c TMP_30 v) in (let TMP_32 \def (S O) in (let TMP_33 \def 
(lift TMP_32 O t) in (let TMP_34 \def (S O) in (let TMP_35 \def (Bind Abst) 
in (let TMP_36 \def (THead TMP_35 w u) in (let TMP_37 \def (lift TMP_34 O 
TMP_36) in (let TMP_38 \def (Bind Abst) in (let TMP_39 \def (CHead c TMP_38 
v) in (let TMP_40 \def (S O) in (let TMP_41 \def (Bind Abst) in (let TMP_42 
\def (drop_refl c) in (let TMP_43 \def (drop_drop TMP_41 O c c TMP_42 v) in 
(let TMP_44 \def (Bind Abst) in (let TMP_45 \def (THead TMP_44 w u) in (let 
TMP_46 \def (pc3_lift TMP_39 c TMP_40 O TMP_43 t TMP_45 H) in (let TMP_47 
\def (TLRef O) in (let TMP_48 \def (pc3_thin_dx TMP_31 TMP_33 TMP_37 TMP_46 
TMP_47 Appl) in (let TMP_49 \def (pc3_head_21 c v w H0 TMP_17 TMP_22 TMP_29 
TMP_48) in (let TMP_50 \def (Bind Abst) in (let TMP_51 \def (THead TMP_50 w 
u) in (let TMP_52 \def (Bind Abst) in (let TMP_53 \def (Flat Appl) in (let 
TMP_54 \def (TLRef O) in (let TMP_55 \def (S O) in (let TMP_56 \def (Bind 
Abst) in (let TMP_57 \def (THead TMP_56 w u) in (let TMP_58 \def (lift TMP_55 
O TMP_57) in (let TMP_59 \def (THead TMP_53 TMP_54 TMP_58) in (let TMP_60 
\def (THead TMP_52 w TMP_59) in (let TMP_61 \def (Bind Abst) in (let TMP_62 
\def (Flat Appl) in (let TMP_63 \def (TLRef O) in (let TMP_64 \def (S O) in 
(let TMP_65 \def (Bind Abst) in (let TMP_66 \def (THead TMP_65 w u) in (let 
TMP_67 \def (lift TMP_64 O TMP_66) in (let TMP_68 \def (THead TMP_62 TMP_63 
TMP_67) in (let TMP_69 \def (THead TMP_61 w TMP_68) in (let TMP_70 \def (Bind 
Abst) in (let TMP_71 \def (THead TMP_70 w u) in (let TMP_72 \def (pr3_refl c 
w) in (let TMP_73 \def (pr3_eta c w u w TMP_72) in (let TMP_74 \def 
(pc3_pr3_r c TMP_69 TMP_71 TMP_73) in (let TMP_75 \def (Bind Abst) in (let 
TMP_76 \def (THead TMP_75 w u) in (let TMP_77 \def (pc3_s c TMP_76 t H) in 
(let TMP_78 \def (pc3_t TMP_51 c TMP_60 TMP_74 t TMP_77) in (pc3_t TMP_9 c 
TMP_16 TMP_49 t 
TMP_78))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))).

