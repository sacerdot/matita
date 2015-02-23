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

include "basic_1/pr0/subst0.ma".

include "basic_1/subst1/fwd.ma".

theorem pr0_delta1:
 \forall (u1: T).(\forall (u2: T).((pr0 u1 u2) \to (\forall (t1: T).(\forall 
(t2: T).((pr0 t1 t2) \to (\forall (w: T).((subst1 O u2 t2 w) \to (pr0 (THead 
(Bind Abbr) u1 t1) (THead (Bind Abbr) u2 w)))))))))
\def
 \lambda (u1: T).(\lambda (u2: T).(\lambda (H: (pr0 u1 u2)).(\lambda (t1: 
T).(\lambda (t2: T).(\lambda (H0: (pr0 t1 t2)).(\lambda (w: T).(\lambda (H1: 
(subst1 O u2 t2 w)).(let TMP_5 \def (\lambda (t: T).(let TMP_1 \def (Bind 
Abbr) in (let TMP_2 \def (THead TMP_1 u1 t1) in (let TMP_3 \def (Bind Abbr) 
in (let TMP_4 \def (THead TMP_3 u2 t) in (pr0 TMP_2 TMP_4)))))) in (let TMP_6 
\def (Bind Abbr) in (let TMP_7 \def (pr0_comp u1 u2 H t1 t2 H0 TMP_6) in (let 
TMP_8 \def (\lambda (t0: T).(\lambda (H2: (subst0 O u2 t2 t0)).(pr0_delta u1 
u2 H t1 t2 H0 t0 H2))) in (subst1_ind O u2 t2 TMP_5 TMP_7 TMP_8 w 
H1)))))))))))).

theorem pr0_subst1_back:
 \forall (u2: T).(\forall (t1: T).(\forall (t2: T).(\forall (i: nat).((subst1 
i u2 t1 t2) \to (\forall (u1: T).((pr0 u1 u2) \to (ex2 T (\lambda (t: 
T).(subst1 i u1 t1 t)) (\lambda (t: T).(pr0 t t2)))))))))
\def
 \lambda (u2: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (i: nat).(\lambda 
(H: (subst1 i u2 t1 t2)).(let TMP_3 \def (\lambda (t: T).(\forall (u1: 
T).((pr0 u1 u2) \to (let TMP_1 \def (\lambda (t0: T).(subst1 i u1 t1 t0)) in 
(let TMP_2 \def (\lambda (t0: T).(pr0 t0 t)) in (ex2 T TMP_1 TMP_2)))))) in 
(let TMP_8 \def (\lambda (u1: T).(\lambda (_: (pr0 u1 u2)).(let TMP_4 \def 
(\lambda (t: T).(subst1 i u1 t1 t)) in (let TMP_5 \def (\lambda (t: T).(pr0 t 
t1)) in (let TMP_6 \def (subst1_refl i u1 t1) in (let TMP_7 \def (pr0_refl 
t1) in (ex_intro2 T TMP_4 TMP_5 t1 TMP_6 TMP_7))))))) in (let TMP_19 \def 
(\lambda (t0: T).(\lambda (H0: (subst0 i u2 t1 t0)).(\lambda (u1: T).(\lambda 
(H1: (pr0 u1 u2)).(let TMP_9 \def (\lambda (t: T).(subst0 i u1 t1 t)) in (let 
TMP_10 \def (\lambda (t: T).(pr0 t t0)) in (let TMP_11 \def (\lambda (t: 
T).(subst1 i u1 t1 t)) in (let TMP_12 \def (\lambda (t: T).(pr0 t t0)) in 
(let TMP_13 \def (ex2 T TMP_11 TMP_12) in (let TMP_17 \def (\lambda (x: 
T).(\lambda (H2: (subst0 i u1 t1 x)).(\lambda (H3: (pr0 x t0)).(let TMP_14 
\def (\lambda (t: T).(subst1 i u1 t1 t)) in (let TMP_15 \def (\lambda (t: 
T).(pr0 t t0)) in (let TMP_16 \def (subst1_single i u1 t1 x H2) in (ex_intro2 
T TMP_14 TMP_15 x TMP_16 H3))))))) in (let TMP_18 \def (pr0_subst0_back u2 t1 
t0 i H0 u1 H1) in (ex2_ind T TMP_9 TMP_10 TMP_13 TMP_17 TMP_18)))))))))))) in 
(subst1_ind i u2 t1 TMP_3 TMP_8 TMP_19 t2 H)))))))).

theorem pr0_subst1_fwd:
 \forall (u2: T).(\forall (t1: T).(\forall (t2: T).(\forall (i: nat).((subst1 
i u2 t1 t2) \to (\forall (u1: T).((pr0 u2 u1) \to (ex2 T (\lambda (t: 
T).(subst1 i u1 t1 t)) (\lambda (t: T).(pr0 t2 t)))))))))
\def
 \lambda (u2: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda (i: nat).(\lambda 
(H: (subst1 i u2 t1 t2)).(let TMP_3 \def (\lambda (t: T).(\forall (u1: 
T).((pr0 u2 u1) \to (let TMP_1 \def (\lambda (t0: T).(subst1 i u1 t1 t0)) in 
(let TMP_2 \def (\lambda (t0: T).(pr0 t t0)) in (ex2 T TMP_1 TMP_2)))))) in 
(let TMP_8 \def (\lambda (u1: T).(\lambda (_: (pr0 u2 u1)).(let TMP_4 \def 
(\lambda (t: T).(subst1 i u1 t1 t)) in (let TMP_5 \def (\lambda (t: T).(pr0 
t1 t)) in (let TMP_6 \def (subst1_refl i u1 t1) in (let TMP_7 \def (pr0_refl 
t1) in (ex_intro2 T TMP_4 TMP_5 t1 TMP_6 TMP_7))))))) in (let TMP_19 \def 
(\lambda (t0: T).(\lambda (H0: (subst0 i u2 t1 t0)).(\lambda (u1: T).(\lambda 
(H1: (pr0 u2 u1)).(let TMP_9 \def (\lambda (t: T).(subst0 i u1 t1 t)) in (let 
TMP_10 \def (\lambda (t: T).(pr0 t0 t)) in (let TMP_11 \def (\lambda (t: 
T).(subst1 i u1 t1 t)) in (let TMP_12 \def (\lambda (t: T).(pr0 t0 t)) in 
(let TMP_13 \def (ex2 T TMP_11 TMP_12) in (let TMP_17 \def (\lambda (x: 
T).(\lambda (H2: (subst0 i u1 t1 x)).(\lambda (H3: (pr0 t0 x)).(let TMP_14 
\def (\lambda (t: T).(subst1 i u1 t1 t)) in (let TMP_15 \def (\lambda (t: 
T).(pr0 t0 t)) in (let TMP_16 \def (subst1_single i u1 t1 x H2) in (ex_intro2 
T TMP_14 TMP_15 x TMP_16 H3))))))) in (let TMP_18 \def (pr0_subst0_fwd u2 t1 
t0 i H0 u1 H1) in (ex2_ind T TMP_9 TMP_10 TMP_13 TMP_17 TMP_18)))))))))))) in 
(subst1_ind i u2 t1 TMP_3 TMP_8 TMP_19 t2 H)))))))).

theorem pr0_subst1:
 \forall (t1: T).(\forall (t2: T).((pr0 t1 t2) \to (\forall (v1: T).(\forall 
(w1: T).(\forall (i: nat).((subst1 i v1 t1 w1) \to (\forall (v2: T).((pr0 v1 
v2) \to (ex2 T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst1 i v2 t2 
w2)))))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr0 t1 t2)).(\lambda (v1: 
T).(\lambda (w1: T).(\lambda (i: nat).(\lambda (H0: (subst1 i v1 t1 w1)).(let 
TMP_3 \def (\lambda (t: T).(\forall (v2: T).((pr0 v1 v2) \to (let TMP_1 \def 
(\lambda (w2: T).(pr0 t w2)) in (let TMP_2 \def (\lambda (w2: T).(subst1 i v2 
t2 w2)) in (ex2 T TMP_1 TMP_2)))))) in (let TMP_7 \def (\lambda (v2: 
T).(\lambda (_: (pr0 v1 v2)).(let TMP_4 \def (\lambda (w2: T).(pr0 t1 w2)) in 
(let TMP_5 \def (\lambda (w2: T).(subst1 i v2 t2 w2)) in (let TMP_6 \def 
(subst1_refl i v2 t2) in (ex_intro2 T TMP_4 TMP_5 t2 H TMP_6)))))) in (let 
TMP_30 \def (\lambda (t0: T).(\lambda (H1: (subst0 i v1 t1 t0)).(\lambda (v2: 
T).(\lambda (H2: (pr0 v1 v2)).(let TMP_8 \def (pr0 t0 t2) in (let TMP_9 \def 
(\lambda (w2: T).(pr0 t0 w2)) in (let TMP_10 \def (\lambda (w2: T).(subst0 i 
v2 t2 w2)) in (let TMP_11 \def (ex2 T TMP_9 TMP_10) in (let TMP_12 \def 
(\lambda (w2: T).(pr0 t0 w2)) in (let TMP_13 \def (\lambda (w2: T).(subst1 i 
v2 t2 w2)) in (let TMP_14 \def (ex2 T TMP_12 TMP_13) in (let TMP_18 \def 
(\lambda (H3: (pr0 t0 t2)).(let TMP_15 \def (\lambda (w2: T).(pr0 t0 w2)) in 
(let TMP_16 \def (\lambda (w2: T).(subst1 i v2 t2 w2)) in (let TMP_17 \def 
(subst1_refl i v2 t2) in (ex_intro2 T TMP_15 TMP_16 t2 H3 TMP_17))))) in (let 
TMP_28 \def (\lambda (H3: (ex2 T (\lambda (w2: T).(pr0 t0 w2)) (\lambda (w2: 
T).(subst0 i v2 t2 w2)))).(let TMP_19 \def (\lambda (w2: T).(pr0 t0 w2)) in 
(let TMP_20 \def (\lambda (w2: T).(subst0 i v2 t2 w2)) in (let TMP_21 \def 
(\lambda (w2: T).(pr0 t0 w2)) in (let TMP_22 \def (\lambda (w2: T).(subst1 i 
v2 t2 w2)) in (let TMP_23 \def (ex2 T TMP_21 TMP_22) in (let TMP_27 \def 
(\lambda (x: T).(\lambda (H4: (pr0 t0 x)).(\lambda (H5: (subst0 i v2 t2 
x)).(let TMP_24 \def (\lambda (w2: T).(pr0 t0 w2)) in (let TMP_25 \def 
(\lambda (w2: T).(subst1 i v2 t2 w2)) in (let TMP_26 \def (subst1_single i v2 
t2 x H5) in (ex_intro2 T TMP_24 TMP_25 x H4 TMP_26))))))) in (ex2_ind T 
TMP_19 TMP_20 TMP_23 TMP_27 H3)))))))) in (let TMP_29 \def (pr0_subst0 t1 t2 
H v1 t0 i H1 v2 H2) in (or_ind TMP_8 TMP_11 TMP_14 TMP_18 TMP_28 
TMP_29))))))))))))))) in (subst1_ind i v1 t1 TMP_3 TMP_7 TMP_30 w1 
H0)))))))))).

