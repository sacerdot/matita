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

include "basic_1/pr1/props.ma".

include "basic_1/pr0/pr0.ma".

theorem pr1_strip:
 \forall (t0: T).(\forall (t1: T).((pr1 t0 t1) \to (\forall (t2: T).((pr0 t0 
t2) \to (ex2 T (\lambda (t: T).(pr1 t1 t)) (\lambda (t: T).(pr1 t2 t)))))))
\def
 \lambda (t0: T).(\lambda (t1: T).(\lambda (H: (pr1 t0 t1)).(let TMP_3 \def 
(\lambda (t: T).(\lambda (t2: T).(\forall (t3: T).((pr0 t t3) \to (let TMP_1 
\def (\lambda (t4: T).(pr1 t2 t4)) in (let TMP_2 \def (\lambda (t4: T).(pr1 
t3 t4)) in (ex2 T TMP_1 TMP_2))))))) in (let TMP_8 \def (\lambda (t: 
T).(\lambda (t2: T).(\lambda (H0: (pr0 t t2)).(let TMP_4 \def (\lambda (t3: 
T).(pr1 t t3)) in (let TMP_5 \def (\lambda (t3: T).(pr1 t2 t3)) in (let TMP_6 
\def (pr1_pr0 t t2 H0) in (let TMP_7 \def (pr1_refl t2) in (ex_intro2 T TMP_4 
TMP_5 t2 TMP_6 TMP_7)))))))) in (let TMP_26 \def (\lambda (t2: T).(\lambda 
(t3: T).(\lambda (H0: (pr0 t3 t2)).(\lambda (t4: T).(\lambda (_: (pr1 t2 
t4)).(\lambda (H2: ((\forall (t5: T).((pr0 t2 t5) \to (ex2 T (\lambda (t: 
T).(pr1 t4 t)) (\lambda (t: T).(pr1 t5 t))))))).(\lambda (t5: T).(\lambda 
(H3: (pr0 t3 t5)).(let TMP_9 \def (\lambda (t: T).(pr0 t5 t)) in (let TMP_10 
\def (\lambda (t: T).(pr0 t2 t)) in (let TMP_11 \def (\lambda (t: T).(pr1 t4 
t)) in (let TMP_12 \def (\lambda (t: T).(pr1 t5 t)) in (let TMP_13 \def (ex2 
T TMP_11 TMP_12) in (let TMP_24 \def (\lambda (x: T).(\lambda (H4: (pr0 t5 
x)).(\lambda (H5: (pr0 t2 x)).(let H6 \def (H2 x H5) in (let TMP_14 \def 
(\lambda (t: T).(pr1 t4 t)) in (let TMP_15 \def (\lambda (t: T).(pr1 x t)) in 
(let TMP_16 \def (\lambda (t: T).(pr1 t4 t)) in (let TMP_17 \def (\lambda (t: 
T).(pr1 t5 t)) in (let TMP_18 \def (ex2 T TMP_16 TMP_17) in (let TMP_23 \def 
(\lambda (x0: T).(\lambda (H7: (pr1 t4 x0)).(\lambda (H8: (pr1 x x0)).(let 
TMP_19 \def (\lambda (t: T).(pr1 t4 t)) in (let TMP_20 \def (\lambda (t: 
T).(pr1 t5 t)) in (let TMP_21 \def (pr1_pr0 t5 x H4) in (let TMP_22 \def 
(pr1_t x t5 TMP_21 x0 H8) in (ex_intro2 T TMP_19 TMP_20 x0 H7 TMP_22)))))))) 
in (ex2_ind T TMP_14 TMP_15 TMP_18 TMP_23 H6))))))))))) in (let TMP_25 \def 
(pr0_confluence t3 t5 H3 t2 H0) in (ex2_ind T TMP_9 TMP_10 TMP_13 TMP_24 
TMP_25)))))))))))))))) in (pr1_ind TMP_3 TMP_8 TMP_26 t0 t1 H)))))).

theorem pr1_confluence:
 \forall (t0: T).(\forall (t1: T).((pr1 t0 t1) \to (\forall (t2: T).((pr1 t0 
t2) \to (ex2 T (\lambda (t: T).(pr1 t1 t)) (\lambda (t: T).(pr1 t2 t)))))))
\def
 \lambda (t0: T).(\lambda (t1: T).(\lambda (H: (pr1 t0 t1)).(let TMP_3 \def 
(\lambda (t: T).(\lambda (t2: T).(\forall (t3: T).((pr1 t t3) \to (let TMP_1 
\def (\lambda (t4: T).(pr1 t2 t4)) in (let TMP_2 \def (\lambda (t4: T).(pr1 
t3 t4)) in (ex2 T TMP_1 TMP_2))))))) in (let TMP_7 \def (\lambda (t: 
T).(\lambda (t2: T).(\lambda (H0: (pr1 t t2)).(let TMP_4 \def (\lambda (t3: 
T).(pr1 t t3)) in (let TMP_5 \def (\lambda (t3: T).(pr1 t2 t3)) in (let TMP_6 
\def (pr1_refl t2) in (ex_intro2 T TMP_4 TMP_5 t2 H0 TMP_6))))))) in (let 
TMP_23 \def (\lambda (t2: T).(\lambda (t3: T).(\lambda (H0: (pr0 t3 
t2)).(\lambda (t4: T).(\lambda (_: (pr1 t2 t4)).(\lambda (H2: ((\forall (t5: 
T).((pr1 t2 t5) \to (ex2 T (\lambda (t: T).(pr1 t4 t)) (\lambda (t: T).(pr1 
t5 t))))))).(\lambda (t5: T).(\lambda (H3: (pr1 t3 t5)).(let H_x \def 
(pr1_strip t3 t5 H3 t2 H0) in (let H4 \def H_x in (let TMP_8 \def (\lambda 
(t: T).(pr1 t5 t)) in (let TMP_9 \def (\lambda (t: T).(pr1 t2 t)) in (let 
TMP_10 \def (\lambda (t: T).(pr1 t4 t)) in (let TMP_11 \def (\lambda (t: 
T).(pr1 t5 t)) in (let TMP_12 \def (ex2 T TMP_10 TMP_11) in (let TMP_22 \def 
(\lambda (x: T).(\lambda (H5: (pr1 t5 x)).(\lambda (H6: (pr1 t2 x)).(let H_x0 
\def (H2 x H6) in (let H7 \def H_x0 in (let TMP_13 \def (\lambda (t: T).(pr1 
t4 t)) in (let TMP_14 \def (\lambda (t: T).(pr1 x t)) in (let TMP_15 \def 
(\lambda (t: T).(pr1 t4 t)) in (let TMP_16 \def (\lambda (t: T).(pr1 t5 t)) 
in (let TMP_17 \def (ex2 T TMP_15 TMP_16) in (let TMP_21 \def (\lambda (x0: 
T).(\lambda (H8: (pr1 t4 x0)).(\lambda (H9: (pr1 x x0)).(let TMP_18 \def 
(\lambda (t: T).(pr1 t4 t)) in (let TMP_19 \def (\lambda (t: T).(pr1 t5 t)) 
in (let TMP_20 \def (pr1_t x t5 H5 x0 H9) in (ex_intro2 T TMP_18 TMP_19 x0 H8 
TMP_20))))))) in (ex2_ind T TMP_13 TMP_14 TMP_17 TMP_21 H7)))))))))))) in 
(ex2_ind T TMP_8 TMP_9 TMP_12 TMP_22 H4))))))))))))))))) in (pr1_ind TMP_3 
TMP_7 TMP_23 t0 t1 H)))))).

