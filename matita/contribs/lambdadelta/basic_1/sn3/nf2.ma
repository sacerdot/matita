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

include "basic_1/sn3/fwd.ma".

include "basic_1/nf2/dec.ma".

include "basic_1/nf2/pr3.ma".

theorem sn3_nf2:
 \forall (c: C).(\forall (t: T).((nf2 c t) \to (sn3 c t)))
\def
 \lambda (c: C).(\lambda (t: T).(\lambda (H: (nf2 c t)).(let TMP_7 \def 
(\lambda (t2: T).(\lambda (H0: (((eq T t t2) \to (\forall (P: 
Prop).P)))).(\lambda (H1: (pr3 c t t2)).(let H_y \def (nf2_pr3_unfold c t t2 
H1 H) in (let TMP_1 \def (\lambda (t0: T).(pr3 c t t0)) in (let H2 \def 
(eq_ind_r T t2 TMP_1 H1 t H_y) in (let TMP_2 \def (\lambda (t0: T).((eq T t 
t0) \to (\forall (P: Prop).P))) in (let H3 \def (eq_ind_r T t2 TMP_2 H0 t 
H_y) in (let TMP_3 \def (\lambda (t0: T).(sn3 c t0)) in (let TMP_4 \def 
(refl_equal T t) in (let TMP_5 \def (sn3 c t) in (let TMP_6 \def (H3 TMP_4 
TMP_5) in (eq_ind T t TMP_3 TMP_6 t2 H_y))))))))))))) in (sn3_sing c t 
TMP_7)))).

theorem nf2_sn3:
 \forall (c: C).(\forall (t: T).((sn3 c t) \to (ex2 T (\lambda (u: T).(pr3 c 
t u)) (\lambda (u: T).(nf2 c u)))))
\def
 \lambda (c: C).(\lambda (t: T).(\lambda (H: (sn3 c t)).(let TMP_3 \def 
(\lambda (t0: T).(let TMP_1 \def (\lambda (u: T).(pr3 c t0 u)) in (let TMP_2 
\def (\lambda (u: T).(nf2 c u)) in (ex2 T TMP_1 TMP_2)))) in (let TMP_32 \def 
(\lambda (t1: T).(\lambda (_: ((\forall (t2: T).((((eq T t1 t2) \to (\forall 
(P: Prop).P))) \to ((pr3 c t1 t2) \to (sn3 c t2)))))).(\lambda (H1: ((\forall 
(t2: T).((((eq T t1 t2) \to (\forall (P: Prop).P))) \to ((pr3 c t1 t2) \to 
(ex2 T (\lambda (u: T).(pr3 c t2 u)) (\lambda (u: T).(nf2 c u)))))))).(let 
H_x \def (nf2_dec c t1) in (let H2 \def H_x in (let TMP_4 \def (nf2 c t1) in 
(let TMP_5 \def (\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) in 
(let TMP_6 \def (\lambda (t2: T).(pr2 c t1 t2)) in (let TMP_7 \def (ex2 T 
TMP_5 TMP_6) in (let TMP_8 \def (\lambda (u: T).(pr3 c t1 u)) in (let TMP_9 
\def (\lambda (u: T).(nf2 c u)) in (let TMP_10 \def (ex2 T TMP_8 TMP_9) in 
(let TMP_14 \def (\lambda (H3: (nf2 c t1)).(let TMP_11 \def (\lambda (u: 
T).(pr3 c t1 u)) in (let TMP_12 \def (\lambda (u: T).(nf2 c u)) in (let 
TMP_13 \def (pr3_refl c t1) in (ex_intro2 T TMP_11 TMP_12 t1 TMP_13 H3))))) 
in (let TMP_31 \def (\lambda (H3: (ex2 T (\lambda (t2: T).((eq T t1 t2) \to 
(\forall (P: Prop).P))) (\lambda (t2: T).(pr2 c t1 t2)))).(let TMP_15 \def 
(\lambda (t2: T).((eq T t1 t2) \to (\forall (P: Prop).P))) in (let TMP_16 
\def (\lambda (t2: T).(pr2 c t1 t2)) in (let TMP_17 \def (\lambda (u: T).(pr3 
c t1 u)) in (let TMP_18 \def (\lambda (u: T).(nf2 c u)) in (let TMP_19 \def 
(ex2 T TMP_17 TMP_18) in (let TMP_30 \def (\lambda (x: T).(\lambda (H4: (((eq 
T t1 x) \to (\forall (P: Prop).P)))).(\lambda (H5: (pr2 c t1 x)).(let H_y 
\def (H1 x H4) in (let TMP_20 \def (pr3_pr2 c t1 x H5) in (let H6 \def (H_y 
TMP_20) in (let TMP_21 \def (\lambda (u: T).(pr3 c x u)) in (let TMP_22 \def 
(\lambda (u: T).(nf2 c u)) in (let TMP_23 \def (\lambda (u: T).(pr3 c t1 u)) 
in (let TMP_24 \def (\lambda (u: T).(nf2 c u)) in (let TMP_25 \def (ex2 T 
TMP_23 TMP_24) in (let TMP_29 \def (\lambda (x0: T).(\lambda (H7: (pr3 c x 
x0)).(\lambda (H8: (nf2 c x0)).(let TMP_26 \def (\lambda (u: T).(pr3 c t1 u)) 
in (let TMP_27 \def (\lambda (u: T).(nf2 c u)) in (let TMP_28 \def (pr3_sing 
c x t1 H5 x0 H7) in (ex_intro2 T TMP_26 TMP_27 x0 TMP_28 H8))))))) in 
(ex2_ind T TMP_21 TMP_22 TMP_25 TMP_29 H6))))))))))))) in (ex2_ind T TMP_15 
TMP_16 TMP_19 TMP_30 H3)))))))) in (or_ind TMP_4 TMP_7 TMP_10 TMP_14 TMP_31 
H2))))))))))))))) in (sn3_ind c TMP_3 TMP_32 t H))))).

