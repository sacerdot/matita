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

include "Basic-1/pr2/defs.ma".

include "Basic-1/pr0/pr0.ma".

include "Basic-1/getl/props.ma".

theorem pr2_confluence__pr2_free_free:
 \forall (c: C).(\forall (t0: T).(\forall (t1: T).(\forall (t2: T).((pr0 t0 
t1) \to ((pr0 t0 t2) \to (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: 
T).(pr2 c t2 t))))))))
\def
 \lambda (c: C).(\lambda (t0: T).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (pr0 t0 t1)).(\lambda (H0: (pr0 t0 t2)).(ex2_ind T (\lambda (t: T).(pr0 
t2 t)) (\lambda (t: T).(pr0 t1 t)) (ex2 T (\lambda (t: T).(pr2 c t1 t)) 
(\lambda (t: T).(pr2 c t2 t))) (\lambda (x: T).(\lambda (H1: (pr0 t2 
x)).(\lambda (H2: (pr0 t1 x)).(ex_intro2 T (\lambda (t: T).(pr2 c t1 t)) 
(\lambda (t: T).(pr2 c t2 t)) x (pr2_free c t1 x H2) (pr2_free c t2 x H1))))) 
(pr0_confluence t0 t2 H0 t1 H))))))).
(* COMMENTS
Initial nodes: 135
END *)

theorem pr2_confluence__pr2_free_delta:
 \forall (c: C).(\forall (d: C).(\forall (t0: T).(\forall (t1: T).(\forall 
(t2: T).(\forall (t4: T).(\forall (u: T).(\forall (i: nat).((pr0 t0 t1) \to 
((getl i c (CHead d (Bind Abbr) u)) \to ((pr0 t0 t4) \to ((subst0 i u t4 t2) 
\to (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 
t))))))))))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (t0: T).(\lambda (t1: T).(\lambda 
(t2: T).(\lambda (t4: T).(\lambda (u: T).(\lambda (i: nat).(\lambda (H: (pr0 
t0 t1)).(\lambda (H0: (getl i c (CHead d (Bind Abbr) u))).(\lambda (H1: (pr0 
t0 t4)).(\lambda (H2: (subst0 i u t4 t2)).(ex2_ind T (\lambda (t: T).(pr0 t4 
t)) (\lambda (t: T).(pr0 t1 t)) (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda 
(t: T).(pr2 c t2 t))) (\lambda (x: T).(\lambda (H3: (pr0 t4 x)).(\lambda (H4: 
(pr0 t1 x)).(or_ind (pr0 t2 x) (ex2 T (\lambda (w2: T).(pr0 t2 w2)) (\lambda 
(w2: T).(subst0 i u x w2))) (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: 
T).(pr2 c t2 t))) (\lambda (H5: (pr0 t2 x)).(ex_intro2 T (\lambda (t: T).(pr2 
c t1 t)) (\lambda (t: T).(pr2 c t2 t)) x (pr2_free c t1 x H4) (pr2_free c t2 
x H5))) (\lambda (H5: (ex2 T (\lambda (w2: T).(pr0 t2 w2)) (\lambda (w2: 
T).(subst0 i u x w2)))).(ex2_ind T (\lambda (w2: T).(pr0 t2 w2)) (\lambda 
(w2: T).(subst0 i u x w2)) (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: 
T).(pr2 c t2 t))) (\lambda (x0: T).(\lambda (H6: (pr0 t2 x0)).(\lambda (H7: 
(subst0 i u x x0)).(ex_intro2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: 
T).(pr2 c t2 t)) x0 (pr2_delta c d u i H0 t1 x H4 x0 H7) (pr2_free c t2 x0 
H6))))) H5)) (pr0_subst0 t4 x H3 u t2 i H2 u (pr0_refl u)))))) 
(pr0_confluence t0 t4 H1 t1 H))))))))))))).
(* COMMENTS
Initial nodes: 403
END *)

theorem pr2_confluence__pr2_delta_delta:
 \forall (c: C).(\forall (d: C).(\forall (d0: C).(\forall (t0: T).(\forall 
(t1: T).(\forall (t2: T).(\forall (t3: T).(\forall (t4: T).(\forall (u: 
T).(\forall (u0: T).(\forall (i: nat).(\forall (i0: nat).((getl i c (CHead d 
(Bind Abbr) u)) \to ((pr0 t0 t3) \to ((subst0 i u t3 t1) \to ((getl i0 c 
(CHead d0 (Bind Abbr) u0)) \to ((pr0 t0 t4) \to ((subst0 i0 u0 t4 t2) \to 
(ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 
t))))))))))))))))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (d0: C).(\lambda (t0: T).(\lambda 
(t1: T).(\lambda (t2: T).(\lambda (t3: T).(\lambda (t4: T).(\lambda (u: 
T).(\lambda (u0: T).(\lambda (i: nat).(\lambda (i0: nat).(\lambda (H: (getl i 
c (CHead d (Bind Abbr) u))).(\lambda (H0: (pr0 t0 t3)).(\lambda (H1: (subst0 
i u t3 t1)).(\lambda (H2: (getl i0 c (CHead d0 (Bind Abbr) u0))).(\lambda 
(H3: (pr0 t0 t4)).(\lambda (H4: (subst0 i0 u0 t4 t2)).(ex2_ind T (\lambda (t: 
T).(pr0 t4 t)) (\lambda (t: T).(pr0 t3 t)) (ex2 T (\lambda (t: T).(pr2 c t1 
t)) (\lambda (t: T).(pr2 c t2 t))) (\lambda (x: T).(\lambda (H5: (pr0 t4 
x)).(\lambda (H6: (pr0 t3 x)).(or_ind (pr0 t1 x) (ex2 T (\lambda (w2: T).(pr0 
t1 w2)) (\lambda (w2: T).(subst0 i u x w2))) (ex2 T (\lambda (t: T).(pr2 c t1 
t)) (\lambda (t: T).(pr2 c t2 t))) (\lambda (H7: (pr0 t1 x)).(or_ind (pr0 t2 
x) (ex2 T (\lambda (w2: T).(pr0 t2 w2)) (\lambda (w2: T).(subst0 i0 u0 x 
w2))) (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 t))) 
(\lambda (H8: (pr0 t2 x)).(ex_intro2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda 
(t: T).(pr2 c t2 t)) x (pr2_free c t1 x H7) (pr2_free c t2 x H8))) (\lambda 
(H8: (ex2 T (\lambda (w2: T).(pr0 t2 w2)) (\lambda (w2: T).(subst0 i0 u0 x 
w2)))).(ex2_ind T (\lambda (w2: T).(pr0 t2 w2)) (\lambda (w2: T).(subst0 i0 
u0 x w2)) (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 t))) 
(\lambda (x0: T).(\lambda (H9: (pr0 t2 x0)).(\lambda (H10: (subst0 i0 u0 x 
x0)).(ex_intro2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 t)) 
x0 (pr2_delta c d0 u0 i0 H2 t1 x H7 x0 H10) (pr2_free c t2 x0 H9))))) H8)) 
(pr0_subst0 t4 x H5 u0 t2 i0 H4 u0 (pr0_refl u0)))) (\lambda (H7: (ex2 T 
(\lambda (w2: T).(pr0 t1 w2)) (\lambda (w2: T).(subst0 i u x w2)))).(ex2_ind 
T (\lambda (w2: T).(pr0 t1 w2)) (\lambda (w2: T).(subst0 i u x w2)) (ex2 T 
(\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 t))) (\lambda (x0: 
T).(\lambda (H8: (pr0 t1 x0)).(\lambda (H9: (subst0 i u x x0)).(or_ind (pr0 
t2 x) (ex2 T (\lambda (w2: T).(pr0 t2 w2)) (\lambda (w2: T).(subst0 i0 u0 x 
w2))) (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 t))) 
(\lambda (H10: (pr0 t2 x)).(ex_intro2 T (\lambda (t: T).(pr2 c t1 t)) 
(\lambda (t: T).(pr2 c t2 t)) x0 (pr2_free c t1 x0 H8) (pr2_delta c d u i H 
t2 x H10 x0 H9))) (\lambda (H10: (ex2 T (\lambda (w2: T).(pr0 t2 w2)) 
(\lambda (w2: T).(subst0 i0 u0 x w2)))).(ex2_ind T (\lambda (w2: T).(pr0 t2 
w2)) (\lambda (w2: T).(subst0 i0 u0 x w2)) (ex2 T (\lambda (t: T).(pr2 c t1 
t)) (\lambda (t: T).(pr2 c t2 t))) (\lambda (x1: T).(\lambda (H11: (pr0 t2 
x1)).(\lambda (H12: (subst0 i0 u0 x x1)).(neq_eq_e i i0 (ex2 T (\lambda (t: 
T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 t))) (\lambda (H13: (not (eq nat i 
i0))).(ex2_ind T (\lambda (t: T).(subst0 i u x1 t)) (\lambda (t: T).(subst0 
i0 u0 x0 t)) (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 
t))) (\lambda (x2: T).(\lambda (H14: (subst0 i u x1 x2)).(\lambda (H15: 
(subst0 i0 u0 x0 x2)).(ex_intro2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: 
T).(pr2 c t2 t)) x2 (pr2_delta c d0 u0 i0 H2 t1 x0 H8 x2 H15) (pr2_delta c d 
u i H t2 x1 H11 x2 H14))))) (subst0_confluence_neq x x1 u0 i0 H12 x0 u i H9 
(sym_not_eq nat i i0 H13)))) (\lambda (H13: (eq nat i i0)).(let H14 \def 
(eq_ind_r nat i0 (\lambda (n: nat).(subst0 n u0 x x1)) H12 i H13) in (let H15 
\def (eq_ind_r nat i0 (\lambda (n: nat).(getl n c (CHead d0 (Bind Abbr) u0))) 
H2 i H13) in (let H16 \def (eq_ind C (CHead d (Bind Abbr) u) (\lambda (c0: 
C).(getl i c c0)) H (CHead d0 (Bind Abbr) u0) (getl_mono c (CHead d (Bind 
Abbr) u) i H (CHead d0 (Bind Abbr) u0) H15)) in (let H17 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow d | (CHead c0 _ _) \Rightarrow c0])) (CHead d (Bind Abbr) u) 
(CHead d0 (Bind Abbr) u0) (getl_mono c (CHead d (Bind Abbr) u) i H (CHead d0 
(Bind Abbr) u0) H15)) in ((let H18 \def (f_equal C T (\lambda (e: C).(match e 
in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t) 
\Rightarrow t])) (CHead d (Bind Abbr) u) (CHead d0 (Bind Abbr) u0) (getl_mono 
c (CHead d (Bind Abbr) u) i H (CHead d0 (Bind Abbr) u0) H15)) in (\lambda 
(H19: (eq C d d0)).(let H20 \def (eq_ind_r T u0 (\lambda (t: T).(subst0 i t x 
x1)) H14 u H18) in (let H21 \def (eq_ind_r T u0 (\lambda (t: T).(getl i c 
(CHead d0 (Bind Abbr) t))) H16 u H18) in (let H22 \def (eq_ind_r C d0 
(\lambda (c0: C).(getl i c (CHead c0 (Bind Abbr) u))) H21 d H19) in (or4_ind 
(eq T x1 x0) (ex2 T (\lambda (t: T).(subst0 i u x1 t)) (\lambda (t: 
T).(subst0 i u x0 t))) (subst0 i u x1 x0) (subst0 i u x0 x1) (ex2 T (\lambda 
(t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 t))) (\lambda (H23: (eq T x1 
x0)).(let H24 \def (eq_ind T x1 (\lambda (t: T).(pr0 t2 t)) H11 x0 H23) in 
(ex_intro2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 t)) x0 
(pr2_free c t1 x0 H8) (pr2_free c t2 x0 H24)))) (\lambda (H23: (ex2 T 
(\lambda (t: T).(subst0 i u x1 t)) (\lambda (t: T).(subst0 i u x0 
t)))).(ex2_ind T (\lambda (t: T).(subst0 i u x1 t)) (\lambda (t: T).(subst0 i 
u x0 t)) (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 t))) 
(\lambda (x2: T).(\lambda (H24: (subst0 i u x1 x2)).(\lambda (H25: (subst0 i 
u x0 x2)).(ex_intro2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c 
t2 t)) x2 (pr2_delta c d u i H22 t1 x0 H8 x2 H25) (pr2_delta c d u i H22 t2 
x1 H11 x2 H24))))) H23)) (\lambda (H23: (subst0 i u x1 x0)).(ex_intro2 T 
(\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 t)) x0 (pr2_free c t1 
x0 H8) (pr2_delta c d u i H22 t2 x1 H11 x0 H23))) (\lambda (H23: (subst0 i u 
x0 x1)).(ex_intro2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 
t)) x1 (pr2_delta c d u i H22 t1 x0 H8 x1 H23) (pr2_free c t2 x1 H11))) 
(subst0_confluence_eq x x1 u i H20 x0 H9))))))) H17)))))))))) H10)) 
(pr0_subst0 t4 x H5 u0 t2 i0 H4 u0 (pr0_refl u0)))))) H7)) (pr0_subst0 t3 x 
H6 u t1 i H1 u (pr0_refl u)))))) (pr0_confluence t0 t4 H3 t3 
H0))))))))))))))))))).
(* COMMENTS
Initial nodes: 1901
END *)

theorem pr2_confluence:
 \forall (c: C).(\forall (t0: T).(\forall (t1: T).((pr2 c t0 t1) \to (\forall 
(t2: T).((pr2 c t0 t2) \to (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: 
T).(pr2 c t2 t))))))))
\def
 \lambda (c: C).(\lambda (t0: T).(\lambda (t1: T).(\lambda (H: (pr2 c t0 
t1)).(\lambda (t2: T).(\lambda (H0: (pr2 c t0 t2)).(let H1 \def (match H in 
pr2 return (\lambda (c0: C).(\lambda (t: T).(\lambda (t3: T).(\lambda (_: 
(pr2 c0 t t3)).((eq C c0 c) \to ((eq T t t0) \to ((eq T t3 t1) \to (ex2 T 
(\lambda (t4: T).(pr2 c t1 t4)) (\lambda (t4: T).(pr2 c t2 t4)))))))))) with 
[(pr2_free c0 t3 t4 H1) \Rightarrow (\lambda (H2: (eq C c0 c)).(\lambda (H3: 
(eq T t3 t0)).(\lambda (H4: (eq T t4 t1)).(eq_ind C c (\lambda (_: C).((eq T 
t3 t0) \to ((eq T t4 t1) \to ((pr0 t3 t4) \to (ex2 T (\lambda (t: T).(pr2 c 
t1 t)) (\lambda (t: T).(pr2 c t2 t))))))) (\lambda (H5: (eq T t3 t0)).(eq_ind 
T t0 (\lambda (t: T).((eq T t4 t1) \to ((pr0 t t4) \to (ex2 T (\lambda (t5: 
T).(pr2 c t1 t5)) (\lambda (t5: T).(pr2 c t2 t5)))))) (\lambda (H6: (eq T t4 
t1)).(eq_ind T t1 (\lambda (t: T).((pr0 t0 t) \to (ex2 T (\lambda (t5: 
T).(pr2 c t1 t5)) (\lambda (t5: T).(pr2 c t2 t5))))) (\lambda (H7: (pr0 t0 
t1)).(let H8 \def (match H0 in pr2 return (\lambda (c1: C).(\lambda (t: 
T).(\lambda (t5: T).(\lambda (_: (pr2 c1 t t5)).((eq C c1 c) \to ((eq T t t0) 
\to ((eq T t5 t2) \to (ex2 T (\lambda (t6: T).(pr2 c t1 t6)) (\lambda (t6: 
T).(pr2 c t2 t6)))))))))) with [(pr2_free c1 t5 t6 H8) \Rightarrow (\lambda 
(H9: (eq C c1 c)).(\lambda (H10: (eq T t5 t0)).(\lambda (H11: (eq T t6 
t2)).(eq_ind C c (\lambda (_: C).((eq T t5 t0) \to ((eq T t6 t2) \to ((pr0 t5 
t6) \to (ex2 T (\lambda (t: T).(pr2 c t1 t)) (\lambda (t: T).(pr2 c t2 
t))))))) (\lambda (H12: (eq T t5 t0)).(eq_ind T t0 (\lambda (t: T).((eq T t6 
t2) \to ((pr0 t t6) \to (ex2 T (\lambda (t7: T).(pr2 c t1 t7)) (\lambda (t7: 
T).(pr2 c t2 t7)))))) (\lambda (H13: (eq T t6 t2)).(eq_ind T t2 (\lambda (t: 
T).((pr0 t0 t) \to (ex2 T (\lambda (t7: T).(pr2 c t1 t7)) (\lambda (t7: 
T).(pr2 c t2 t7))))) (\lambda (H14: (pr0 t0 
t2)).(pr2_confluence__pr2_free_free c t0 t1 t2 H7 H14)) t6 (sym_eq T t6 t2 
H13))) t5 (sym_eq T t5 t0 H12))) c1 (sym_eq C c1 c H9) H10 H11 H8)))) | 
(pr2_delta c1 d u i H8 t5 t6 H9 t H10) \Rightarrow (\lambda (H11: (eq C c1 
c)).(\lambda (H12: (eq T t5 t0)).(\lambda (H13: (eq T t t2)).(eq_ind C c 
(\lambda (c2: C).((eq T t5 t0) \to ((eq T t t2) \to ((getl i c2 (CHead d 
(Bind Abbr) u)) \to ((pr0 t5 t6) \to ((subst0 i u t6 t) \to (ex2 T (\lambda 
(t7: T).(pr2 c t1 t7)) (\lambda (t7: T).(pr2 c t2 t7))))))))) (\lambda (H14: 
(eq T t5 t0)).(eq_ind T t0 (\lambda (t7: T).((eq T t t2) \to ((getl i c 
(CHead d (Bind Abbr) u)) \to ((pr0 t7 t6) \to ((subst0 i u t6 t) \to (ex2 T 
(\lambda (t8: T).(pr2 c t1 t8)) (\lambda (t8: T).(pr2 c t2 t8)))))))) 
(\lambda (H15: (eq T t t2)).(eq_ind T t2 (\lambda (t7: T).((getl i c (CHead d 
(Bind Abbr) u)) \to ((pr0 t0 t6) \to ((subst0 i u t6 t7) \to (ex2 T (\lambda 
(t8: T).(pr2 c t1 t8)) (\lambda (t8: T).(pr2 c t2 t8))))))) (\lambda (H16: 
(getl i c (CHead d (Bind Abbr) u))).(\lambda (H17: (pr0 t0 t6)).(\lambda 
(H18: (subst0 i u t6 t2)).(pr2_confluence__pr2_free_delta c d t0 t1 t2 t6 u i 
H7 H16 H17 H18)))) t (sym_eq T t t2 H15))) t5 (sym_eq T t5 t0 H14))) c1 
(sym_eq C c1 c H11) H12 H13 H8 H9 H10))))]) in (H8 (refl_equal C c) 
(refl_equal T t0) (refl_equal T t2)))) t4 (sym_eq T t4 t1 H6))) t3 (sym_eq T 
t3 t0 H5))) c0 (sym_eq C c0 c H2) H3 H4 H1)))) | (pr2_delta c0 d u i H1 t3 t4 
H2 t H3) \Rightarrow (\lambda (H4: (eq C c0 c)).(\lambda (H5: (eq T t3 
t0)).(\lambda (H6: (eq T t t1)).(eq_ind C c (\lambda (c1: C).((eq T t3 t0) 
\to ((eq T t t1) \to ((getl i c1 (CHead d (Bind Abbr) u)) \to ((pr0 t3 t4) 
\to ((subst0 i u t4 t) \to (ex2 T (\lambda (t5: T).(pr2 c t1 t5)) (\lambda 
(t5: T).(pr2 c t2 t5))))))))) (\lambda (H7: (eq T t3 t0)).(eq_ind T t0 
(\lambda (t5: T).((eq T t t1) \to ((getl i c (CHead d (Bind Abbr) u)) \to 
((pr0 t5 t4) \to ((subst0 i u t4 t) \to (ex2 T (\lambda (t6: T).(pr2 c t1 
t6)) (\lambda (t6: T).(pr2 c t2 t6)))))))) (\lambda (H8: (eq T t t1)).(eq_ind 
T t1 (\lambda (t5: T).((getl i c (CHead d (Bind Abbr) u)) \to ((pr0 t0 t4) 
\to ((subst0 i u t4 t5) \to (ex2 T (\lambda (t6: T).(pr2 c t1 t6)) (\lambda 
(t6: T).(pr2 c t2 t6))))))) (\lambda (H9: (getl i c (CHead d (Bind Abbr) 
u))).(\lambda (H10: (pr0 t0 t4)).(\lambda (H11: (subst0 i u t4 t1)).(let H12 
\def (match H0 in pr2 return (\lambda (c1: C).(\lambda (t5: T).(\lambda (t6: 
T).(\lambda (_: (pr2 c1 t5 t6)).((eq C c1 c) \to ((eq T t5 t0) \to ((eq T t6 
t2) \to (ex2 T (\lambda (t7: T).(pr2 c t1 t7)) (\lambda (t7: T).(pr2 c t2 
t7)))))))))) with [(pr2_free c1 t5 t6 H12) \Rightarrow (\lambda (H13: (eq C 
c1 c)).(\lambda (H14: (eq T t5 t0)).(\lambda (H15: (eq T t6 t2)).(eq_ind C c 
(\lambda (_: C).((eq T t5 t0) \to ((eq T t6 t2) \to ((pr0 t5 t6) \to (ex2 T 
(\lambda (t7: T).(pr2 c t1 t7)) (\lambda (t7: T).(pr2 c t2 t7))))))) (\lambda 
(H16: (eq T t5 t0)).(eq_ind T t0 (\lambda (t7: T).((eq T t6 t2) \to ((pr0 t7 
t6) \to (ex2 T (\lambda (t8: T).(pr2 c t1 t8)) (\lambda (t8: T).(pr2 c t2 
t8)))))) (\lambda (H17: (eq T t6 t2)).(eq_ind T t2 (\lambda (t7: T).((pr0 t0 
t7) \to (ex2 T (\lambda (t8: T).(pr2 c t1 t8)) (\lambda (t8: T).(pr2 c t2 
t8))))) (\lambda (H18: (pr0 t0 t2)).(ex2_sym T (pr2 c t2) (pr2 c t1) 
(pr2_confluence__pr2_free_delta c d t0 t2 t1 t4 u i H18 H9 H10 H11))) t6 
(sym_eq T t6 t2 H17))) t5 (sym_eq T t5 t0 H16))) c1 (sym_eq C c1 c H13) H14 
H15 H12)))) | (pr2_delta c1 d0 u0 i0 H12 t5 t6 H13 t7 H14) \Rightarrow 
(\lambda (H15: (eq C c1 c)).(\lambda (H16: (eq T t5 t0)).(\lambda (H17: (eq T 
t7 t2)).(eq_ind C c (\lambda (c2: C).((eq T t5 t0) \to ((eq T t7 t2) \to 
((getl i0 c2 (CHead d0 (Bind Abbr) u0)) \to ((pr0 t5 t6) \to ((subst0 i0 u0 
t6 t7) \to (ex2 T (\lambda (t8: T).(pr2 c t1 t8)) (\lambda (t8: T).(pr2 c t2 
t8))))))))) (\lambda (H18: (eq T t5 t0)).(eq_ind T t0 (\lambda (t8: T).((eq T 
t7 t2) \to ((getl i0 c (CHead d0 (Bind Abbr) u0)) \to ((pr0 t8 t6) \to 
((subst0 i0 u0 t6 t7) \to (ex2 T (\lambda (t9: T).(pr2 c t1 t9)) (\lambda 
(t9: T).(pr2 c t2 t9)))))))) (\lambda (H19: (eq T t7 t2)).(eq_ind T t2 
(\lambda (t8: T).((getl i0 c (CHead d0 (Bind Abbr) u0)) \to ((pr0 t0 t6) \to 
((subst0 i0 u0 t6 t8) \to (ex2 T (\lambda (t9: T).(pr2 c t1 t9)) (\lambda 
(t9: T).(pr2 c t2 t9))))))) (\lambda (H20: (getl i0 c (CHead d0 (Bind Abbr) 
u0))).(\lambda (H21: (pr0 t0 t6)).(\lambda (H22: (subst0 i0 u0 t6 
t2)).(pr2_confluence__pr2_delta_delta c d d0 t0 t1 t2 t4 t6 u u0 i i0 H9 H10 
H11 H20 H21 H22)))) t7 (sym_eq T t7 t2 H19))) t5 (sym_eq T t5 t0 H18))) c1 
(sym_eq C c1 c H15) H16 H17 H12 H13 H14))))]) in (H12 (refl_equal C c) 
(refl_equal T t0) (refl_equal T t2)))))) t (sym_eq T t t1 H8))) t3 (sym_eq T 
t3 t0 H7))) c0 (sym_eq C c0 c H4) H5 H6 H1 H2 H3))))]) in (H1 (refl_equal C 
c) (refl_equal T t0) (refl_equal T t1)))))))).
(* COMMENTS
Initial nodes: 2087
END *)

