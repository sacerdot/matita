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

include "Basic-1/pc3/left.ma".

include "Basic-1/fsubst0/defs.ma".

include "Basic-1/csubst0/getl.ma".

theorem pc3_pr2_fsubst0:
 \forall (c1: C).(\forall (t1: T).(\forall (t: T).((pr2 c1 t1 t) \to (\forall 
(i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t2: T).((fsubst0 i u c1 
t1 c2 t2) \to (\forall (e: C).((getl i c1 (CHead e (Bind Abbr) u)) \to (pc3 
c2 t2 t)))))))))))
\def
 \lambda (c1: C).(\lambda (t1: T).(\lambda (t: T).(\lambda (H: (pr2 c1 t1 
t)).(pr2_ind (\lambda (c: C).(\lambda (t0: T).(\lambda (t2: T).(\forall (i: 
nat).(\forall (u: T).(\forall (c2: C).(\forall (t3: T).((fsubst0 i u c t0 c2 
t3) \to (\forall (e: C).((getl i c (CHead e (Bind Abbr) u)) \to (pc3 c2 t3 
t2))))))))))) (\lambda (c: C).(\lambda (t2: T).(\lambda (t3: T).(\lambda (H0: 
(pr0 t2 t3)).(\lambda (i: nat).(\lambda (u: T).(\lambda (c2: C).(\lambda (t0: 
T).(\lambda (H1: (fsubst0 i u c t2 c2 t0)).(fsubst0_ind i u c t2 (\lambda 
(c0: C).(\lambda (t4: T).(\forall (e: C).((getl i c (CHead e (Bind Abbr) u)) 
\to (pc3 c0 t4 t3))))) (\lambda (t4: T).(\lambda (H2: (subst0 i u t2 
t4)).(\lambda (e: C).(\lambda (H3: (getl i c (CHead e (Bind Abbr) 
u))).(or_ind (pr0 t4 t3) (ex2 T (\lambda (w2: T).(pr0 t4 w2)) (\lambda (w2: 
T).(subst0 i u t3 w2))) (pc3 c t4 t3) (\lambda (H4: (pr0 t4 t3)).(pc3_pr2_r c 
t4 t3 (pr2_free c t4 t3 H4))) (\lambda (H4: (ex2 T (\lambda (w2: T).(pr0 t4 
w2)) (\lambda (w2: T).(subst0 i u t3 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 
t4 w2)) (\lambda (w2: T).(subst0 i u t3 w2)) (pc3 c t4 t3) (\lambda (x: 
T).(\lambda (H5: (pr0 t4 x)).(\lambda (H6: (subst0 i u t3 x)).(pc3_pr2_u c x 
t4 (pr2_free c t4 x H5) t3 (pc3_pr2_x c x t3 (pr2_delta c e u i H3 t3 t3 
(pr0_refl t3) x H6)))))) H4)) (pr0_subst0 t2 t3 H0 u t4 i H2 u (pr0_refl 
u))))))) (\lambda (c0: C).(\lambda (_: (csubst0 i u c c0)).(\lambda (e: 
C).(\lambda (_: (getl i c (CHead e (Bind Abbr) u))).(pc3_pr2_r c0 t2 t3 
(pr2_free c0 t2 t3 H0)))))) (\lambda (t4: T).(\lambda (H2: (subst0 i u t2 
t4)).(\lambda (c0: C).(\lambda (H3: (csubst0 i u c c0)).(\lambda (e: 
C).(\lambda (H4: (getl i c (CHead e (Bind Abbr) u))).(or_ind (pr0 t4 t3) (ex2 
T (\lambda (w2: T).(pr0 t4 w2)) (\lambda (w2: T).(subst0 i u t3 w2))) (pc3 c0 
t4 t3) (\lambda (H5: (pr0 t4 t3)).(pc3_pr2_r c0 t4 t3 (pr2_free c0 t4 t3 
H5))) (\lambda (H5: (ex2 T (\lambda (w2: T).(pr0 t4 w2)) (\lambda (w2: 
T).(subst0 i u t3 w2)))).(ex2_ind T (\lambda (w2: T).(pr0 t4 w2)) (\lambda 
(w2: T).(subst0 i u t3 w2)) (pc3 c0 t4 t3) (\lambda (x: T).(\lambda (H6: (pr0 
t4 x)).(\lambda (H7: (subst0 i u t3 x)).(pc3_pr2_u c0 x t4 (pr2_free c0 t4 x 
H6) t3 (pc3_pr2_x c0 x t3 (pr2_delta c0 e u i (csubst0_getl_ge i i (le_n i) c 
c0 u H3 (CHead e (Bind Abbr) u) H4) t3 t3 (pr0_refl t3) x H7)))))) H5)) 
(pr0_subst0 t2 t3 H0 u t4 i H2 u (pr0_refl u))))))))) c2 t0 H1)))))))))) 
(\lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H0: (getl i c (CHead d (Bind Abbr) u))).(\lambda (t2: T).(\lambda (t3: 
T).(\lambda (H1: (pr0 t2 t3)).(\lambda (t0: T).(\lambda (H2: (subst0 i u t3 
t0)).(\lambda (i0: nat).(\lambda (u0: T).(\lambda (c2: C).(\lambda (t4: 
T).(\lambda (H3: (fsubst0 i0 u0 c t2 c2 t4)).(fsubst0_ind i0 u0 c t2 (\lambda 
(c0: C).(\lambda (t5: T).(\forall (e: C).((getl i0 c (CHead e (Bind Abbr) 
u0)) \to (pc3 c0 t5 t0))))) (\lambda (t5: T).(\lambda (H4: (subst0 i0 u0 t2 
t5)).(\lambda (e: C).(\lambda (H5: (getl i0 c (CHead e (Bind Abbr) 
u0))).(pc3_t t2 c t5 (pc3_s c t5 t2 (pc3_pr2_r c t2 t5 (pr2_delta c e u0 i0 
H5 t2 t2 (pr0_refl t2) t5 H4))) t0 (pc3_pr2_r c t2 t0 (pr2_delta c d u i H0 
t2 t3 H1 t0 H2))))))) (\lambda (c0: C).(\lambda (H4: (csubst0 i0 u0 c 
c0)).(\lambda (e: C).(\lambda (H5: (getl i0 c (CHead e (Bind Abbr) 
u0))).(lt_le_e i i0 (pc3 c0 t2 t0) (\lambda (H6: (lt i i0)).(let H7 \def 
(csubst0_getl_lt i0 i H6 c c0 u0 H4 (CHead d (Bind Abbr) u) H0) in (or4_ind 
(getl i c0 (CHead d (Bind Abbr) u)) (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead 
e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl i c0 (CHead e0 (Bind b) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) 
u0 u1 w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u1: T).(getl i c0 
(CHead e2 (Bind b) u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1))))))) (\lambda 
(b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl 
i c0 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) u0 u1 w)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i0 (S i)) u0 e1 e2))))))) (pc3 c0 t2 t0) (\lambda (H8: 
(getl i c0 (CHead d (Bind Abbr) u))).(pc3_pr2_r c0 t2 t0 (pr2_delta c0 d u i 
H8 t2 t3 H1 t0 H2))) (\lambda (H8: (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead 
e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl i c0 (CHead e0 (Bind b) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) 
u0 u1 w))))))).(ex3_4_ind B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e0 (Bind b) 
u1)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(getl i c0 (CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) u0 u1 w))))) 
(pc3 c0 t2 t0) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: T).(\lambda 
(x3: T).(\lambda (H9: (eq C (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x2))).(\lambda (H10: (getl i c0 (CHead x1 (Bind x0) x3))).(\lambda (H11: 
(subst0 (minus i0 (S i)) u0 x2 x3)).(let H12 \def (f_equal C C (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | 
(CHead c3 _ _) \Rightarrow c3])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x2) H9) in ((let H13 \def (f_equal C B (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x2) H9) in ((let H14 \def (f_equal C T (\lambda (e0: C).(match 
e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ 
t5) \Rightarrow t5])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x2) H9) in 
(\lambda (H15: (eq B Abbr x0)).(\lambda (H16: (eq C d x1)).(let H17 \def 
(eq_ind_r T x2 (\lambda (t5: T).(subst0 (minus i0 (S i)) u0 t5 x3)) H11 u 
H14) in (let H18 \def (eq_ind_r C x1 (\lambda (c3: C).(getl i c0 (CHead c3 
(Bind x0) x3))) H10 d H16) in (let H19 \def (eq_ind_r B x0 (\lambda (b: 
B).(getl i c0 (CHead d (Bind b) x3))) H18 Abbr H15) in (ex2_ind T (\lambda 
(t5: T).(subst0 i x3 t3 t5)) (\lambda (t5: T).(subst0 (S (plus (minus i0 (S 
i)) i)) u0 t0 t5)) (pc3 c0 t2 t0) (\lambda (x: T).(\lambda (H20: (subst0 i x3 
t3 x)).(\lambda (H21: (subst0 (S (plus (minus i0 (S i)) i)) u0 t0 x)).(let 
H22 \def (eq_ind_r nat (S (plus (minus i0 (S i)) i)) (\lambda (n: 
nat).(subst0 n u0 t0 x)) H21 i0 (lt_plus_minus_r i i0 H6)) in (pc3_pr2_u c0 x 
t2 (pr2_delta c0 d x3 i H19 t2 t3 H1 x H20) t0 (pc3_pr2_x c0 x t0 (pr2_delta 
c0 e u0 i0 (csubst0_getl_ge i0 i0 (le_n i0) c c0 u0 H4 (CHead e (Bind Abbr) 
u0) H5) t0 t0 (pr0_refl t0) x H22))))))) (subst0_subst0_back t3 t0 u i H2 x3 
u0 (minus i0 (S i)) H17)))))))) H13)) H12))))))))) H8)) (\lambda (H8: (ex3_4 
B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq 
C (CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u1: T).(getl i c0 (CHead e2 
(Bind b) u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 (minus i0 (S i)) u0 e1 e2))))))).(ex3_4_ind B C C T (\lambda 
(b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq C (CHead d (Bind 
Abbr) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: B).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u1: T).(getl i c0 (CHead e2 (Bind b) u1)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i0 (S 
i)) u0 e1 e2))))) (pc3 c0 t2 t0) (\lambda (x0: B).(\lambda (x1: C).(\lambda 
(x2: C).(\lambda (x3: T).(\lambda (H9: (eq C (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x3))).(\lambda (H10: (getl i c0 (CHead x2 (Bind x0) 
x3))).(\lambda (H11: (csubst0 (minus i0 (S i)) u0 x1 x2)).(let H12 \def 
(f_equal C C (\lambda (e0: C).(match e0 in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow d | (CHead c3 _ _) \Rightarrow c3])) (CHead d (Bind 
Abbr) u) (CHead x1 (Bind x0) x3) H9) in ((let H13 \def (f_equal C B (\lambda 
(e0: C).(match e0 in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow 
Abbr | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).B) with 
[(Bind b) \Rightarrow b | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) 
u) (CHead x1 (Bind x0) x3) H9) in ((let H14 \def (f_equal C T (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | 
(CHead _ _ t5) \Rightarrow t5])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x3) H9) in (\lambda (H15: (eq B Abbr x0)).(\lambda (H16: (eq C d x1)).(let 
H17 \def (eq_ind_r T x3 (\lambda (t5: T).(getl i c0 (CHead x2 (Bind x0) t5))) 
H10 u H14) in (let H18 \def (eq_ind_r C x1 (\lambda (c3: C).(csubst0 (minus 
i0 (S i)) u0 c3 x2)) H11 d H16) in (let H19 \def (eq_ind_r B x0 (\lambda (b: 
B).(getl i c0 (CHead x2 (Bind b) u))) H17 Abbr H15) in (pc3_pr2_r c0 t2 t0 
(pr2_delta c0 x2 u i H19 t2 t3 H1 t0 H2)))))))) H13)) H12))))))))) H8)) 
(\lambda (H8: (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(getl i c0 (CHead e2 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 
e2)))))))).(ex4_5_ind B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(getl i c0 (CHead e2 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2)))))) 
(pc3 c0 t2 t0) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: C).(\lambda 
(x3: T).(\lambda (x4: T).(\lambda (H9: (eq C (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x3))).(\lambda (H10: (getl i c0 (CHead x2 (Bind x0) 
x4))).(\lambda (H11: (subst0 (minus i0 (S i)) u0 x3 x4)).(\lambda (H12: 
(csubst0 (minus i0 (S i)) u0 x1 x2)).(let H13 \def (f_equal C C (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | 
(CHead c3 _ _) \Rightarrow c3])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x3) H9) in ((let H14 \def (f_equal C B (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x3) H9) in ((let H15 \def (f_equal C T (\lambda (e0: C).(match 
e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ 
t5) \Rightarrow t5])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x3) H9) in 
(\lambda (H16: (eq B Abbr x0)).(\lambda (H17: (eq C d x1)).(let H18 \def 
(eq_ind_r T x3 (\lambda (t5: T).(subst0 (minus i0 (S i)) u0 t5 x4)) H11 u 
H15) in (let H19 \def (eq_ind_r C x1 (\lambda (c3: C).(csubst0 (minus i0 (S 
i)) u0 c3 x2)) H12 d H17) in (let H20 \def (eq_ind_r B x0 (\lambda (b: 
B).(getl i c0 (CHead x2 (Bind b) x4))) H10 Abbr H16) in (ex2_ind T (\lambda 
(t5: T).(subst0 i x4 t3 t5)) (\lambda (t5: T).(subst0 (S (plus (minus i0 (S 
i)) i)) u0 t0 t5)) (pc3 c0 t2 t0) (\lambda (x: T).(\lambda (H21: (subst0 i x4 
t3 x)).(\lambda (H22: (subst0 (S (plus (minus i0 (S i)) i)) u0 t0 x)).(let 
H23 \def (eq_ind_r nat (S (plus (minus i0 (S i)) i)) (\lambda (n: 
nat).(subst0 n u0 t0 x)) H22 i0 (lt_plus_minus_r i i0 H6)) in (pc3_pr2_u c0 x 
t2 (pr2_delta c0 x2 x4 i H20 t2 t3 H1 x H21) t0 (pc3_pr2_x c0 x t0 (pr2_delta 
c0 e u0 i0 (csubst0_getl_ge i0 i0 (le_n i0) c c0 u0 H4 (CHead e (Bind Abbr) 
u0) H5) t0 t0 (pr0_refl t0) x H23))))))) (subst0_subst0_back t3 t0 u i H2 x4 
u0 (minus i0 (S i)) H18)))))))) H14)) H13))))))))))) H8)) H7))) (\lambda (H6: 
(le i0 i)).(pc3_pr2_r c0 t2 t0 (pr2_delta c0 d u i (csubst0_getl_ge i0 i H6 c 
c0 u0 H4 (CHead d (Bind Abbr) u) H0) t2 t3 H1 t0 H2)))))))) (\lambda (t5: 
T).(\lambda (H4: (subst0 i0 u0 t2 t5)).(\lambda (c0: C).(\lambda (H5: 
(csubst0 i0 u0 c c0)).(\lambda (e: C).(\lambda (H6: (getl i0 c (CHead e (Bind 
Abbr) u0))).(lt_le_e i i0 (pc3 c0 t5 t0) (\lambda (H7: (lt i i0)).(let H8 
\def (csubst0_getl_lt i0 i H7 c c0 u0 H5 (CHead d (Bind Abbr) u) H0) in 
(or4_ind (getl i c0 (CHead d (Bind Abbr) u)) (ex3_4 B C T T (\lambda (b: 
B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind 
Abbr) u) (CHead e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(getl i c0 (CHead e0 (Bind b) w)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 
(Bind b) u1)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u1: T).(getl i c0 (CHead e2 (Bind b) u1)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 (Bind b) 
u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(getl i c0 (CHead e2 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2))))))) 
(pc3 c0 t5 t0) (\lambda (H9: (getl i c0 (CHead d (Bind Abbr) u))).(pc3_pr2_u2 
c0 t2 t5 (pr2_delta c0 e u0 i0 (csubst0_getl_ge i0 i0 (le_n i0) c c0 u0 H5 
(CHead e (Bind Abbr) u0) H6) t2 t2 (pr0_refl t2) t5 H4) t0 (pc3_pr2_r c0 t2 
t0 (pr2_delta c0 d u i H9 t2 t3 H1 t0 H2)))) (\lambda (H9: (ex3_4 B C T T 
(\lambda (b: B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C 
(CHead d (Bind Abbr) u) (CHead e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(getl i c0 (CHead e0 (Bind b) w)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w))))))).(ex3_4_ind B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead 
e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl i c0 (CHead e0 (Bind b) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) 
u0 u1 w))))) (pc3 c0 t5 t0) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: 
T).(\lambda (x3: T).(\lambda (H10: (eq C (CHead d (Bind Abbr) u) (CHead x1 
(Bind x0) x2))).(\lambda (H11: (getl i c0 (CHead x1 (Bind x0) x3))).(\lambda 
(H12: (subst0 (minus i0 (S i)) u0 x2 x3)).(let H13 \def (f_equal C C (\lambda 
(e0: C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow 
d | (CHead c3 _ _) \Rightarrow c3])) (CHead d (Bind Abbr) u) (CHead x1 (Bind 
x0) x2) H10) in ((let H14 \def (f_equal C B (\lambda (e0: C).(match e0 in C 
return (\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x2) H10) in ((let H15 \def (f_equal C T (\lambda (e0: C).(match 
e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ 
t6) \Rightarrow t6])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x2) H10) in 
(\lambda (H16: (eq B Abbr x0)).(\lambda (H17: (eq C d x1)).(let H18 \def 
(eq_ind_r T x2 (\lambda (t6: T).(subst0 (minus i0 (S i)) u0 t6 x3)) H12 u 
H15) in (let H19 \def (eq_ind_r C x1 (\lambda (c3: C).(getl i c0 (CHead c3 
(Bind x0) x3))) H11 d H17) in (let H20 \def (eq_ind_r B x0 (\lambda (b: 
B).(getl i c0 (CHead d (Bind b) x3))) H19 Abbr H16) in (ex2_ind T (\lambda 
(t6: T).(subst0 i x3 t3 t6)) (\lambda (t6: T).(subst0 (S (plus (minus i0 (S 
i)) i)) u0 t0 t6)) (pc3 c0 t5 t0) (\lambda (x: T).(\lambda (H21: (subst0 i x3 
t3 x)).(\lambda (H22: (subst0 (S (plus (minus i0 (S i)) i)) u0 t0 x)).(let 
H23 \def (eq_ind_r nat (S (plus (minus i0 (S i)) i)) (\lambda (n: 
nat).(subst0 n u0 t0 x)) H22 i0 (lt_plus_minus_r i i0 H7)) in (pc3_pr2_u2 c0 
t2 t5 (pr2_delta c0 e u0 i0 (csubst0_getl_ge i0 i0 (le_n i0) c c0 u0 H5 
(CHead e (Bind Abbr) u0) H6) t2 t2 (pr0_refl t2) t5 H4) t0 (pc3_pr2_u c0 x t2 
(pr2_delta c0 d x3 i H20 t2 t3 H1 x H21) t0 (pc3_pr2_x c0 x t0 (pr2_delta c0 
e u0 i0 (csubst0_getl_ge i0 i0 (le_n i0) c c0 u0 H5 (CHead e (Bind Abbr) u0) 
H6) t0 t0 (pr0_refl t0) x H23)))))))) (subst0_subst0_back t3 t0 u i H2 x3 u0 
(minus i0 (S i)) H18)))))))) H14)) H13))))))))) H9)) (\lambda (H9: (ex3_4 B C 
C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq C 
(CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u1: T).(getl i c0 (CHead e2 (Bind b) 
u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus i0 (S i)) u0 e1 e2))))))).(ex3_4_ind B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq C (CHead d (Bind 
Abbr) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: B).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u1: T).(getl i c0 (CHead e2 (Bind b) u1)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i0 (S 
i)) u0 e1 e2))))) (pc3 c0 t5 t0) (\lambda (x0: B).(\lambda (x1: C).(\lambda 
(x2: C).(\lambda (x3: T).(\lambda (H10: (eq C (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x3))).(\lambda (H11: (getl i c0 (CHead x2 (Bind x0) 
x3))).(\lambda (H12: (csubst0 (minus i0 (S i)) u0 x1 x2)).(let H13 \def 
(f_equal C C (\lambda (e0: C).(match e0 in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow d | (CHead c3 _ _) \Rightarrow c3])) (CHead d (Bind 
Abbr) u) (CHead x1 (Bind x0) x3) H10) in ((let H14 \def (f_equal C B (\lambda 
(e0: C).(match e0 in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow 
Abbr | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).B) with 
[(Bind b) \Rightarrow b | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) 
u) (CHead x1 (Bind x0) x3) H10) in ((let H15 \def (f_equal C T (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | 
(CHead _ _ t6) \Rightarrow t6])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x3) H10) in (\lambda (H16: (eq B Abbr x0)).(\lambda (H17: (eq C d x1)).(let 
H18 \def (eq_ind_r T x3 (\lambda (t6: T).(getl i c0 (CHead x2 (Bind x0) t6))) 
H11 u H15) in (let H19 \def (eq_ind_r C x1 (\lambda (c3: C).(csubst0 (minus 
i0 (S i)) u0 c3 x2)) H12 d H17) in (let H20 \def (eq_ind_r B x0 (\lambda (b: 
B).(getl i c0 (CHead x2 (Bind b) u))) H18 Abbr H16) in (pc3_pr2_u2 c0 t2 t5 
(pr2_delta c0 e u0 i0 (csubst0_getl_ge i0 i0 (le_n i0) c c0 u0 H5 (CHead e 
(Bind Abbr) u0) H6) t2 t2 (pr0_refl t2) t5 H4) t0 (pc3_pr2_r c0 t2 t0 
(pr2_delta c0 x2 u i H20 t2 t3 H1 t0 H2))))))))) H14)) H13))))))))) H9)) 
(\lambda (H9: (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(getl i c0 (CHead e2 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 
e2)))))))).(ex4_5_ind B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(getl i c0 (CHead e2 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2)))))) 
(pc3 c0 t5 t0) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: C).(\lambda 
(x3: T).(\lambda (x4: T).(\lambda (H10: (eq C (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x3))).(\lambda (H11: (getl i c0 (CHead x2 (Bind x0) 
x4))).(\lambda (H12: (subst0 (minus i0 (S i)) u0 x3 x4)).(\lambda (H13: 
(csubst0 (minus i0 (S i)) u0 x1 x2)).(let H14 \def (f_equal C C (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | 
(CHead c3 _ _) \Rightarrow c3])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x3) H10) in ((let H15 \def (f_equal C B (\lambda (e0: C).(match e0 in C 
return (\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x3) H10) in ((let H16 \def (f_equal C T (\lambda (e0: C).(match 
e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ 
t6) \Rightarrow t6])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x3) H10) in 
(\lambda (H17: (eq B Abbr x0)).(\lambda (H18: (eq C d x1)).(let H19 \def 
(eq_ind_r T x3 (\lambda (t6: T).(subst0 (minus i0 (S i)) u0 t6 x4)) H12 u 
H16) in (let H20 \def (eq_ind_r C x1 (\lambda (c3: C).(csubst0 (minus i0 (S 
i)) u0 c3 x2)) H13 d H18) in (let H21 \def (eq_ind_r B x0 (\lambda (b: 
B).(getl i c0 (CHead x2 (Bind b) x4))) H11 Abbr H17) in (ex2_ind T (\lambda 
(t6: T).(subst0 i x4 t3 t6)) (\lambda (t6: T).(subst0 (S (plus (minus i0 (S 
i)) i)) u0 t0 t6)) (pc3 c0 t5 t0) (\lambda (x: T).(\lambda (H22: (subst0 i x4 
t3 x)).(\lambda (H23: (subst0 (S (plus (minus i0 (S i)) i)) u0 t0 x)).(let 
H24 \def (eq_ind_r nat (S (plus (minus i0 (S i)) i)) (\lambda (n: 
nat).(subst0 n u0 t0 x)) H23 i0 (lt_plus_minus_r i i0 H7)) in (pc3_pr2_u2 c0 
t2 t5 (pr2_delta c0 e u0 i0 (csubst0_getl_ge i0 i0 (le_n i0) c c0 u0 H5 
(CHead e (Bind Abbr) u0) H6) t2 t2 (pr0_refl t2) t5 H4) t0 (pc3_pr2_u c0 x t2 
(pr2_delta c0 x2 x4 i H21 t2 t3 H1 x H22) t0 (pc3_pr2_x c0 x t0 (pr2_delta c0 
e u0 i0 (csubst0_getl_ge i0 i0 (le_n i0) c c0 u0 H5 (CHead e (Bind Abbr) u0) 
H6) t0 t0 (pr0_refl t0) x H24)))))))) (subst0_subst0_back t3 t0 u i H2 x4 u0 
(minus i0 (S i)) H19)))))))) H15)) H14))))))))))) H9)) H8))) (\lambda (H7: 
(le i0 i)).(pc3_pr2_u2 c0 t2 t5 (pr2_delta c0 e u0 i0 (csubst0_getl_ge i0 i0 
(le_n i0) c c0 u0 H5 (CHead e (Bind Abbr) u0) H6) t2 t2 (pr0_refl t2) t5 H4) 
t0 (pc3_pr2_r c0 t2 t0 (pr2_delta c0 d u i (csubst0_getl_ge i0 i H7 c c0 u0 
H5 (CHead d (Bind Abbr) u) H0) t2 t3 H1 t0 H2))))))))))) c2 t4 
H3)))))))))))))))) c1 t1 t H)))).
(* COMMENTS
Initial nodes: 6455
END *)

theorem pc3_pr2_fsubst0_back:
 \forall (c1: C).(\forall (t: T).(\forall (t1: T).((pr2 c1 t t1) \to (\forall 
(i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t2: T).((fsubst0 i u c1 
t1 c2 t2) \to (\forall (e: C).((getl i c1 (CHead e (Bind Abbr) u)) \to (pc3 
c2 t t2)))))))))))
\def
 \lambda (c1: C).(\lambda (t: T).(\lambda (t1: T).(\lambda (H: (pr2 c1 t 
t1)).(pr2_ind (\lambda (c: C).(\lambda (t0: T).(\lambda (t2: T).(\forall (i: 
nat).(\forall (u: T).(\forall (c2: C).(\forall (t3: T).((fsubst0 i u c t2 c2 
t3) \to (\forall (e: C).((getl i c (CHead e (Bind Abbr) u)) \to (pc3 c2 t0 
t3))))))))))) (\lambda (c: C).(\lambda (t2: T).(\lambda (t3: T).(\lambda (H0: 
(pr0 t2 t3)).(\lambda (i: nat).(\lambda (u: T).(\lambda (c2: C).(\lambda (t0: 
T).(\lambda (H1: (fsubst0 i u c t3 c2 t0)).(fsubst0_ind i u c t3 (\lambda 
(c0: C).(\lambda (t4: T).(\forall (e: C).((getl i c (CHead e (Bind Abbr) u)) 
\to (pc3 c0 t2 t4))))) (\lambda (t4: T).(\lambda (H2: (subst0 i u t3 
t4)).(\lambda (e: C).(\lambda (H3: (getl i c (CHead e (Bind Abbr) 
u))).(pc3_pr2_u c t3 t2 (pr2_free c t2 t3 H0) t4 (pc3_pr2_r c t3 t4 
(pr2_delta c e u i H3 t3 t3 (pr0_refl t3) t4 H2))))))) (\lambda (c0: 
C).(\lambda (_: (csubst0 i u c c0)).(\lambda (e: C).(\lambda (_: (getl i c 
(CHead e (Bind Abbr) u))).(pc3_pr2_r c0 t2 t3 (pr2_free c0 t2 t3 H0)))))) 
(\lambda (t4: T).(\lambda (H2: (subst0 i u t3 t4)).(\lambda (c0: C).(\lambda 
(H3: (csubst0 i u c c0)).(\lambda (e: C).(\lambda (H4: (getl i c (CHead e 
(Bind Abbr) u))).(pc3_pr2_u c0 t3 t2 (pr2_free c0 t2 t3 H0) t4 (pc3_pr2_r c0 
t3 t4 (pr2_delta c0 e u i (csubst0_getl_ge i i (le_n i) c c0 u H3 (CHead e 
(Bind Abbr) u) H4) t3 t3 (pr0_refl t3) t4 H2))))))))) c2 t0 H1)))))))))) 
(\lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H0: (getl i c (CHead d (Bind Abbr) u))).(\lambda (t2: T).(\lambda (t3: 
T).(\lambda (H1: (pr0 t2 t3)).(\lambda (t0: T).(\lambda (H2: (subst0 i u t3 
t0)).(\lambda (i0: nat).(\lambda (u0: T).(\lambda (c2: C).(\lambda (t4: 
T).(\lambda (H3: (fsubst0 i0 u0 c t0 c2 t4)).(fsubst0_ind i0 u0 c t0 (\lambda 
(c0: C).(\lambda (t5: T).(\forall (e: C).((getl i0 c (CHead e (Bind Abbr) 
u0)) \to (pc3 c0 t2 t5))))) (\lambda (t5: T).(\lambda (H4: (subst0 i0 u0 t0 
t5)).(\lambda (e: C).(\lambda (H5: (getl i0 c (CHead e (Bind Abbr) 
u0))).(pc3_t t3 c t2 (pc3_pr3_r c t2 t3 (pr3_pr2 c t2 t3 (pr2_free c t2 t3 
H1))) t5 (pc3_pr3_r c t3 t5 (pr3_sing c t0 t3 (pr2_delta c d u i H0 t3 t3 
(pr0_refl t3) t0 H2) t5 (pr3_pr2 c t0 t5 (pr2_delta c e u0 i0 H5 t0 t0 
(pr0_refl t0) t5 H4))))))))) (\lambda (c0: C).(\lambda (H4: (csubst0 i0 u0 c 
c0)).(\lambda (e: C).(\lambda (H5: (getl i0 c (CHead e (Bind Abbr) 
u0))).(lt_le_e i i0 (pc3 c0 t2 t0) (\lambda (H6: (lt i i0)).(let H7 \def 
(csubst0_getl_lt i0 i H6 c c0 u0 H4 (CHead d (Bind Abbr) u) H0) in (or4_ind 
(getl i c0 (CHead d (Bind Abbr) u)) (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead 
e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl i c0 (CHead e0 (Bind b) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) 
u0 u1 w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u1: T).(getl i c0 
(CHead e2 (Bind b) u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1))))))) (\lambda 
(b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl 
i c0 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) u0 u1 w)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i0 (S i)) u0 e1 e2))))))) (pc3 c0 t2 t0) (\lambda (H8: 
(getl i c0 (CHead d (Bind Abbr) u))).(pc3_pr2_r c0 t2 t0 (pr2_delta c0 d u i 
H8 t2 t3 H1 t0 H2))) (\lambda (H8: (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead 
e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl i c0 (CHead e0 (Bind b) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) 
u0 u1 w))))))).(ex3_4_ind B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e0 (Bind b) 
u1)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(getl i c0 (CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) u0 u1 w))))) 
(pc3 c0 t2 t0) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: T).(\lambda 
(x3: T).(\lambda (H9: (eq C (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x2))).(\lambda (H10: (getl i c0 (CHead x1 (Bind x0) x3))).(\lambda (H11: 
(subst0 (minus i0 (S i)) u0 x2 x3)).(let H12 \def (f_equal C C (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | 
(CHead c3 _ _) \Rightarrow c3])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x2) H9) in ((let H13 \def (f_equal C B (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x2) H9) in ((let H14 \def (f_equal C T (\lambda (e0: C).(match 
e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ 
t5) \Rightarrow t5])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x2) H9) in 
(\lambda (H15: (eq B Abbr x0)).(\lambda (H16: (eq C d x1)).(let H17 \def 
(eq_ind_r T x2 (\lambda (t5: T).(subst0 (minus i0 (S i)) u0 t5 x3)) H11 u 
H14) in (let H18 \def (eq_ind_r C x1 (\lambda (c3: C).(getl i c0 (CHead c3 
(Bind x0) x3))) H10 d H16) in (let H19 \def (eq_ind_r B x0 (\lambda (b: 
B).(getl i c0 (CHead d (Bind b) x3))) H18 Abbr H15) in (ex2_ind T (\lambda 
(t5: T).(subst0 i x3 t3 t5)) (\lambda (t5: T).(subst0 (S (plus (minus i0 (S 
i)) i)) u0 t0 t5)) (pc3 c0 t2 t0) (\lambda (x: T).(\lambda (H20: (subst0 i x3 
t3 x)).(\lambda (H21: (subst0 (S (plus (minus i0 (S i)) i)) u0 t0 x)).(let 
H22 \def (eq_ind_r nat (S (plus (minus i0 (S i)) i)) (\lambda (n: 
nat).(subst0 n u0 t0 x)) H21 i0 (lt_plus_minus_r i i0 H6)) in (pc3_pr2_u c0 x 
t2 (pr2_delta c0 d x3 i H19 t2 t3 H1 x H20) t0 (pc3_pr2_x c0 x t0 (pr2_delta 
c0 e u0 i0 (csubst0_getl_ge i0 i0 (le_n i0) c c0 u0 H4 (CHead e (Bind Abbr) 
u0) H5) t0 t0 (pr0_refl t0) x H22))))))) (subst0_subst0_back t3 t0 u i H2 x3 
u0 (minus i0 (S i)) H17)))))))) H13)) H12))))))))) H8)) (\lambda (H8: (ex3_4 
B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq 
C (CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u1: T).(getl i c0 (CHead e2 
(Bind b) u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 (minus i0 (S i)) u0 e1 e2))))))).(ex3_4_ind B C C T (\lambda 
(b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq C (CHead d (Bind 
Abbr) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: B).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u1: T).(getl i c0 (CHead e2 (Bind b) u1)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i0 (S 
i)) u0 e1 e2))))) (pc3 c0 t2 t0) (\lambda (x0: B).(\lambda (x1: C).(\lambda 
(x2: C).(\lambda (x3: T).(\lambda (H9: (eq C (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x3))).(\lambda (H10: (getl i c0 (CHead x2 (Bind x0) 
x3))).(\lambda (H11: (csubst0 (minus i0 (S i)) u0 x1 x2)).(let H12 \def 
(f_equal C C (\lambda (e0: C).(match e0 in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow d | (CHead c3 _ _) \Rightarrow c3])) (CHead d (Bind 
Abbr) u) (CHead x1 (Bind x0) x3) H9) in ((let H13 \def (f_equal C B (\lambda 
(e0: C).(match e0 in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow 
Abbr | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).B) with 
[(Bind b) \Rightarrow b | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) 
u) (CHead x1 (Bind x0) x3) H9) in ((let H14 \def (f_equal C T (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | 
(CHead _ _ t5) \Rightarrow t5])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x3) H9) in (\lambda (H15: (eq B Abbr x0)).(\lambda (H16: (eq C d x1)).(let 
H17 \def (eq_ind_r T x3 (\lambda (t5: T).(getl i c0 (CHead x2 (Bind x0) t5))) 
H10 u H14) in (let H18 \def (eq_ind_r C x1 (\lambda (c3: C).(csubst0 (minus 
i0 (S i)) u0 c3 x2)) H11 d H16) in (let H19 \def (eq_ind_r B x0 (\lambda (b: 
B).(getl i c0 (CHead x2 (Bind b) u))) H17 Abbr H15) in (pc3_pr2_r c0 t2 t0 
(pr2_delta c0 x2 u i H19 t2 t3 H1 t0 H2)))))))) H13)) H12))))))))) H8)) 
(\lambda (H8: (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(getl i c0 (CHead e2 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 
e2)))))))).(ex4_5_ind B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(getl i c0 (CHead e2 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2)))))) 
(pc3 c0 t2 t0) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: C).(\lambda 
(x3: T).(\lambda (x4: T).(\lambda (H9: (eq C (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x3))).(\lambda (H10: (getl i c0 (CHead x2 (Bind x0) 
x4))).(\lambda (H11: (subst0 (minus i0 (S i)) u0 x3 x4)).(\lambda (H12: 
(csubst0 (minus i0 (S i)) u0 x1 x2)).(let H13 \def (f_equal C C (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | 
(CHead c3 _ _) \Rightarrow c3])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x3) H9) in ((let H14 \def (f_equal C B (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x3) H9) in ((let H15 \def (f_equal C T (\lambda (e0: C).(match 
e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ 
t5) \Rightarrow t5])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x3) H9) in 
(\lambda (H16: (eq B Abbr x0)).(\lambda (H17: (eq C d x1)).(let H18 \def 
(eq_ind_r T x3 (\lambda (t5: T).(subst0 (minus i0 (S i)) u0 t5 x4)) H11 u 
H15) in (let H19 \def (eq_ind_r C x1 (\lambda (c3: C).(csubst0 (minus i0 (S 
i)) u0 c3 x2)) H12 d H17) in (let H20 \def (eq_ind_r B x0 (\lambda (b: 
B).(getl i c0 (CHead x2 (Bind b) x4))) H10 Abbr H16) in (ex2_ind T (\lambda 
(t5: T).(subst0 i x4 t3 t5)) (\lambda (t5: T).(subst0 (S (plus (minus i0 (S 
i)) i)) u0 t0 t5)) (pc3 c0 t2 t0) (\lambda (x: T).(\lambda (H21: (subst0 i x4 
t3 x)).(\lambda (H22: (subst0 (S (plus (minus i0 (S i)) i)) u0 t0 x)).(let 
H23 \def (eq_ind_r nat (S (plus (minus i0 (S i)) i)) (\lambda (n: 
nat).(subst0 n u0 t0 x)) H22 i0 (lt_plus_minus_r i i0 H6)) in (pc3_pr2_u c0 x 
t2 (pr2_delta c0 x2 x4 i H20 t2 t3 H1 x H21) t0 (pc3_pr2_x c0 x t0 (pr2_delta 
c0 e u0 i0 (csubst0_getl_ge i0 i0 (le_n i0) c c0 u0 H4 (CHead e (Bind Abbr) 
u0) H5) t0 t0 (pr0_refl t0) x H23))))))) (subst0_subst0_back t3 t0 u i H2 x4 
u0 (minus i0 (S i)) H18)))))))) H14)) H13))))))))))) H8)) H7))) (\lambda (H6: 
(le i0 i)).(pc3_pr2_r c0 t2 t0 (pr2_delta c0 d u i (csubst0_getl_ge i0 i H6 c 
c0 u0 H4 (CHead d (Bind Abbr) u) H0) t2 t3 H1 t0 H2)))))))) (\lambda (t5: 
T).(\lambda (H4: (subst0 i0 u0 t0 t5)).(\lambda (c0: C).(\lambda (H5: 
(csubst0 i0 u0 c c0)).(\lambda (e: C).(\lambda (H6: (getl i0 c (CHead e (Bind 
Abbr) u0))).(lt_le_e i i0 (pc3 c0 t2 t5) (\lambda (H7: (lt i i0)).(let H8 
\def (csubst0_getl_lt i0 i H7 c c0 u0 H5 (CHead d (Bind Abbr) u) H0) in 
(or4_ind (getl i c0 (CHead d (Bind Abbr) u)) (ex3_4 B C T T (\lambda (b: 
B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind 
Abbr) u) (CHead e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(getl i c0 (CHead e0 (Bind b) w)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 
(Bind b) u1)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u1: T).(getl i c0 (CHead e2 (Bind b) u1)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 (Bind b) 
u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(getl i c0 (CHead e2 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2))))))) 
(pc3 c0 t2 t5) (\lambda (H9: (getl i c0 (CHead d (Bind Abbr) u))).(pc3_pr2_u 
c0 t3 t2 (pr2_free c0 t2 t3 H1) t5 (pc3_pr3_r c0 t3 t5 (pr3_sing c0 t0 t3 
(pr2_delta c0 d u i H9 t3 t3 (pr0_refl t3) t0 H2) t5 (pr3_pr2 c0 t0 t5 
(pr2_delta c0 e u0 i0 (csubst0_getl_ge i0 i0 (le_n i0) c c0 u0 H5 (CHead e 
(Bind Abbr) u0) H6) t0 t0 (pr0_refl t0) t5 H4)))))) (\lambda (H9: (ex3_4 B C 
T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C 
(CHead d (Bind Abbr) u) (CHead e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(getl i c0 (CHead e0 (Bind b) w)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w))))))).(ex3_4_ind B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead 
e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl i c0 (CHead e0 (Bind b) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i0 (S i)) 
u0 u1 w))))) (pc3 c0 t2 t5) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: 
T).(\lambda (x3: T).(\lambda (H10: (eq C (CHead d (Bind Abbr) u) (CHead x1 
(Bind x0) x2))).(\lambda (H11: (getl i c0 (CHead x1 (Bind x0) x3))).(\lambda 
(H12: (subst0 (minus i0 (S i)) u0 x2 x3)).(let H13 \def (f_equal C C (\lambda 
(e0: C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow 
d | (CHead c3 _ _) \Rightarrow c3])) (CHead d (Bind Abbr) u) (CHead x1 (Bind 
x0) x2) H10) in ((let H14 \def (f_equal C B (\lambda (e0: C).(match e0 in C 
return (\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x2) H10) in ((let H15 \def (f_equal C T (\lambda (e0: C).(match 
e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ 
t6) \Rightarrow t6])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x2) H10) in 
(\lambda (H16: (eq B Abbr x0)).(\lambda (H17: (eq C d x1)).(let H18 \def 
(eq_ind_r T x2 (\lambda (t6: T).(subst0 (minus i0 (S i)) u0 t6 x3)) H12 u 
H15) in (let H19 \def (eq_ind_r C x1 (\lambda (c3: C).(getl i c0 (CHead c3 
(Bind x0) x3))) H11 d H17) in (let H20 \def (eq_ind_r B x0 (\lambda (b: 
B).(getl i c0 (CHead d (Bind b) x3))) H19 Abbr H16) in (ex2_ind T (\lambda 
(t6: T).(subst0 i x3 t3 t6)) (\lambda (t6: T).(subst0 (S (plus (minus i0 (S 
i)) i)) u0 t0 t6)) (pc3 c0 t2 t5) (\lambda (x: T).(\lambda (H21: (subst0 i x3 
t3 x)).(\lambda (H22: (subst0 (S (plus (minus i0 (S i)) i)) u0 t0 x)).(let 
H23 \def (eq_ind_r nat (S (plus (minus i0 (S i)) i)) (\lambda (n: 
nat).(subst0 n u0 t0 x)) H22 i0 (lt_plus_minus_r i i0 H7)) in (pc3_pr2_u c0 x 
t2 (pr2_delta c0 d x3 i H20 t2 t3 H1 x H21) t5 (pc3_pr2_u2 c0 t0 x (pr2_delta 
c0 e u0 i0 (csubst0_getl_ge i0 i0 (le_n i0) c c0 u0 H5 (CHead e (Bind Abbr) 
u0) H6) t0 t0 (pr0_refl t0) x H23) t5 (pc3_pr2_r c0 t0 t5 (pr2_delta c0 e u0 
i0 (csubst0_getl_ge i0 i0 (le_n i0) c c0 u0 H5 (CHead e (Bind Abbr) u0) H6) 
t0 t0 (pr0_refl t0) t5 H4)))))))) (subst0_subst0_back t3 t0 u i H2 x3 u0 
(minus i0 (S i)) H18)))))))) H14)) H13))))))))) H9)) (\lambda (H9: (ex3_4 B C 
C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq C 
(CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u1: T).(getl i c0 (CHead e2 (Bind b) 
u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus i0 (S i)) u0 e1 e2))))))).(ex3_4_ind B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq C (CHead d (Bind 
Abbr) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: B).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u1: T).(getl i c0 (CHead e2 (Bind b) u1)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i0 (S 
i)) u0 e1 e2))))) (pc3 c0 t2 t5) (\lambda (x0: B).(\lambda (x1: C).(\lambda 
(x2: C).(\lambda (x3: T).(\lambda (H10: (eq C (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x3))).(\lambda (H11: (getl i c0 (CHead x2 (Bind x0) 
x3))).(\lambda (H12: (csubst0 (minus i0 (S i)) u0 x1 x2)).(let H13 \def 
(f_equal C C (\lambda (e0: C).(match e0 in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow d | (CHead c3 _ _) \Rightarrow c3])) (CHead d (Bind 
Abbr) u) (CHead x1 (Bind x0) x3) H10) in ((let H14 \def (f_equal C B (\lambda 
(e0: C).(match e0 in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow 
Abbr | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).B) with 
[(Bind b) \Rightarrow b | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) 
u) (CHead x1 (Bind x0) x3) H10) in ((let H15 \def (f_equal C T (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | 
(CHead _ _ t6) \Rightarrow t6])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x3) H10) in (\lambda (H16: (eq B Abbr x0)).(\lambda (H17: (eq C d x1)).(let 
H18 \def (eq_ind_r T x3 (\lambda (t6: T).(getl i c0 (CHead x2 (Bind x0) t6))) 
H11 u H15) in (let H19 \def (eq_ind_r C x1 (\lambda (c3: C).(csubst0 (minus 
i0 (S i)) u0 c3 x2)) H12 d H17) in (let H20 \def (eq_ind_r B x0 (\lambda (b: 
B).(getl i c0 (CHead x2 (Bind b) u))) H18 Abbr H16) in (pc3_pr2_u c0 t0 t2 
(pr2_delta c0 x2 u i H20 t2 t3 H1 t0 H2) t5 (pc3_pr2_r c0 t0 t5 (pr2_delta c0 
e u0 i0 (csubst0_getl_ge i0 i0 (le_n i0) c c0 u0 H5 (CHead e (Bind Abbr) u0) 
H6) t0 t0 (pr0_refl t0) t5 H4))))))))) H14)) H13))))))))) H9)) (\lambda (H9: 
(ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 (Bind b) 
u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(getl i c0 (CHead e2 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 
e2)))))))).(ex4_5_ind B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(getl i c0 (CHead e2 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 
(minus i0 (S i)) u0 u1 w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (S i)) u0 e1 e2)))))) 
(pc3 c0 t2 t5) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: C).(\lambda 
(x3: T).(\lambda (x4: T).(\lambda (H10: (eq C (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x3))).(\lambda (H11: (getl i c0 (CHead x2 (Bind x0) 
x4))).(\lambda (H12: (subst0 (minus i0 (S i)) u0 x3 x4)).(\lambda (H13: 
(csubst0 (minus i0 (S i)) u0 x1 x2)).(let H14 \def (f_equal C C (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | 
(CHead c3 _ _) \Rightarrow c3])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x3) H10) in ((let H15 \def (f_equal C B (\lambda (e0: C).(match e0 in C 
return (\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x3) H10) in ((let H16 \def (f_equal C T (\lambda (e0: C).(match 
e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ 
t6) \Rightarrow t6])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x3) H10) in 
(\lambda (H17: (eq B Abbr x0)).(\lambda (H18: (eq C d x1)).(let H19 \def 
(eq_ind_r T x3 (\lambda (t6: T).(subst0 (minus i0 (S i)) u0 t6 x4)) H12 u 
H16) in (let H20 \def (eq_ind_r C x1 (\lambda (c3: C).(csubst0 (minus i0 (S 
i)) u0 c3 x2)) H13 d H18) in (let H21 \def (eq_ind_r B x0 (\lambda (b: 
B).(getl i c0 (CHead x2 (Bind b) x4))) H11 Abbr H17) in (ex2_ind T (\lambda 
(t6: T).(subst0 i x4 t3 t6)) (\lambda (t6: T).(subst0 (S (plus (minus i0 (S 
i)) i)) u0 t0 t6)) (pc3 c0 t2 t5) (\lambda (x: T).(\lambda (H22: (subst0 i x4 
t3 x)).(\lambda (H23: (subst0 (S (plus (minus i0 (S i)) i)) u0 t0 x)).(let 
H24 \def (eq_ind_r nat (S (plus (minus i0 (S i)) i)) (\lambda (n: 
nat).(subst0 n u0 t0 x)) H23 i0 (lt_plus_minus_r i i0 H7)) in (pc3_pr2_u c0 x 
t2 (pr2_delta c0 x2 x4 i H21 t2 t3 H1 x H22) t5 (pc3_pr2_u2 c0 t0 x 
(pr2_delta c0 e u0 i0 (csubst0_getl_ge i0 i0 (le_n i0) c c0 u0 H5 (CHead e 
(Bind Abbr) u0) H6) t0 t0 (pr0_refl t0) x H24) t5 (pc3_pr2_r c0 t0 t5 
(pr2_delta c0 e u0 i0 (csubst0_getl_ge i0 i0 (le_n i0) c c0 u0 H5 (CHead e 
(Bind Abbr) u0) H6) t0 t0 (pr0_refl t0) t5 H4)))))))) (subst0_subst0_back t3 
t0 u i H2 x4 u0 (minus i0 (S i)) H19)))))))) H15)) H14))))))))))) H9)) H8))) 
(\lambda (H7: (le i0 i)).(pc3_pr2_u c0 t0 t2 (pr2_delta c0 d u i 
(csubst0_getl_ge i0 i H7 c c0 u0 H5 (CHead d (Bind Abbr) u) H0) t2 t3 H1 t0 
H2) t5 (pc3_pr2_r c0 t0 t5 (pr2_delta c0 e u0 i0 (csubst0_getl_ge i0 i0 (le_n 
i0) c c0 u0 H5 (CHead e (Bind Abbr) u0) H6) t0 t0 (pr0_refl t0) t5 
H4))))))))))) c2 t4 H3)))))))))))))))) c1 t t1 H)))).
(* COMMENTS
Initial nodes: 6191
END *)

theorem pc3_fsubst0:
 \forall (c1: C).(\forall (t1: T).(\forall (t: T).((pc3 c1 t1 t) \to (\forall 
(i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t2: T).((fsubst0 i u c1 
t1 c2 t2) \to (\forall (e: C).((getl i c1 (CHead e (Bind Abbr) u)) \to (pc3 
c2 t2 t)))))))))))
\def
 \lambda (c1: C).(\lambda (t1: T).(\lambda (t: T).(\lambda (H: (pc3 c1 t1 
t)).(pc3_ind_left c1 (\lambda (t0: T).(\lambda (t2: T).(\forall (i: 
nat).(\forall (u: T).(\forall (c2: C).(\forall (t3: T).((fsubst0 i u c1 t0 c2 
t3) \to (\forall (e: C).((getl i c1 (CHead e (Bind Abbr) u)) \to (pc3 c2 t3 
t2)))))))))) (\lambda (t0: T).(\lambda (i: nat).(\lambda (u: T).(\lambda (c2: 
C).(\lambda (t2: T).(\lambda (H0: (fsubst0 i u c1 t0 c2 t2)).(fsubst0_ind i u 
c1 t0 (\lambda (c: C).(\lambda (t3: T).(\forall (e: C).((getl i c1 (CHead e 
(Bind Abbr) u)) \to (pc3 c t3 t0))))) (\lambda (t3: T).(\lambda (H1: (subst0 
i u t0 t3)).(\lambda (e: C).(\lambda (H2: (getl i c1 (CHead e (Bind Abbr) 
u))).(pc3_pr2_x c1 t3 t0 (pr2_delta c1 e u i H2 t0 t0 (pr0_refl t0) t3 
H1)))))) (\lambda (c0: C).(\lambda (_: (csubst0 i u c1 c0)).(\lambda (e: 
C).(\lambda (_: (getl i c1 (CHead e (Bind Abbr) u))).(pc3_refl c0 t0))))) 
(\lambda (t3: T).(\lambda (H1: (subst0 i u t0 t3)).(\lambda (c0: C).(\lambda 
(H2: (csubst0 i u c1 c0)).(\lambda (e: C).(\lambda (H3: (getl i c1 (CHead e 
(Bind Abbr) u))).(pc3_pr2_x c0 t3 t0 (pr2_delta c0 e u i (csubst0_getl_ge i i 
(le_n i) c1 c0 u H2 (CHead e (Bind Abbr) u) H3) t0 t0 (pr0_refl t0) t3 
H1)))))))) c2 t2 H0))))))) (\lambda (t0: T).(\lambda (t2: T).(\lambda (H0: 
(pr2 c1 t0 t2)).(\lambda (t3: T).(\lambda (H1: (pc3 c1 t2 t3)).(\lambda (H2: 
((\forall (i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t4: 
T).((fsubst0 i u c1 t2 c2 t4) \to (\forall (e: C).((getl i c1 (CHead e (Bind 
Abbr) u)) \to (pc3 c2 t4 t3)))))))))).(\lambda (i: nat).(\lambda (u: 
T).(\lambda (c2: C).(\lambda (t4: T).(\lambda (H3: (fsubst0 i u c1 t0 c2 
t4)).(fsubst0_ind i u c1 t0 (\lambda (c: C).(\lambda (t5: T).(\forall (e: 
C).((getl i c1 (CHead e (Bind Abbr) u)) \to (pc3 c t5 t3))))) (\lambda (t5: 
T).(\lambda (H4: (subst0 i u t0 t5)).(\lambda (e: C).(\lambda (H5: (getl i c1 
(CHead e (Bind Abbr) u))).(pc3_t t2 c1 t5 (pc3_pr2_fsubst0 c1 t0 t2 H0 i u c1 
t5 (fsubst0_snd i u c1 t0 t5 H4) e H5) t3 H1))))) (\lambda (c0: C).(\lambda 
(H4: (csubst0 i u c1 c0)).(\lambda (e: C).(\lambda (H5: (getl i c1 (CHead e 
(Bind Abbr) u))).(pc3_t t2 c0 t0 (pc3_pr2_fsubst0 c1 t0 t2 H0 i u c0 t0 
(fsubst0_fst i u c1 t0 c0 H4) e H5) t3 (H2 i u c0 t2 (fsubst0_fst i u c1 t2 
c0 H4) e H5)))))) (\lambda (t5: T).(\lambda (H4: (subst0 i u t0 t5)).(\lambda 
(c0: C).(\lambda (H5: (csubst0 i u c1 c0)).(\lambda (e: C).(\lambda (H6: 
(getl i c1 (CHead e (Bind Abbr) u))).(pc3_t t2 c0 t5 (pc3_pr2_fsubst0 c1 t0 
t2 H0 i u c0 t5 (fsubst0_both i u c1 t0 t5 H4 c0 H5) e H6) t3 (H2 i u c0 t2 
(fsubst0_fst i u c1 t2 c0 H5) e H6)))))))) c2 t4 H3)))))))))))) (\lambda (t0: 
T).(\lambda (t2: T).(\lambda (H0: (pr2 c1 t0 t2)).(\lambda (t3: T).(\lambda 
(H1: (pc3 c1 t0 t3)).(\lambda (H2: ((\forall (i: nat).(\forall (u: 
T).(\forall (c2: C).(\forall (t4: T).((fsubst0 i u c1 t0 c2 t4) \to (\forall 
(e: C).((getl i c1 (CHead e (Bind Abbr) u)) \to (pc3 c2 t4 
t3)))))))))).(\lambda (i: nat).(\lambda (u: T).(\lambda (c2: C).(\lambda (t4: 
T).(\lambda (H3: (fsubst0 i u c1 t2 c2 t4)).(fsubst0_ind i u c1 t2 (\lambda 
(c: C).(\lambda (t5: T).(\forall (e: C).((getl i c1 (CHead e (Bind Abbr) u)) 
\to (pc3 c t5 t3))))) (\lambda (t5: T).(\lambda (H4: (subst0 i u t2 
t5)).(\lambda (e: C).(\lambda (H5: (getl i c1 (CHead e (Bind Abbr) 
u))).(pc3_t t0 c1 t5 (pc3_s c1 t5 t0 (pc3_pr2_fsubst0_back c1 t0 t2 H0 i u c1 
t5 (fsubst0_snd i u c1 t2 t5 H4) e H5)) t3 H1))))) (\lambda (c0: C).(\lambda 
(H4: (csubst0 i u c1 c0)).(\lambda (e: C).(\lambda (H5: (getl i c1 (CHead e 
(Bind Abbr) u))).(pc3_t t0 c0 t2 (pc3_s c0 t2 t0 (pc3_pr2_fsubst0_back c1 t0 
t2 H0 i u c0 t2 (fsubst0_fst i u c1 t2 c0 H4) e H5)) t3 (H2 i u c0 t0 
(fsubst0_fst i u c1 t0 c0 H4) e H5)))))) (\lambda (t5: T).(\lambda (H4: 
(subst0 i u t2 t5)).(\lambda (c0: C).(\lambda (H5: (csubst0 i u c1 
c0)).(\lambda (e: C).(\lambda (H6: (getl i c1 (CHead e (Bind Abbr) 
u))).(pc3_t t0 c0 t5 (pc3_s c0 t5 t0 (pc3_pr2_fsubst0_back c1 t0 t2 H0 i u c0 
t5 (fsubst0_both i u c1 t2 t5 H4 c0 H5) e H6)) t3 (H2 i u c0 t0 (fsubst0_fst 
i u c1 t0 c0 H5) e H6)))))))) c2 t4 H3)))))))))))) t1 t H)))).
(* COMMENTS
Initial nodes: 1249
END *)

