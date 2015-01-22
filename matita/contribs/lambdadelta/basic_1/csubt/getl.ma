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

include "Basic-1/csubt/clear.ma".

include "Basic-1/csubt/drop.ma".

include "Basic-1/getl/clear.ma".

theorem csubt_getl_abbr:
 \forall (g: G).(\forall (c1: C).(\forall (d1: C).(\forall (u: T).(\forall 
(n: nat).((getl n c1 (CHead d1 (Bind Abbr) u)) \to (\forall (c2: C).((csubt g 
c1 c2) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl n 
c2 (CHead d2 (Bind Abbr) u)))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (d1: C).(\lambda (u: T).(\lambda 
(n: nat).(\lambda (H: (getl n c1 (CHead d1 (Bind Abbr) u))).(let H0 \def 
(getl_gen_all c1 (CHead d1 (Bind Abbr) u) n H) in (ex2_ind C (\lambda (e: 
C).(drop n O c1 e)) (\lambda (e: C).(clear e (CHead d1 (Bind Abbr) u))) 
(\forall (c2: C).((csubt g c1 c2) \to (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) u)))))) (\lambda (x: 
C).(\lambda (H1: (drop n O c1 x)).(\lambda (H2: (clear x (CHead d1 (Bind 
Abbr) u))).(C_ind (\lambda (c: C).((drop n O c1 c) \to ((clear c (CHead d1 
(Bind Abbr) u)) \to (\forall (c2: C).((csubt g c1 c2) \to (ex2 C (\lambda 
(d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) 
u))))))))) (\lambda (n0: nat).(\lambda (_: (drop n O c1 (CSort n0))).(\lambda 
(H4: (clear (CSort n0) (CHead d1 (Bind Abbr) u))).(clear_gen_sort (CHead d1 
(Bind Abbr) u) n0 H4 (\forall (c2: C).((csubt g c1 c2) \to (ex2 C (\lambda 
(d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) 
u)))))))))) (\lambda (x0: C).(\lambda (_: (((drop n O c1 x0) \to ((clear x0 
(CHead d1 (Bind Abbr) u)) \to (\forall (c2: C).((csubt g c1 c2) \to (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind 
Abbr) u)))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (H3: (drop n O c1 
(CHead x0 k t))).(\lambda (H4: (clear (CHead x0 k t) (CHead d1 (Bind Abbr) 
u))).(K_ind (\lambda (k0: K).((drop n O c1 (CHead x0 k0 t)) \to ((clear 
(CHead x0 k0 t) (CHead d1 (Bind Abbr) u)) \to (\forall (c2: C).((csubt g c1 
c2) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl n c2 
(CHead d2 (Bind Abbr) u))))))))) (\lambda (b: B).(\lambda (H5: (drop n O c1 
(CHead x0 (Bind b) t))).(\lambda (H6: (clear (CHead x0 (Bind b) t) (CHead d1 
(Bind Abbr) u))).(let H7 \def (f_equal C C (\lambda (e: C).(match e in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow d1 | (CHead c _ _) 
\Rightarrow c])) (CHead d1 (Bind Abbr) u) (CHead x0 (Bind b) t) 
(clear_gen_bind b x0 (CHead d1 (Bind Abbr) u) t H6)) in ((let H8 \def 
(f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow Abbr | (CHead _ k0 _) \Rightarrow (match k0 in K 
return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) 
\Rightarrow Abbr])])) (CHead d1 (Bind Abbr) u) (CHead x0 (Bind b) t) 
(clear_gen_bind b x0 (CHead d1 (Bind Abbr) u) t H6)) in ((let H9 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) (CHead d1 (Bind 
Abbr) u) (CHead x0 (Bind b) t) (clear_gen_bind b x0 (CHead d1 (Bind Abbr) u) 
t H6)) in (\lambda (H10: (eq B Abbr b)).(\lambda (H11: (eq C d1 x0)).(\lambda 
(c2: C).(\lambda (H12: (csubt g c1 c2)).(let H13 \def (eq_ind_r T t (\lambda 
(t0: T).(drop n O c1 (CHead x0 (Bind b) t0))) H5 u H9) in (let H14 \def 
(eq_ind_r B b (\lambda (b0: B).(drop n O c1 (CHead x0 (Bind b0) u))) H13 Abbr 
H10) in (let H15 \def (eq_ind_r C x0 (\lambda (c: C).(drop n O c1 (CHead c 
(Bind Abbr) u))) H14 d1 H11) in (ex2_ind C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(drop n O c2 (CHead d2 (Bind Abbr) u))) (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) u)))) 
(\lambda (x1: C).(\lambda (H16: (csubt g d1 x1)).(\lambda (H17: (drop n O c2 
(CHead x1 (Bind Abbr) u))).(ex_intro2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) u))) x1 H16 (getl_intro n 
c2 (CHead x1 (Bind Abbr) u) (CHead x1 (Bind Abbr) u) H17 (clear_bind Abbr x1 
u)))))) (csubt_drop_abbr g n c1 c2 H12 d1 u H15)))))))))) H8)) H7))))) 
(\lambda (f: F).(\lambda (H5: (drop n O c1 (CHead x0 (Flat f) t))).(\lambda 
(H6: (clear (CHead x0 (Flat f) t) (CHead d1 (Bind Abbr) u))).(let H7 \def H5 
in (unintro C c1 (\lambda (c: C).((drop n O c (CHead x0 (Flat f) t)) \to 
(\forall (c2: C).((csubt g c c2) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) u)))))))) (nat_ind (\lambda 
(n0: nat).(\forall (x1: C).((drop n0 O x1 (CHead x0 (Flat f) t)) \to (\forall 
(c2: C).((csubt g x1 c2) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(getl n0 c2 (CHead d2 (Bind Abbr) u))))))))) (\lambda (x1: 
C).(\lambda (H8: (drop O O x1 (CHead x0 (Flat f) t))).(\lambda (c2: 
C).(\lambda (H9: (csubt g x1 c2)).(let H10 \def (eq_ind C x1 (\lambda (c: 
C).(csubt g c c2)) H9 (CHead x0 (Flat f) t) (drop_gen_refl x1 (CHead x0 (Flat 
f) t) H8)) in (let H_y \def (clear_flat x0 (CHead d1 (Bind Abbr) u) 
(clear_gen_flat f x0 (CHead d1 (Bind Abbr) u) t H6) f t) in (let H11 \def 
(csubt_clear_conf g (CHead x0 (Flat f) t) c2 H10 (CHead d1 (Bind Abbr) u) 
H_y) in (ex2_ind C (\lambda (e2: C).(csubt g (CHead d1 (Bind Abbr) u) e2)) 
(\lambda (e2: C).(clear c2 e2)) (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (x2: 
C).(\lambda (H12: (csubt g (CHead d1 (Bind Abbr) u) x2)).(\lambda (H13: 
(clear c2 x2)).(let H14 \def (csubt_gen_abbr g d1 x2 u H12) in (ex2_ind C 
(\lambda (e2: C).(eq C x2 (CHead e2 (Bind Abbr) u))) (\lambda (e2: C).(csubt 
g d1 e2)) (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl O 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (x3: C).(\lambda (H15: (eq C x2 
(CHead x3 (Bind Abbr) u))).(\lambda (H16: (csubt g d1 x3)).(let H17 \def 
(eq_ind C x2 (\lambda (c: C).(clear c2 c)) H13 (CHead x3 (Bind Abbr) u) H15) 
in (ex_intro2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl O c2 
(CHead d2 (Bind Abbr) u))) x3 H16 (getl_intro O c2 (CHead x3 (Bind Abbr) u) 
c2 (drop_refl c2) H17)))))) H14))))) H11)))))))) (\lambda (n0: nat).(\lambda 
(H8: ((\forall (x1: C).((drop n0 O x1 (CHead x0 (Flat f) t)) \to (\forall 
(c2: C).((csubt g x1 c2) \to (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(getl n0 c2 (CHead d2 (Bind Abbr) u)))))))))).(\lambda (x1: 
C).(\lambda (H9: (drop (S n0) O x1 (CHead x0 (Flat f) t))).(\lambda (c2: 
C).(\lambda (H10: (csubt g x1 c2)).(let H11 \def (drop_clear x1 (CHead x0 
(Flat f) t) n0 H9) in (ex2_3_ind B C T (\lambda (b: B).(\lambda (e: 
C).(\lambda (v: T).(clear x1 (CHead e (Bind b) v))))) (\lambda (_: 
B).(\lambda (e: C).(\lambda (_: T).(drop n0 O e (CHead x0 (Flat f) t))))) 
(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl (S n0) c2 
(CHead d2 (Bind Abbr) u)))) (\lambda (x2: B).(\lambda (x3: C).(\lambda (x4: 
T).(\lambda (H12: (clear x1 (CHead x3 (Bind x2) x4))).(\lambda (H13: (drop n0 
O x3 (CHead x0 (Flat f) t))).(let H14 \def (csubt_clear_conf g x1 c2 H10 
(CHead x3 (Bind x2) x4) H12) in (ex2_ind C (\lambda (e2: C).(csubt g (CHead 
x3 (Bind x2) x4) e2)) (\lambda (e2: C).(clear c2 e2)) (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abbr) 
u)))) (\lambda (x5: C).(\lambda (H15: (csubt g (CHead x3 (Bind x2) x4) 
x5)).(\lambda (H16: (clear c2 x5)).(let H17 \def (csubt_gen_bind g x2 x3 x5 
x4 H15) in (ex2_3_ind B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: 
T).(eq C x5 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csubt g x3 e2)))) (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abbr) u)))) (\lambda 
(x6: B).(\lambda (x7: C).(\lambda (x8: T).(\lambda (H18: (eq C x5 (CHead x7 
(Bind x6) x8))).(\lambda (H19: (csubt g x3 x7)).(let H20 \def (eq_ind C x5 
(\lambda (c: C).(clear c2 c)) H16 (CHead x7 (Bind x6) x8) H18) in (let H21 
\def (H8 x3 H13 x7 H19) in (ex2_ind C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(getl n0 x7 (CHead d2 (Bind Abbr) u))) (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abbr) 
u)))) (\lambda (x9: C).(\lambda (H22: (csubt g d1 x9)).(\lambda (H23: (getl 
n0 x7 (CHead x9 (Bind Abbr) u))).(ex_intro2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abbr) u))) x9 H22 
(getl_clear_bind x6 c2 x7 x8 H20 (CHead x9 (Bind Abbr) u) n0 H23))))) 
H21)))))))) H17))))) H14))))))) H11)))))))) n) H7))))) k H3 H4))))))) x H1 
H2)))) H0))))))).
(* COMMENTS
Initial nodes: 2313
END *)

theorem csubt_getl_abst:
 \forall (g: G).(\forall (c1: C).(\forall (d1: C).(\forall (t: T).(\forall 
(n: nat).((getl n c1 (CHead d1 (Bind Abst) t)) \to (\forall (c2: C).((csubt g 
c1 c2) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u 
t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (d1: C).(\lambda (t: T).(\lambda 
(n: nat).(\lambda (H: (getl n c1 (CHead d1 (Bind Abst) t))).(let H0 \def 
(getl_gen_all c1 (CHead d1 (Bind Abst) t) n H) in (ex2_ind C (\lambda (e: 
C).(drop n O c1 e)) (\lambda (e: C).(clear e (CHead d1 (Bind Abst) t))) 
(\forall (c2: C).((csubt g c1 c2) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl n c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))))) 
(\lambda (x: C).(\lambda (H1: (drop n O c1 x)).(\lambda (H2: (clear x (CHead 
d1 (Bind Abst) t))).(C_ind (\lambda (c: C).((drop n O c1 c) \to ((clear c 
(CHead d1 (Bind Abst) t)) \to (\forall (c2: C).((csubt g c1 c2) \to (or (ex2 
C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl n c2 (CHead d2 
(Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u: T).(getl n c2 (CHead d2 (Bind Abbr) u)))) 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda 
(u: T).(ty3 g d2 u t)))))))))) (\lambda (n0: nat).(\lambda (_: (drop n O c1 
(CSort n0))).(\lambda (H4: (clear (CSort n0) (CHead d1 (Bind Abst) 
t))).(clear_gen_sort (CHead d1 (Bind Abst) t) n0 H4 (\forall (c2: C).((csubt 
g c1 c2) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u 
t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))))))))) (\lambda (x0: 
C).(\lambda (_: (((drop n O c1 x0) \to ((clear x0 (CHead d1 (Bind Abst) t)) 
\to (\forall (c2: C).((csubt g c1 c2) \to (or (ex2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl n c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t))))))))))).(\lambda (k: K).(\lambda (t0: T).(\lambda (H3: (drop n O c1 
(CHead x0 k t0))).(\lambda (H4: (clear (CHead x0 k t0) (CHead d1 (Bind Abst) 
t))).(K_ind (\lambda (k0: K).((drop n O c1 (CHead x0 k0 t0)) \to ((clear 
(CHead x0 k0 t0) (CHead d1 (Bind Abst) t)) \to (\forall (c2: C).((csubt g c1 
c2) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl n 
c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n c2 (CHead d2 
(Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda 
(d2: C).(\lambda (u: T).(ty3 g d2 u t)))))))))) (\lambda (b: B).(\lambda (H5: 
(drop n O c1 (CHead x0 (Bind b) t0))).(\lambda (H6: (clear (CHead x0 (Bind b) 
t0) (CHead d1 (Bind Abst) t))).(let H7 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d1 | 
(CHead c _ _) \Rightarrow c])) (CHead d1 (Bind Abst) t) (CHead x0 (Bind b) 
t0) (clear_gen_bind b x0 (CHead d1 (Bind Abst) t) t0 H6)) in ((let H8 \def 
(f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow Abst | (CHead _ k0 _) \Rightarrow (match k0 in K 
return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) 
\Rightarrow Abst])])) (CHead d1 (Bind Abst) t) (CHead x0 (Bind b) t0) 
(clear_gen_bind b x0 (CHead d1 (Bind Abst) t) t0 H6)) in ((let H9 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow t | (CHead _ _ t1) \Rightarrow t1])) (CHead d1 (Bind 
Abst) t) (CHead x0 (Bind b) t0) (clear_gen_bind b x0 (CHead d1 (Bind Abst) t) 
t0 H6)) in (\lambda (H10: (eq B Abst b)).(\lambda (H11: (eq C d1 
x0)).(\lambda (c2: C).(\lambda (H12: (csubt g c1 c2)).(let H13 \def (eq_ind_r 
T t0 (\lambda (t1: T).(drop n O c1 (CHead x0 (Bind b) t1))) H5 t H9) in (let 
H14 \def (eq_ind_r B b (\lambda (b0: B).(drop n O c1 (CHead x0 (Bind b0) t))) 
H13 Abst H10) in (let H15 \def (eq_ind_r C x0 (\lambda (c: C).(drop n O c1 
(CHead c (Bind Abst) t))) H14 d1 H11) in (or_ind (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(drop n O c2 (CHead d2 (Bind Abst) t)))) 
(ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u: T).(drop n O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: 
C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g 
d2 u t)))) (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u 
t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) (\lambda (H16: (ex2 
C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(drop n O c2 (CHead d2 
(Bind Abst) t))))).(ex2_ind C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(drop n O c2 (CHead d2 (Bind Abst) t))) (or (ex2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl n c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) 
(\lambda (x1: C).(\lambda (H17: (csubt g d1 x1)).(\lambda (H18: (drop n O c2 
(CHead x1 (Bind Abst) t))).(or_introl (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl n c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))) 
(ex_intro2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl n c2 
(CHead d2 (Bind Abst) t))) x1 H17 (getl_intro n c2 (CHead x1 (Bind Abst) t) 
(CHead x1 (Bind Abst) t) H18 (clear_bind Abst x1 t))))))) H16)) (\lambda 
(H16: (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u: T).(drop n O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: 
C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g 
d2 u t))))).(ex4_2_ind C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) 
(\lambda (d2: C).(\lambda (u: T).(drop n O c2 (CHead d2 (Bind Abbr) u)))) 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda 
(u: T).(ty3 g d2 u t))) (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u 
t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) (\lambda (x1: 
C).(\lambda (x2: T).(\lambda (H17: (csubt g d1 x1)).(\lambda (H18: (drop n O 
c2 (CHead x1 (Bind Abbr) x2))).(\lambda (H19: (ty3 g d1 x2 t)).(\lambda (H20: 
(ty3 g x1 x2 t)).(or_intror (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u 
t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))) (ex4_2_intro C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl n c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) x1 x2 
H17 (getl_intro n c2 (CHead x1 (Bind Abbr) x2) (CHead x1 (Bind Abbr) x2) H18 
(clear_bind Abbr x1 x2)) H19 H20)))))))) H16)) (csubt_drop_abst g n c1 c2 H12 
d1 t H15)))))))))) H8)) H7))))) (\lambda (f: F).(\lambda (H5: (drop n O c1 
(CHead x0 (Flat f) t0))).(\lambda (H6: (clear (CHead x0 (Flat f) t0) (CHead 
d1 (Bind Abst) t))).(let H7 \def H5 in (unintro C c1 (\lambda (c: C).((drop n 
O c (CHead x0 (Flat f) t0)) \to (\forall (c2: C).((csubt g c c2) \to (or (ex2 
C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl n c2 (CHead d2 
(Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u: T).(getl n c2 (CHead d2 (Bind Abbr) u)))) 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda 
(u: T).(ty3 g d2 u t))))))))) (nat_ind (\lambda (n0: nat).(\forall (x1: 
C).((drop n0 O x1 (CHead x0 (Flat f) t0)) \to (\forall (c2: C).((csubt g x1 
c2) \to (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl 
n0 c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n0 c2 (CHead d2 
(Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda 
(d2: C).(\lambda (u: T).(ty3 g d2 u t)))))))))) (\lambda (x1: C).(\lambda 
(H8: (drop O O x1 (CHead x0 (Flat f) t0))).(\lambda (c2: C).(\lambda (H9: 
(csubt g x1 c2)).(let H10 \def (eq_ind C x1 (\lambda (c: C).(csubt g c c2)) 
H9 (CHead x0 (Flat f) t0) (drop_gen_refl x1 (CHead x0 (Flat f) t0) H8)) in 
(let H_y \def (clear_flat x0 (CHead d1 (Bind Abst) t) (clear_gen_flat f x0 
(CHead d1 (Bind Abst) t) t0 H6) f t0) in (let H11 \def (csubt_clear_conf g 
(CHead x0 (Flat f) t0) c2 H10 (CHead d1 (Bind Abst) t) H_y) in (ex2_ind C 
(\lambda (e2: C).(csubt g (CHead d1 (Bind Abst) t) e2)) (\lambda (e2: 
C).(clear c2 e2)) (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(getl O c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl O 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u 
t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) (\lambda (x2: 
C).(\lambda (H12: (csubt g (CHead d1 (Bind Abst) t) x2)).(\lambda (H13: 
(clear c2 x2)).(let H14 \def (csubt_gen_abst g d1 x2 t H12) in (or_ind (ex2 C 
(\lambda (e2: C).(eq C x2 (CHead e2 (Bind Abst) t))) (\lambda (e2: C).(csubt 
g d1 e2))) (ex4_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C x2 (CHead e2 
(Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csubt g d1 e2))) 
(\lambda (_: C).(\lambda (v2: T).(ty3 g d1 v2 t))) (\lambda (e2: C).(\lambda 
(v2: T).(ty3 g e2 v2 t)))) (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda 
(d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: 
T).(getl O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) 
(\lambda (H15: (ex2 C (\lambda (e2: C).(eq C x2 (CHead e2 (Bind Abst) t))) 
(\lambda (e2: C).(csubt g d1 e2)))).(ex2_ind C (\lambda (e2: C).(eq C x2 
(CHead e2 (Bind Abst) t))) (\lambda (e2: C).(csubt g d1 e2)) (or (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl O c2 (CHead d2 (Bind 
Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) 
(\lambda (d2: C).(\lambda (u: T).(getl O c2 (CHead d2 (Bind Abbr) u)))) 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda 
(u: T).(ty3 g d2 u t))))) (\lambda (x3: C).(\lambda (H16: (eq C x2 (CHead x3 
(Bind Abst) t))).(\lambda (H17: (csubt g d1 x3)).(let H18 \def (eq_ind C x2 
(\lambda (c: C).(clear c2 c)) H13 (CHead x3 (Bind Abst) t) H16) in (or_introl 
(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl O c2 (CHead 
d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u: T).(getl O c2 (CHead d2 (Bind Abbr) u)))) 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda 
(u: T).(ty3 g d2 u t)))) (ex_intro2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) t))) x3 H17 (getl_intro O 
c2 (CHead x3 (Bind Abst) t) c2 (drop_refl c2) H18))))))) H15)) (\lambda (H15: 
(ex4_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C x2 (CHead e2 (Bind Abbr) 
v2)))) (\lambda (e2: C).(\lambda (_: T).(csubt g d1 e2))) (\lambda (_: 
C).(\lambda (v2: T).(ty3 g d1 v2 t))) (\lambda (e2: C).(\lambda (v2: T).(ty3 
g e2 v2 t))))).(ex4_2_ind C T (\lambda (e2: C).(\lambda (v2: T).(eq C x2 
(CHead e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csubt g d1 
e2))) (\lambda (_: C).(\lambda (v2: T).(ty3 g d1 v2 t))) (\lambda (e2: 
C).(\lambda (v2: T).(ty3 g e2 v2 t))) (or (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) 
(\lambda (x3: C).(\lambda (x4: T).(\lambda (H16: (eq C x2 (CHead x3 (Bind 
Abbr) x4))).(\lambda (H17: (csubt g d1 x3)).(\lambda (H18: (ty3 g d1 x4 
t)).(\lambda (H19: (ty3 g x3 x4 t)).(let H20 \def (eq_ind C x2 (\lambda (c: 
C).(clear c2 c)) H13 (CHead x3 (Bind Abbr) x4) H16) in (or_intror (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl O c2 (CHead d2 (Bind 
Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) 
(\lambda (d2: C).(\lambda (u: T).(getl O c2 (CHead d2 (Bind Abbr) u)))) 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda 
(u: T).(ty3 g d2 u t)))) (ex4_2_intro C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl O c2 (CHead d2 
(Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda 
(d2: C).(\lambda (u: T).(ty3 g d2 u t))) x3 x4 H17 (getl_intro O c2 (CHead x3 
(Bind Abbr) x4) c2 (drop_refl c2) H20) H18 H19))))))))) H15)) H14))))) 
H11)))))))) (\lambda (n0: nat).(\lambda (H8: ((\forall (x1: C).((drop n0 O x1 
(CHead x0 (Flat f) t0)) \to (\forall (c2: C).((csubt g x1 c2) \to (or (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl n0 c2 (CHead d2 
(Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 
d2))) (\lambda (d2: C).(\lambda (u: T).(getl n0 c2 (CHead d2 (Bind Abbr) 
u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t))))))))))).(\lambda (x1: C).(\lambda (H9: 
(drop (S n0) O x1 (CHead x0 (Flat f) t0))).(\lambda (c2: C).(\lambda (H10: 
(csubt g x1 c2)).(let H11 \def (drop_clear x1 (CHead x0 (Flat f) t0) n0 H9) 
in (ex2_3_ind B C T (\lambda (b: B).(\lambda (e: C).(\lambda (v: T).(clear x1 
(CHead e (Bind b) v))))) (\lambda (_: B).(\lambda (e: C).(\lambda (_: 
T).(drop n0 O e (CHead x0 (Flat f) t0))))) (or (ex2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abst) t)))) (ex4_2 
C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u: T).(getl (S n0) c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: 
C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g 
d2 u t))))) (\lambda (x2: B).(\lambda (x3: C).(\lambda (x4: T).(\lambda (H12: 
(clear x1 (CHead x3 (Bind x2) x4))).(\lambda (H13: (drop n0 O x3 (CHead x0 
(Flat f) t0))).(let H14 \def (csubt_clear_conf g x1 c2 H10 (CHead x3 (Bind 
x2) x4) H12) in (ex2_ind C (\lambda (e2: C).(csubt g (CHead x3 (Bind x2) x4) 
e2)) (\lambda (e2: C).(clear c2 e2)) (or (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl (S n0) c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda 
(u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) 
(\lambda (x5: C).(\lambda (H15: (csubt g (CHead x3 (Bind x2) x4) 
x5)).(\lambda (H16: (clear c2 x5)).(let H17 \def (csubt_gen_bind g x2 x3 x5 
x4 H15) in (ex2_3_ind B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: 
T).(eq C x5 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csubt g x3 e2)))) (or (ex2 C (\lambda (d2: C).(csubt g d1 
d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl (S n0) c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda 
(u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) 
(\lambda (x6: B).(\lambda (x7: C).(\lambda (x8: T).(\lambda (H18: (eq C x5 
(CHead x7 (Bind x6) x8))).(\lambda (H19: (csubt g x3 x7)).(let H20 \def 
(eq_ind C x5 (\lambda (c: C).(clear c2 c)) H16 (CHead x7 (Bind x6) x8) H18) 
in (let H21 \def (H8 x3 H13 x7 H19) in (or_ind (ex2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(getl n0 x7 (CHead d2 (Bind Abst) t)))) (ex4_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl n0 x7 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: 
T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))) (or 
(ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl (S n0) c2 
(CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl (S n0) c2 (CHead 
d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) (\lambda (H22: (ex2 C 
(\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: C).(getl n0 x7 (CHead d2 
(Bind Abst) t))))).(ex2_ind C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(getl n0 x7 (CHead d2 (Bind Abst) t))) (or (ex2 C (\lambda (d2: C).(csubt 
g d1 d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abst) t)))) (ex4_2 
C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u: T).(getl (S n0) c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: 
C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g 
d2 u t))))) (\lambda (x9: C).(\lambda (H23: (csubt g d1 x9)).(\lambda (H24: 
(getl n0 x7 (CHead x9 (Bind Abst) t))).(or_introl (ex2 C (\lambda (d2: 
C).(csubt g d1 d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abst) 
t)))) (ex4_2 C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u: T).(getl (S n0) c2 (CHead d2 (Bind Abbr) u)))) (\lambda 
(_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 
g d2 u t)))) (ex_intro2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda (d2: 
C).(getl (S n0) c2 (CHead d2 (Bind Abst) t))) x9 H23 (getl_clear_bind x6 c2 
x7 x8 H20 (CHead x9 (Bind Abst) t) n0 H24)))))) H22)) (\lambda (H22: (ex4_2 C 
T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: 
C).(\lambda (u: T).(getl n0 x7 (CHead d2 (Bind Abbr) u)))) (\lambda (_: 
C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g 
d2 u t))))).(ex4_2_ind C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) 
(\lambda (d2: C).(\lambda (u: T).(getl n0 x7 (CHead d2 (Bind Abbr) u)))) 
(\lambda (_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda 
(u: T).(ty3 g d2 u t))) (or (ex2 C (\lambda (d2: C).(csubt g d1 d2)) (\lambda 
(d2: C).(getl (S n0) c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl 
(S n0) c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda (u: T).(ty3 g 
d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) (\lambda (x9: 
C).(\lambda (x10: T).(\lambda (H23: (csubt g d1 x9)).(\lambda (H24: (getl n0 
x7 (CHead x9 (Bind Abbr) x10))).(\lambda (H25: (ty3 g d1 x10 t)).(\lambda 
(H26: (ty3 g x9 x10 t)).(or_intror (ex2 C (\lambda (d2: C).(csubt g d1 d2)) 
(\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abst) t)))) (ex4_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl (S n0) c2 (CHead d2 (Bind Abbr) u)))) (\lambda (_: C).(\lambda 
(u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t)))) 
(ex4_2_intro C T (\lambda (d2: C).(\lambda (_: T).(csubt g d1 d2))) (\lambda 
(d2: C).(\lambda (u: T).(getl (S n0) c2 (CHead d2 (Bind Abbr) u)))) (\lambda 
(_: C).(\lambda (u: T).(ty3 g d1 u t))) (\lambda (d2: C).(\lambda (u: T).(ty3 
g d2 u t))) x9 x10 H23 (getl_clear_bind x6 c2 x7 x8 H20 (CHead x9 (Bind Abbr) 
x10) n0 H24) H25 H26)))))))) H22)) H21)))))))) H17))))) H14))))))) 
H11)))))))) n) H7))))) k H3 H4))))))) x H1 H2)))) H0))))))).
(* COMMENTS
Initial nodes: 5861
END *)

