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

include "Basic-1/csuba/drop.ma".

include "Basic-1/csuba/clear.ma".

include "Basic-1/getl/clear.ma".

theorem csuba_getl_abbr:
 \forall (g: G).(\forall (c1: C).(\forall (d1: C).(\forall (u: T).(\forall 
(i: nat).((getl i c1 (CHead d1 (Bind Abbr) u)) \to (\forall (c2: C).((csuba g 
c1 c2) \to (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u))) 
(\lambda (d2: C).(csuba g d1 d2))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (d1: C).(\lambda (u: T).(\lambda 
(i: nat).(\lambda (H: (getl i c1 (CHead d1 (Bind Abbr) u))).(let H0 \def 
(getl_gen_all c1 (CHead d1 (Bind Abbr) u) i H) in (ex2_ind C (\lambda (e: 
C).(drop i O c1 e)) (\lambda (e: C).(clear e (CHead d1 (Bind Abbr) u))) 
(\forall (c2: C).((csuba g c1 c2) \to (ex2 C (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))))) (\lambda (x: 
C).(\lambda (H1: (drop i O c1 x)).(\lambda (H2: (clear x (CHead d1 (Bind 
Abbr) u))).(C_ind (\lambda (c: C).((drop i O c1 c) \to ((clear c (CHead d1 
(Bind Abbr) u)) \to (\forall (c2: C).((csuba g c1 c2) \to (ex2 C (\lambda 
(d2: C).(getl i c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 
d2)))))))) (\lambda (n: nat).(\lambda (_: (drop i O c1 (CSort n))).(\lambda 
(H4: (clear (CSort n) (CHead d1 (Bind Abbr) u))).(clear_gen_sort (CHead d1 
(Bind Abbr) u) n H4 (\forall (c2: C).((csuba g c1 c2) \to (ex2 C (\lambda 
(d2: C).(getl i c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 
d2))))))))) (\lambda (x0: C).(\lambda (_: (((drop i O c1 x0) \to ((clear x0 
(CHead d1 (Bind Abbr) u)) \to (\forall (c2: C).((csuba g c1 c2) \to (ex2 C 
(\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: 
C).(csuba g d1 d2))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (H3: 
(drop i O c1 (CHead x0 k t))).(\lambda (H4: (clear (CHead x0 k t) (CHead d1 
(Bind Abbr) u))).(K_ind (\lambda (k0: K).((drop i O c1 (CHead x0 k0 t)) \to 
((clear (CHead x0 k0 t) (CHead d1 (Bind Abbr) u)) \to (\forall (c2: 
C).((csuba g c1 c2) \to (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind 
Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))))))) (\lambda (b: B).(\lambda 
(H5: (drop i O c1 (CHead x0 (Bind b) t))).(\lambda (H6: (clear (CHead x0 
(Bind b) t) (CHead d1 (Bind Abbr) u))).(let H7 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d1 | 
(CHead c _ _) \Rightarrow c])) (CHead d1 (Bind Abbr) u) (CHead x0 (Bind b) t) 
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
(c2: C).(\lambda (H12: (csuba g c1 c2)).(let H13 \def (eq_ind_r T t (\lambda 
(t0: T).(drop i O c1 (CHead x0 (Bind b) t0))) H5 u H9) in (let H14 \def 
(eq_ind_r B b (\lambda (b0: B).(drop i O c1 (CHead x0 (Bind b0) u))) H13 Abbr 
H10) in (let H15 \def (eq_ind_r C x0 (\lambda (c: C).(drop i O c1 (CHead c 
(Bind Abbr) u))) H14 d1 H11) in (let H16 \def (csuba_drop_abbr i c1 d1 u H15 
g c2 H12) in (ex2_ind C (\lambda (d2: C).(drop i O c2 (CHead d2 (Bind Abbr) 
u))) (\lambda (d2: C).(csuba g d1 d2)) (ex2 C (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))) (\lambda (x1: 
C).(\lambda (H17: (drop i O c2 (CHead x1 (Bind Abbr) u))).(\lambda (H18: 
(csuba g d1 x1)).(ex_intro2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind 
Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)) x1 (getl_intro i c2 (CHead x1 
(Bind Abbr) u) (CHead x1 (Bind Abbr) u) H17 (clear_bind Abbr x1 u)) H18)))) 
H16)))))))))) H8)) H7))))) (\lambda (f: F).(\lambda (H5: (drop i O c1 (CHead 
x0 (Flat f) t))).(\lambda (H6: (clear (CHead x0 (Flat f) t) (CHead d1 (Bind 
Abbr) u))).(let H7 \def H5 in (unintro C c1 (\lambda (c: C).((drop i O c 
(CHead x0 (Flat f) t)) \to (\forall (c2: C).((csuba g c c2) \to (ex2 C 
(\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: 
C).(csuba g d1 d2))))))) (nat_ind (\lambda (n: nat).(\forall (x1: C).((drop n 
O x1 (CHead x0 (Flat f) t)) \to (\forall (c2: C).((csuba g x1 c2) \to (ex2 C 
(\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: 
C).(csuba g d1 d2)))))))) (\lambda (x1: C).(\lambda (H8: (drop O O x1 (CHead 
x0 (Flat f) t))).(\lambda (c2: C).(\lambda (H9: (csuba g x1 c2)).(let H10 
\def (eq_ind C x1 (\lambda (c: C).(csuba g c c2)) H9 (CHead x0 (Flat f) t) 
(drop_gen_refl x1 (CHead x0 (Flat f) t) H8)) in (let H_y \def (clear_flat x0 
(CHead d1 (Bind Abbr) u) (clear_gen_flat f x0 (CHead d1 (Bind Abbr) u) t H6) 
f t) in (let H11 \def (csuba_clear_conf g (CHead x0 (Flat f) t) c2 H10 (CHead 
d1 (Bind Abbr) u) H_y) in (ex2_ind C (\lambda (e2: C).(csuba g (CHead d1 
(Bind Abbr) u) e2)) (\lambda (e2: C).(clear c2 e2)) (ex2 C (\lambda (d2: 
C).(getl O c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))) 
(\lambda (x2: C).(\lambda (H12: (csuba g (CHead d1 (Bind Abbr) u) 
x2)).(\lambda (H13: (clear c2 x2)).(let H_x \def (csuba_gen_abbr g d1 x2 u 
H12) in (let H14 \def H_x in (ex2_ind C (\lambda (d2: C).(eq C x2 (CHead d2 
(Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)) (ex2 C (\lambda (d2: 
C).(getl O c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))) 
(\lambda (x3: C).(\lambda (H15: (eq C x2 (CHead x3 (Bind Abbr) u))).(\lambda 
(H16: (csuba g d1 x3)).(let H17 \def (eq_ind C x2 (\lambda (c: C).(clear c2 
c)) H13 (CHead x3 (Bind Abbr) u) H15) in (ex_intro2 C (\lambda (d2: C).(getl 
O c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)) x3 
(getl_intro O c2 (CHead x3 (Bind Abbr) u) c2 (drop_refl c2) H17) H16))))) 
H14)))))) H11)))))))) (\lambda (n: nat).(\lambda (H8: ((\forall (x1: 
C).((drop n O x1 (CHead x0 (Flat f) t)) \to (\forall (c2: C).((csuba g x1 c2) 
\to (ex2 C (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) u))) (\lambda 
(d2: C).(csuba g d1 d2))))))))).(\lambda (x1: C).(\lambda (H9: (drop (S n) O 
x1 (CHead x0 (Flat f) t))).(\lambda (c2: C).(\lambda (H10: (csuba g x1 
c2)).(let H11 \def (drop_clear x1 (CHead x0 (Flat f) t) n H9) in (ex2_3_ind B 
C T (\lambda (b: B).(\lambda (e: C).(\lambda (v: T).(clear x1 (CHead e (Bind 
b) v))))) (\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop n O e (CHead 
x0 (Flat f) t))))) (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind 
Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))) (\lambda (x2: B).(\lambda (x3: 
C).(\lambda (x4: T).(\lambda (H12: (clear x1 (CHead x3 (Bind x2) 
x4))).(\lambda (H13: (drop n O x3 (CHead x0 (Flat f) t))).(let H14 \def 
(csuba_clear_conf g x1 c2 H10 (CHead x3 (Bind x2) x4) H12) in (ex2_ind C 
(\lambda (e2: C).(csuba g (CHead x3 (Bind x2) x4) e2)) (\lambda (e2: 
C).(clear c2 e2)) (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind 
Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))) (\lambda (x5: C).(\lambda (H15: 
(csuba g (CHead x3 (Bind x2) x4) x5)).(\lambda (H16: (clear c2 x5)).(let H_x 
\def (csuba_gen_bind g x2 x3 x5 x4 H15) in (let H17 \def H_x in (ex2_3_ind B 
C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C x5 (CHead e2 
(Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g 
x3 e2)))) (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abbr) u))) 
(\lambda (d2: C).(csuba g d1 d2))) (\lambda (x6: B).(\lambda (x7: C).(\lambda 
(x8: T).(\lambda (H18: (eq C x5 (CHead x7 (Bind x6) x8))).(\lambda (H19: 
(csuba g x3 x7)).(let H20 \def (eq_ind C x5 (\lambda (c: C).(clear c2 c)) H16 
(CHead x7 (Bind x6) x8) H18) in (let H21 \def (H8 x3 H13 x7 H19) in (ex2_ind 
C (\lambda (d2: C).(getl n x7 (CHead d2 (Bind Abbr) u))) (\lambda (d2: 
C).(csuba g d1 d2)) (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind 
Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))) (\lambda (x9: C).(\lambda (H22: 
(getl n x7 (CHead x9 (Bind Abbr) u))).(\lambda (H23: (csuba g d1 
x9)).(ex_intro2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abbr) u))) 
(\lambda (d2: C).(csuba g d1 d2)) x9 (getl_clear_bind x6 c2 x7 x8 H20 (CHead 
x9 (Bind Abbr) u) n H22) H23)))) H21)))))))) H17)))))) H14))))))) H11)))))))) 
i) H7))))) k H3 H4))))))) x H1 H2)))) H0))))))).
(* COMMENTS
Initial nodes: 2319
END *)

theorem csuba_getl_abst:
 \forall (g: G).(\forall (c1: C).(\forall (d1: C).(\forall (u1: T).(\forall 
(i: nat).((getl i c1 (CHead d1 (Bind Abst) u1)) \to (\forall (c2: C).((csuba 
g c1 c2) \to (or (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) 
u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (d1: C).(\lambda (u1: T).(\lambda 
(i: nat).(\lambda (H: (getl i c1 (CHead d1 (Bind Abst) u1))).(let H0 \def 
(getl_gen_all c1 (CHead d1 (Bind Abst) u1) i H) in (ex2_ind C (\lambda (e: 
C).(drop i O c1 e)) (\lambda (e: C).(clear e (CHead d1 (Bind Abst) u1))) 
(\forall (c2: C).((csuba g c1 c2) \to (or (ex2 C (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind 
Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 
d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc 
g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))))) (\lambda (x: C).(\lambda (H1: (drop i O c1 x)).(\lambda (H2: (clear 
x (CHead d1 (Bind Abst) u1))).(C_ind (\lambda (c: C).((drop i O c1 c) \to 
((clear c (CHead d1 (Bind Abst) u1)) \to (\forall (c2: C).((csuba g c1 c2) 
\to (or (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abbr) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))))))))) (\lambda 
(n: nat).(\lambda (_: (drop i O c1 (CSort n))).(\lambda (H4: (clear (CSort n) 
(CHead d1 (Bind Abst) u1))).(clear_gen_sort (CHead d1 (Bind Abst) u1) n H4 
(\forall (c2: C).((csuba g c1 c2) \to (or (ex2 C (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind 
Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 
d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc 
g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))))))))) (\lambda (x0: C).(\lambda (_: (((drop i O c1 x0) \to ((clear x0 
(CHead d1 (Bind Abst) u1)) \to (\forall (c2: C).((csuba g c1 c2) \to (or (ex2 
C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(getl i c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))))))))))).(\lambda (k: K).(\lambda 
(t: T).(\lambda (H3: (drop i O c1 (CHead x0 k t))).(\lambda (H4: (clear 
(CHead x0 k t) (CHead d1 (Bind Abst) u1))).(K_ind (\lambda (k0: K).((drop i O 
c1 (CHead x0 k0 t)) \to ((clear (CHead x0 k0 t) (CHead d1 (Bind Abst) u1)) 
\to (\forall (c2: C).((csuba g c1 c2) \to (or (ex2 C (\lambda (d2: C).(getl i 
c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
(asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 
u2 a))))))))))) (\lambda (b: B).(\lambda (H5: (drop i O c1 (CHead x0 (Bind b) 
t))).(\lambda (H6: (clear (CHead x0 (Bind b) t) (CHead d1 (Bind Abst) 
u1))).(let H7 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow d1 | (CHead c _ _) \Rightarrow c])) 
(CHead d1 (Bind Abst) u1) (CHead x0 (Bind b) t) (clear_gen_bind b x0 (CHead 
d1 (Bind Abst) u1) t H6)) in ((let H8 \def (f_equal C B (\lambda (e: 
C).(match e in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow Abst | 
(CHead _ k0 _) \Rightarrow (match k0 in K return (\lambda (_: K).B) with 
[(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Abst])])) (CHead d1 (Bind 
Abst) u1) (CHead x0 (Bind b) t) (clear_gen_bind b x0 (CHead d1 (Bind Abst) 
u1) t H6)) in ((let H9 \def (f_equal C T (\lambda (e: C).(match e in C return 
(\lambda (_: C).T) with [(CSort _) \Rightarrow u1 | (CHead _ _ t0) 
\Rightarrow t0])) (CHead d1 (Bind Abst) u1) (CHead x0 (Bind b) t) 
(clear_gen_bind b x0 (CHead d1 (Bind Abst) u1) t H6)) in (\lambda (H10: (eq B 
Abst b)).(\lambda (H11: (eq C d1 x0)).(\lambda (c2: C).(\lambda (H12: (csuba 
g c1 c2)).(let H13 \def (eq_ind_r T t (\lambda (t0: T).(drop i O c1 (CHead x0 
(Bind b) t0))) H5 u1 H9) in (let H14 \def (eq_ind_r B b (\lambda (b0: 
B).(drop i O c1 (CHead x0 (Bind b0) u1))) H13 Abst H10) in (let H15 \def 
(eq_ind_r C x0 (\lambda (c: C).(drop i O c1 (CHead c (Bind Abst) u1))) H14 d1 
H11) in (let H16 \def (csuba_drop_abst i c1 d1 u1 H15 g c2 H12) in (or_ind 
(ex2 C (\lambda (d2: C).(drop i O c2 (CHead d2 (Bind Abst) u1))) (\lambda 
(d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop i O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (or (ex2 C 
(\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(getl i c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (H17: (ex2 C (\lambda 
(d2: C).(drop i O c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2)))).(ex2_ind C (\lambda (d2: C).(drop i O c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2)) (or (ex2 C (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind 
Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 
d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc 
g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))) (\lambda (x1: C).(\lambda (H18: (drop i O c2 (CHead x1 (Bind Abst) 
u1))).(\lambda (H19: (csuba g d1 x1)).(or_introl (ex2 C (\lambda (d2: 
C).(getl i c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a))))) (ex_intro2 C (\lambda (d2: C).(getl i c2 (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2)) x1 (getl_intro i c2 
(CHead x1 (Bind Abst) u1) (CHead x1 (Bind Abst) u1) H18 (clear_bind Abst x1 
u1)) H19))))) H17)) (\lambda (H17: (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop i O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))).(ex4_3_ind C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop i O c2 (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
(asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 
u2 a)))) (or (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abbr) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (x1: 
C).(\lambda (x2: T).(\lambda (x3: A).(\lambda (H18: (drop i O c2 (CHead x1 
(Bind Abbr) x2))).(\lambda (H19: (csuba g d1 x1)).(\lambda (H20: (arity g d1 
u1 (asucc g x3))).(\lambda (H21: (arity g x1 x2 x3)).(or_intror (ex2 C 
(\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(getl i c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (ex4_3_intro C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))) 
x1 x2 x3 (getl_intro i c2 (CHead x1 (Bind Abbr) x2) (CHead x1 (Bind Abbr) x2) 
H18 (clear_bind Abbr x1 x2)) H19 H20 H21))))))))) H17)) H16)))))))))) H8)) 
H7))))) (\lambda (f: F).(\lambda (H5: (drop i O c1 (CHead x0 (Flat f) 
t))).(\lambda (H6: (clear (CHead x0 (Flat f) t) (CHead d1 (Bind Abst) 
u1))).(let H7 \def H5 in (unintro C c1 (\lambda (c: C).((drop i O c (CHead x0 
(Flat f) t)) \to (\forall (c2: C).((csuba g c c2) \to (or (ex2 C (\lambda 
(d2: C).(getl i c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i 
c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: 
A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(a: A).(arity g d2 u2 a)))))))))) (nat_ind (\lambda (n: nat).(\forall (x1: 
C).((drop n O x1 (CHead x0 (Flat f) t)) \to (\forall (c2: C).((csuba g x1 c2) 
\to (or (ex2 C (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl n c2 (CHead d2 (Bind Abbr) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))))))))) (\lambda 
(x1: C).(\lambda (H8: (drop O O x1 (CHead x0 (Flat f) t))).(\lambda (c2: 
C).(\lambda (H9: (csuba g x1 c2)).(let H10 \def (eq_ind C x1 (\lambda (c: 
C).(csuba g c c2)) H9 (CHead x0 (Flat f) t) (drop_gen_refl x1 (CHead x0 (Flat 
f) t) H8)) in (let H_y \def (clear_flat x0 (CHead d1 (Bind Abst) u1) 
(clear_gen_flat f x0 (CHead d1 (Bind Abst) u1) t H6) f t) in (let H11 \def 
(csuba_clear_conf g (CHead x0 (Flat f) t) c2 H10 (CHead d1 (Bind Abst) u1) 
H_y) in (ex2_ind C (\lambda (e2: C).(csuba g (CHead d1 (Bind Abst) u1) e2)) 
(\lambda (e2: C).(clear c2 e2)) (or (ex2 C (\lambda (d2: C).(getl O c2 (CHead 
d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O c2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))) (\lambda (x2: C).(\lambda (H12: (csuba g (CHead d1 (Bind Abst) u1) 
x2)).(\lambda (H13: (clear c2 x2)).(let H_x \def (csuba_gen_abst g d1 x2 u1 
H12) in (let H14 \def H_x in (or_ind (ex2 C (\lambda (d2: C).(eq C x2 (CHead 
d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C x2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))) (or (ex2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda 
(H15: (ex2 C (\lambda (d2: C).(eq C x2 (CHead d2 (Bind Abst) u1))) (\lambda 
(d2: C).(csuba g d1 d2)))).(ex2_ind C (\lambda (d2: C).(eq C x2 (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2)) (or (ex2 C (\lambda (d2: 
C).(getl O c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O c2 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a)))))) (\lambda (x3: C).(\lambda (H16: (eq C x2 (CHead x3 
(Bind Abst) u1))).(\lambda (H17: (csuba g d1 x3)).(let H18 \def (eq_ind C x2 
(\lambda (c: C).(clear c2 c)) H13 (CHead x3 (Bind Abst) u1) H16) in 
(or_introl (ex2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (ex_intro2 C 
(\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2)) x3 (getl_intro O c2 (CHead x3 (Bind Abst) u1) c2 
(drop_refl c2) H18) H17)))))) H15)) (\lambda (H15: (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(eq C x2 (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(eq C x2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))) (or (ex2 C (\lambda (d2: 
C).(getl O c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O c2 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a)))))) (\lambda (x3: C).(\lambda (x4: T).(\lambda (x5: 
A).(\lambda (H16: (eq C x2 (CHead x3 (Bind Abbr) x4))).(\lambda (H17: (csuba 
g d1 x3)).(\lambda (H18: (arity g d1 u1 (asucc g x5))).(\lambda (H19: (arity 
g x3 x4 x5)).(let H20 \def (eq_ind C x2 (\lambda (c: C).(clear c2 c)) H13 
(CHead x3 (Bind Abbr) x4) H16) in (or_intror (ex2 C (\lambda (d2: C).(getl O 
c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O c2 (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
(asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 
u2 a))))) (ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(getl O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))) x3 x4 x5 (getl_intro O c2 (CHead 
x3 (Bind Abbr) x4) c2 (drop_refl c2) H20) H17 H18 H19)))))))))) H15)) 
H14)))))) H11)))))))) (\lambda (n: nat).(\lambda (H8: ((\forall (x1: 
C).((drop n O x1 (CHead x0 (Flat f) t)) \to (\forall (c2: C).((csuba g x1 c2) 
\to (or (ex2 C (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl n c2 (CHead d2 (Bind Abbr) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))))))))).(\lambda (x1: C).(\lambda (H9: (drop (S n) O x1 (CHead x0 (Flat 
f) t))).(\lambda (c2: C).(\lambda (H10: (csuba g x1 c2)).(let H11 \def 
(drop_clear x1 (CHead x0 (Flat f) t) n H9) in (ex2_3_ind B C T (\lambda (b: 
B).(\lambda (e: C).(\lambda (v: T).(clear x1 (CHead e (Bind b) v))))) 
(\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop n O e (CHead x0 (Flat 
f) t))))) (or (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abst) 
u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))) (\lambda (x2: B).(\lambda (x3: C).(\lambda (x4: T).(\lambda (H12: 
(clear x1 (CHead x3 (Bind x2) x4))).(\lambda (H13: (drop n O x3 (CHead x0 
(Flat f) t))).(let H14 \def (csuba_clear_conf g x1 c2 H10 (CHead x3 (Bind x2) 
x4) H12) in (ex2_ind C (\lambda (e2: C).(csuba g (CHead x3 (Bind x2) x4) e2)) 
(\lambda (e2: C).(clear c2 e2)) (or (ex2 C (\lambda (d2: C).(getl (S n) c2 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
(asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 
u2 a)))))) (\lambda (x5: C).(\lambda (H15: (csuba g (CHead x3 (Bind x2) x4) 
x5)).(\lambda (H16: (clear c2 x5)).(let H_x \def (csuba_gen_bind g x2 x3 x5 
x4 H15) in (let H17 \def H_x in (ex2_3_ind B C T (\lambda (b2: B).(\lambda 
(e2: C).(\lambda (v2: T).(eq C x5 (CHead e2 (Bind b2) v2))))) (\lambda (_: 
B).(\lambda (e2: C).(\lambda (_: T).(csuba g x3 e2)))) (or (ex2 C (\lambda 
(d2: C).(getl (S n) c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g 
d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl 
(S n) c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (x6: B).(\lambda (x7: 
C).(\lambda (x8: T).(\lambda (H18: (eq C x5 (CHead x7 (Bind x6) 
x8))).(\lambda (H19: (csuba g x3 x7)).(let H20 \def (eq_ind C x5 (\lambda (c: 
C).(clear c2 c)) H16 (CHead x7 (Bind x6) x8) H18) in (let H21 \def (H8 x3 H13 
x7 H19) in (or_ind (ex2 C (\lambda (d2: C).(getl n x7 (CHead d2 (Bind Abst) 
u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl n x7 (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (or 
(ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abst) u1))) (\lambda 
(d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda 
(H22: (ex2 C (\lambda (d2: C).(getl n x7 (CHead d2 (Bind Abst) u1))) (\lambda 
(d2: C).(csuba g d1 d2)))).(ex2_ind C (\lambda (d2: C).(getl n x7 (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2)) (or (ex2 C (\lambda (d2: 
C).(getl (S n) c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S 
n) c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: 
A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(a: A).(arity g d2 u2 a)))))) (\lambda (x9: C).(\lambda (H23: (getl n x7 
(CHead x9 (Bind Abst) u1))).(\lambda (H24: (csuba g d1 x9)).(or_introl (ex2 C 
(\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(getl (S n) c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda 
(_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (ex_intro2 C (\lambda (d2: 
C).(getl (S n) c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2)) x9 (getl_clear_bind x6 c2 x7 x8 H20 (CHead x9 (Bind Abst) u1) n H23) 
H24))))) H22)) (\lambda (H22: (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(getl n x7 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))).(ex4_3_ind C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl n x7 (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
(asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 
u2 a)))) (or (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abst) 
u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))) (\lambda (x9: C).(\lambda (x10: T).(\lambda (x11: A).(\lambda (H23: 
(getl n x7 (CHead x9 (Bind Abbr) x10))).(\lambda (H24: (csuba g d1 
x9)).(\lambda (H25: (arity g d1 u1 (asucc g x11))).(\lambda (H26: (arity g x9 
x10 x11)).(or_intror (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind 
Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))) (ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(getl (S n) c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))) x9 x10 x11 (getl_clear_bind x6 
c2 x7 x8 H20 (CHead x9 (Bind Abbr) x10) n H23) H24 H25 H26))))))))) H22)) 
H21)))))))) H17)))))) H14))))))) H11)))))))) i) H7))))) k H3 H4))))))) x H1 
H2)))) H0))))))).
(* COMMENTS
Initial nodes: 6437
END *)

theorem csuba_getl_abst_rev:
 \forall (g: G).(\forall (c1: C).(\forall (d1: C).(\forall (u: T).(\forall 
(i: nat).((getl i c1 (CHead d1 (Bind Abst) u)) \to (\forall (c2: C).((csuba g 
c2 c1) \to (or (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(getl i c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (d1: C).(\lambda (u: T).(\lambda 
(i: nat).(\lambda (H: (getl i c1 (CHead d1 (Bind Abst) u))).(let H0 \def 
(getl_gen_all c1 (CHead d1 (Bind Abst) u) i H) in (ex2_ind C (\lambda (e: 
C).(drop i O c1 e)) (\lambda (e: C).(clear e (CHead d1 (Bind Abst) u))) 
(\forall (c2: C).((csuba g c2 c1) \to (or (ex2 C (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))))) (\lambda (x: 
C).(\lambda (H1: (drop i O c1 x)).(\lambda (H2: (clear x (CHead d1 (Bind 
Abst) u))).(C_ind (\lambda (c: C).((drop i O c1 c) \to ((clear c (CHead d1 
(Bind Abst) u)) \to (\forall (c2: C).((csuba g c2 c1) \to (or (ex2 C (\lambda 
(d2: C).(getl i c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 
d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))))))) 
(\lambda (n: nat).(\lambda (_: (drop i O c1 (CSort n))).(\lambda (H4: (clear 
(CSort n) (CHead d1 (Bind Abst) u))).(clear_gen_sort (CHead d1 (Bind Abst) u) 
n H4 (\forall (c2: C).((csuba g c2 c1) \to (or (ex2 C (\lambda (d2: C).(getl 
i c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))))))))) (\lambda (x0: 
C).(\lambda (_: (((drop i O c1 x0) \to ((clear x0 (CHead d1 (Bind Abst) u)) 
\to (\forall (c2: C).((csuba g c2 c1) \to (or (ex2 C (\lambda (d2: C).(getl i 
c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))))))))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (H3: (drop i O c1 (CHead x0 k t))).(\lambda (H4: 
(clear (CHead x0 k t) (CHead d1 (Bind Abst) u))).(K_ind (\lambda (k0: 
K).((drop i O c1 (CHead x0 k0 t)) \to ((clear (CHead x0 k0 t) (CHead d1 (Bind 
Abst) u)) \to (\forall (c2: C).((csuba g c2 c1) \to (or (ex2 C (\lambda (d2: 
C).(getl i c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))))))) (\lambda (b: 
B).(\lambda (H5: (drop i O c1 (CHead x0 (Bind b) t))).(\lambda (H6: (clear 
(CHead x0 (Bind b) t) (CHead d1 (Bind Abst) u))).(let H7 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow d1 | (CHead c _ _) \Rightarrow c])) (CHead d1 (Bind Abst) u) 
(CHead x0 (Bind b) t) (clear_gen_bind b x0 (CHead d1 (Bind Abst) u) t H6)) in 
((let H8 \def (f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: 
C).B) with [(CSort _) \Rightarrow Abst | (CHead _ k0 _) \Rightarrow (match k0 
in K return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) 
\Rightarrow Abst])])) (CHead d1 (Bind Abst) u) (CHead x0 (Bind b) t) 
(clear_gen_bind b x0 (CHead d1 (Bind Abst) u) t H6)) in ((let H9 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) (CHead d1 (Bind 
Abst) u) (CHead x0 (Bind b) t) (clear_gen_bind b x0 (CHead d1 (Bind Abst) u) 
t H6)) in (\lambda (H10: (eq B Abst b)).(\lambda (H11: (eq C d1 x0)).(\lambda 
(c2: C).(\lambda (H12: (csuba g c2 c1)).(let H13 \def (eq_ind_r T t (\lambda 
(t0: T).(drop i O c1 (CHead x0 (Bind b) t0))) H5 u H9) in (let H14 \def 
(eq_ind_r B b (\lambda (b0: B).(drop i O c1 (CHead x0 (Bind b0) u))) H13 Abst 
H10) in (let H15 \def (eq_ind_r C x0 (\lambda (c: C).(drop i O c1 (CHead c 
(Bind Abst) u))) H14 d1 H11) in (let H16 \def (csuba_drop_abst_rev i c1 d1 u 
H15 g c2 H12) in (or_ind (ex2 C (\lambda (d2: C).(drop i O c2 (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(drop i O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) (or (ex2 C (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (H17: (ex2 C 
(\lambda (d2: C).(drop i O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: C).(drop i O c2 (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) (or (ex2 C (\lambda (d2: 
C).(getl i c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x1: 
C).(\lambda (H18: (drop i O c2 (CHead x1 (Bind Abst) u))).(\lambda (H19: 
(csuba g x1 d1)).(or_introl (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) (ex_intro2 C (\lambda (d2: C).(getl i 
c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) x1 
(getl_intro i c2 (CHead x1 (Bind Abst) u) (CHead x1 (Bind Abst) u) H18 
(clear_bind Abst x1 u)) H19))))) H17)) (\lambda (H17: (ex2_2 C T (\lambda 
(d2: C).(\lambda (u2: T).(drop i O c2 (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1))))).(ex2_2_ind C T (\lambda (d2: 
C).(\lambda (u2: T).(drop i O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1))) (or (ex2 C (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x1: 
C).(\lambda (x2: T).(\lambda (H18: (drop i O c2 (CHead x1 (Bind Void) 
x2))).(\lambda (H19: (csuba g x1 d1)).(or_intror (ex2 C (\lambda (d2: 
C).(getl i c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex2_2_intro C T 
(\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x1 x2 (getl_intro i c2 
(CHead x1 (Bind Void) x2) (CHead x1 (Bind Void) x2) H18 (clear_bind Void x1 
x2)) H19)))))) H17)) H16)))))))))) H8)) H7))))) (\lambda (f: F).(\lambda (H5: 
(drop i O c1 (CHead x0 (Flat f) t))).(\lambda (H6: (clear (CHead x0 (Flat f) 
t) (CHead d1 (Bind Abst) u))).(let H7 \def H5 in (unintro C c1 (\lambda (c: 
C).((drop i O c (CHead x0 (Flat f) t)) \to (\forall (c2: C).((csuba g c2 c) 
\to (or (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(getl i c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))))))) (nat_ind (\lambda (n: nat).(\forall (x1: C).((drop 
n O x1 (CHead x0 (Flat f) t)) \to (\forall (c2: C).((csuba g c2 x1) \to (or 
(ex2 C (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl n c2 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))))))))) (\lambda (x1: C).(\lambda (H8: (drop O O x1 (CHead x0 (Flat f) 
t))).(\lambda (c2: C).(\lambda (H9: (csuba g c2 x1)).(let H10 \def (eq_ind C 
x1 (\lambda (c: C).(csuba g c2 c)) H9 (CHead x0 (Flat f) t) (drop_gen_refl x1 
(CHead x0 (Flat f) t) H8)) in (let H_y \def (clear_flat x0 (CHead d1 (Bind 
Abst) u) (clear_gen_flat f x0 (CHead d1 (Bind Abst) u) t H6) f t) in (let H11 
\def (csuba_clear_trans g (CHead x0 (Flat f) t) c2 H10 (CHead d1 (Bind Abst) 
u) H_y) in (ex2_ind C (\lambda (e2: C).(csuba g e2 (CHead d1 (Bind Abst) u))) 
(\lambda (e2: C).(clear c2 e2)) (or (ex2 C (\lambda (d2: C).(getl O c2 (CHead 
d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda 
(d2: C).(\lambda (u2: T).(getl O c2 (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x2: C).(\lambda (H12: 
(csuba g x2 (CHead d1 (Bind Abst) u))).(\lambda (H13: (clear c2 x2)).(let H_x 
\def (csuba_gen_abst_rev g d1 x2 u H12) in (let H14 \def H_x in (or_ind (ex2 
C (\lambda (d2: C).(eq C x2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(eq C x2 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))) (or (ex2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(getl O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (H15: (ex2 C (\lambda (d2: C).(eq C x2 (CHead 
d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind C (\lambda 
(d2: C).(eq C x2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) 
(or (ex2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) u))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl 
O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g 
d2 d1))))) (\lambda (x3: C).(\lambda (H16: (eq C x2 (CHead x3 (Bind Abst) 
u))).(\lambda (H17: (csuba g x3 d1)).(let H18 \def (eq_ind C x2 (\lambda (c: 
C).(clear c2 c)) H13 (CHead x3 (Bind Abst) u) H16) in (or_introl (ex2 C 
(\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl O c2 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))) (ex_intro2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1)) x3 (getl_intro O c2 (CHead x3 (Bind Abst) 
u) c2 (drop_refl c2) H18) H17)))))) H15)) (\lambda (H15: (ex2_2 C T (\lambda 
(d2: C).(\lambda (u2: T).(eq C x2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1))))).(ex2_2_ind C T (\lambda (d2: 
C).(\lambda (u2: T).(eq C x2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1))) (or (ex2 C (\lambda (d2: C).(getl O c2 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(getl O c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x3: 
C).(\lambda (x4: T).(\lambda (H16: (eq C x2 (CHead x3 (Bind Void) 
x4))).(\lambda (H17: (csuba g x3 d1)).(let H18 \def (eq_ind C x2 (\lambda (c: 
C).(clear c2 c)) H13 (CHead x3 (Bind Void) x4) H16) in (or_intror (ex2 C 
(\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl O c2 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))) (ex2_2_intro C T (\lambda (d2: C).(\lambda (u2: T).(getl O c2 (CHead 
d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x3 
x4 (getl_intro O c2 (CHead x3 (Bind Void) x4) c2 (drop_refl c2) H18) 
H17))))))) H15)) H14)))))) H11)))))))) (\lambda (n: nat).(\lambda (H8: 
((\forall (x1: C).((drop n O x1 (CHead x0 (Flat f) t)) \to (\forall (c2: 
C).((csuba g c2 x1) \to (or (ex2 C (\lambda (d2: C).(getl n c2 (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(getl n c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1))))))))))).(\lambda (x1: C).(\lambda (H9: 
(drop (S n) O x1 (CHead x0 (Flat f) t))).(\lambda (c2: C).(\lambda (H10: 
(csuba g c2 x1)).(let H11 \def (drop_clear x1 (CHead x0 (Flat f) t) n H9) in 
(ex2_3_ind B C T (\lambda (b: B).(\lambda (e: C).(\lambda (v: T).(clear x1 
(CHead e (Bind b) v))))) (\lambda (_: B).(\lambda (e: C).(\lambda (_: 
T).(drop n O e (CHead x0 (Flat f) t))))) (or (ex2 C (\lambda (d2: C).(getl (S 
n) c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C 
T (\lambda (d2: C).(\lambda (u2: T).(getl (S n) c2 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x2: 
B).(\lambda (x3: C).(\lambda (x4: T).(\lambda (H12: (clear x1 (CHead x3 (Bind 
x2) x4))).(\lambda (H13: (drop n O x3 (CHead x0 (Flat f) t))).(let H14 \def 
(csuba_clear_trans g x1 c2 H10 (CHead x3 (Bind x2) x4) H12) in (ex2_ind C 
(\lambda (e2: C).(csuba g e2 (CHead x3 (Bind x2) x4))) (\lambda (e2: 
C).(clear c2 e2)) (or (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(getl (S n) c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x5: C).(\lambda (H15: (csuba 
g x5 (CHead x3 (Bind x2) x4))).(\lambda (H16: (clear c2 x5)).(let H_x \def 
(csuba_gen_bind_rev g x2 x3 x5 x4 H15) in (let H17 \def H_x in (ex2_3_ind B C 
T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: T).(eq C x5 (CHead e2 (Bind 
b2) v2))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csuba g e2 
x3)))) (or (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(getl (S n) c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (x6: B).(\lambda (x7: C).(\lambda (x8: 
T).(\lambda (H18: (eq C x5 (CHead x7 (Bind x6) x8))).(\lambda (H19: (csuba g 
x7 x3)).(let H20 \def (eq_ind C x5 (\lambda (c: C).(clear c2 c)) H16 (CHead 
x7 (Bind x6) x8) H18) in (let H21 \def (H8 x3 H13 x7 H19) in (or_ind (ex2 C 
(\lambda (d2: C).(getl n x7 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl n x7 
(CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1)))) (or (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abst) u))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(getl (S n) c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (H22: (ex2 C (\lambda (d2: C).(getl n x7 
(CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind C 
(\lambda (d2: C).(getl n x7 (CHead d2 (Bind Abst) u))) (\lambda (d2: 
C).(csuba g d2 d1)) (or (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 
(Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(getl (S n) c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x9: C).(\lambda (H23: (getl 
n x7 (CHead x9 (Bind Abst) u))).(\lambda (H24: (csuba g x9 d1)).(or_introl 
(ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abst) u))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl 
(S n) c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba 
g d2 d1)))) (ex_intro2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind 
Abst) u))) (\lambda (d2: C).(csuba g d2 d1)) x9 (getl_clear_bind x6 c2 x7 x8 
H20 (CHead x9 (Bind Abst) u) n H23) H24))))) H22)) (\lambda (H22: (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(getl n x7 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))).(ex2_2_ind C T (\lambda 
(d2: C).(\lambda (u2: T).(getl n x7 (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1))) (or (ex2 C (\lambda (d2: C).(getl 
(S n) c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 d1))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(getl (S n) c2 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x9: 
C).(\lambda (x10: T).(\lambda (H23: (getl n x7 (CHead x9 (Bind Void) 
x10))).(\lambda (H24: (csuba g x9 d1)).(or_intror (ex2 C (\lambda (d2: 
C).(getl (S n) c2 (CHead d2 (Bind Abst) u))) (\lambda (d2: C).(csuba g d2 
d1))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl (S n) c2 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) 
(ex2_2_intro C T (\lambda (d2: C).(\lambda (u2: T).(getl (S n) c2 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x9 x10 
(getl_clear_bind x6 c2 x7 x8 H20 (CHead x9 (Bind Void) x10) n H23) H24)))))) 
H22)) H21)))))))) H17)))))) H14))))))) H11)))))))) i) H7))))) k H3 H4))))))) 
x H1 H2)))) H0))))))).
(* COMMENTS
Initial nodes: 4703
END *)

theorem csuba_getl_abbr_rev:
 \forall (g: G).(\forall (c1: C).(\forall (d1: C).(\forall (u1: T).(\forall 
(i: nat).((getl i c1 (CHead d1 (Bind Abbr) u1)) \to (\forall (c2: C).((csuba 
g c2 c1) \to (or3 (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (d1: C).(\lambda (u1: T).(\lambda 
(i: nat).(\lambda (H: (getl i c1 (CHead d1 (Bind Abbr) u1))).(let H0 \def 
(getl_gen_all c1 (CHead d1 (Bind Abbr) u1) i H) in (ex2_ind C (\lambda (e: 
C).(drop i O c1 e)) (\lambda (e: C).(clear e (CHead d1 (Bind Abbr) u1))) 
(\forall (c2: C).((csuba g c2 c1) \to (or3 (ex2 C (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))))) 
(\lambda (x: C).(\lambda (H1: (drop i O c1 x)).(\lambda (H2: (clear x (CHead 
d1 (Bind Abbr) u1))).(C_ind (\lambda (c: C).((drop i O c1 c) \to ((clear c 
(CHead d1 (Bind Abbr) u1)) \to (\forall (c2: C).((csuba g c2 c1) \to (or3 
(ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))))))))) (\lambda (n: nat).(\lambda (_: 
(drop i O c1 (CSort n))).(\lambda (H4: (clear (CSort n) (CHead d1 (Bind Abbr) 
u1))).(clear_gen_sort (CHead d1 (Bind Abbr) u1) n H4 (\forall (c2: C).((csuba 
g c2 c1) \to (or3 (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))))))))) (\lambda (x0: 
C).(\lambda (_: (((drop i O c1 x0) \to ((clear x0 (CHead d1 (Bind Abbr) u1)) 
\to (\forall (c2: C).((csuba g c2 c1) \to (or3 (ex2 C (\lambda (d2: C).(getl 
i c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 
d1))))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (H3: (drop i O c1 
(CHead x0 k t))).(\lambda (H4: (clear (CHead x0 k t) (CHead d1 (Bind Abbr) 
u1))).(K_ind (\lambda (k0: K).((drop i O c1 (CHead x0 k0 t)) \to ((clear 
(CHead x0 k0 t) (CHead d1 (Bind Abbr) u1)) \to (\forall (c2: C).((csuba g c2 
c1) \to (or3 (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))))))))) (\lambda (b: 
B).(\lambda (H5: (drop i O c1 (CHead x0 (Bind b) t))).(\lambda (H6: (clear 
(CHead x0 (Bind b) t) (CHead d1 (Bind Abbr) u1))).(let H7 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow d1 | (CHead c _ _) \Rightarrow c])) (CHead d1 (Bind Abbr) u1) 
(CHead x0 (Bind b) t) (clear_gen_bind b x0 (CHead d1 (Bind Abbr) u1) t H6)) 
in ((let H8 \def (f_equal C B (\lambda (e: C).(match e in C return (\lambda 
(_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k0 _) \Rightarrow 
(match k0 in K return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | 
(Flat _) \Rightarrow Abbr])])) (CHead d1 (Bind Abbr) u1) (CHead x0 (Bind b) 
t) (clear_gen_bind b x0 (CHead d1 (Bind Abbr) u1) t H6)) in ((let H9 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u1 | (CHead _ _ t0) \Rightarrow t0])) (CHead d1 (Bind 
Abbr) u1) (CHead x0 (Bind b) t) (clear_gen_bind b x0 (CHead d1 (Bind Abbr) 
u1) t H6)) in (\lambda (H10: (eq B Abbr b)).(\lambda (H11: (eq C d1 
x0)).(\lambda (c2: C).(\lambda (H12: (csuba g c2 c1)).(let H13 \def (eq_ind_r 
T t (\lambda (t0: T).(drop i O c1 (CHead x0 (Bind b) t0))) H5 u1 H9) in (let 
H14 \def (eq_ind_r B b (\lambda (b0: B).(drop i O c1 (CHead x0 (Bind b0) 
u1))) H13 Abbr H10) in (let H15 \def (eq_ind_r C x0 (\lambda (c: C).(drop i O 
c1 (CHead c (Bind Abbr) u1))) H14 d1 H11) in (let H16 \def 
(csuba_drop_abbr_rev i c1 d1 u1 H15 g c2 H12) in (or3_ind (ex2 C (\lambda 
(d2: C).(drop i O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop i 
O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(drop i O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (or3 (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (H17: (ex2 C 
(\lambda (d2: C).(drop i O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1)))).(ex2_ind C (\lambda (d2: C).(drop i O c2 (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) (or3 (ex2 C (\lambda (d2: 
C).(getl i c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(getl i c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (x1: C).(\lambda (H18: (drop i O c2 (CHead x1 
(Bind Abbr) u1))).(\lambda (H19: (csuba g x1 d1)).(or3_intro0 (ex2 C (\lambda 
(d2: C).(getl i c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i 
c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(getl i c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (ex_intro2 C (\lambda (d2: C).(getl i c2 (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)) x1 (getl_intro i c2 
(CHead x1 (Bind Abbr) u1) (CHead x1 (Bind Abbr) u1) H18 (clear_bind Abbr x1 
u1)) H19))))) H17)) (\lambda (H17: (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(drop i O c2 (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))))).(ex4_3_ind C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop i O c2 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a)))) (or3 (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x1: 
C).(\lambda (x2: T).(\lambda (x3: A).(\lambda (H18: (drop i O c2 (CHead x1 
(Bind Abst) x2))).(\lambda (H19: (csuba g x1 d1)).(\lambda (H20: (arity g x1 
x2 (asucc g x3))).(\lambda (H21: (arity g d1 u1 x3)).(or3_intro1 (ex2 C 
(\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(getl i c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) (ex4_3_intro C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a)))) x1 x2 x3 
(getl_intro i c2 (CHead x1 (Bind Abst) x2) (CHead x1 (Bind Abst) x2) H18 
(clear_bind Abst x1 x2)) H19 H20 H21))))))))) H17)) (\lambda (H17: (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(drop i O c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))).(ex2_2_ind C T (\lambda 
(d2: C).(\lambda (u2: T).(drop i O c2 (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1))) (or3 (ex2 C (\lambda (d2: C).(getl 
i c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl i c2 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) 
(\lambda (x1: C).(\lambda (x2: T).(\lambda (H18: (drop i O c2 (CHead x1 (Bind 
Void) x2))).(\lambda (H19: (csuba g x1 d1)).(or3_intro2 (ex2 C (\lambda (d2: 
C).(getl i c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(getl i c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda (d2: C).(\lambda (u2: 
T).(getl i c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))) x1 x2 (getl_intro i c2 (CHead x1 (Bind Void) x2) (CHead 
x1 (Bind Void) x2) H18 (clear_bind Void x1 x2)) H19)))))) H17)) H16)))))))))) 
H8)) H7))))) (\lambda (f: F).(\lambda (H5: (drop i O c1 (CHead x0 (Flat f) 
t))).(\lambda (H6: (clear (CHead x0 (Flat f) t) (CHead d1 (Bind Abbr) 
u1))).(let H7 \def H5 in (unintro C c1 (\lambda (c: C).((drop i O c (CHead x0 
(Flat f) t)) \to (\forall (c2: C).((csuba g c2 c) \to (or3 (ex2 C (\lambda 
(d2: C).(getl i c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i 
c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(getl i c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))))))) (nat_ind (\lambda (n: nat).(\forall (x1: C).((drop 
n O x1 (CHead x0 (Flat f) t)) \to (\forall (c2: C).((csuba g c2 x1) \to (or3 
(ex2 C (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(getl n c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(getl n c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))))))))) (\lambda (x1: C).(\lambda (H8: 
(drop O O x1 (CHead x0 (Flat f) t))).(\lambda (c2: C).(\lambda (H9: (csuba g 
c2 x1)).(let H10 \def (eq_ind C x1 (\lambda (c: C).(csuba g c2 c)) H9 (CHead 
x0 (Flat f) t) (drop_gen_refl x1 (CHead x0 (Flat f) t) H8)) in (let H_y \def 
(clear_flat x0 (CHead d1 (Bind Abbr) u1) (clear_gen_flat f x0 (CHead d1 (Bind 
Abbr) u1) t H6) f t) in (let H11 \def (csuba_clear_trans g (CHead x0 (Flat f) 
t) c2 H10 (CHead d1 (Bind Abbr) u1) H_y) in (ex2_ind C (\lambda (e2: 
C).(csuba g e2 (CHead d1 (Bind Abbr) u1))) (\lambda (e2: C).(clear c2 e2)) 
(or3 (ex2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(getl O c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(getl O c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x2: 
C).(\lambda (H12: (csuba g x2 (CHead d1 (Bind Abbr) u1))).(\lambda (H13: 
(clear c2 x2)).(let H_x \def (csuba_gen_abbr_rev g d1 x2 u1 H12) in (let H14 
\def H_x in (or3_ind (ex2 C (\lambda (d2: C).(eq C x2 (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(eq C x2 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(eq C x2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (or3 (ex2 C (\lambda (d2: 
C).(getl O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O c2 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(getl O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (H15: (ex2 C (\lambda (d2: C).(eq C x2 (CHead 
d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind C (\lambda 
(d2: C).(eq C x2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1)) (or3 (ex2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl O c2 (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(getl O c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda (x3: 
C).(\lambda (H16: (eq C x2 (CHead x3 (Bind Abbr) u1))).(\lambda (H17: (csuba 
g x3 d1)).(let H18 \def (eq_ind C x2 (\lambda (c: C).(clear c2 c)) H13 (CHead 
x3 (Bind Abbr) u1) H16) in (or3_intro0 (ex2 C (\lambda (d2: C).(getl O c2 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O c2 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl O c2 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) 
(ex_intro2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abbr) u1))) (\lambda 
(d2: C).(csuba g d2 d1)) x3 (getl_intro O c2 (CHead x3 (Bind Abbr) u1) c2 
(drop_refl c2) H18) H17)))))) H15)) (\lambda (H15: (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(eq C x2 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(eq C x2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))) (or3 (ex2 C (\lambda (d2: 
C).(getl O c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O c2 
(CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(getl O c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (x3: C).(\lambda (x4: T).(\lambda (x5: 
A).(\lambda (H16: (eq C x2 (CHead x3 (Bind Abst) x4))).(\lambda (H17: (csuba 
g x3 d1)).(\lambda (H18: (arity g x3 x4 (asucc g x5))).(\lambda (H19: (arity 
g d1 u1 x5)).(let H20 \def (eq_ind C x2 (\lambda (c: C).(clear c2 c)) H13 
(CHead x3 (Bind Abst) x4) H16) in (or3_intro1 (ex2 C (\lambda (d2: C).(getl O 
c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O c2 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl O c2 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) 
(ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O 
c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))) x3 x4 x5 (getl_intro O c2 (CHead x3 (Bind Abst) 
x4) c2 (drop_refl c2) H20) H17 H18 H19)))))))))) H15)) (\lambda (H15: (ex2_2 
C T (\lambda (d2: C).(\lambda (u2: T).(eq C x2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))).(ex2_2_ind C T (\lambda 
(d2: C).(\lambda (u2: T).(eq C x2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1))) (or3 (ex2 C (\lambda (d2: C).(getl O c2 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O c2 (CHead d2 (Bind 
Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 
d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl O c2 (CHead d2 
(Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) 
(\lambda (x3: C).(\lambda (x4: T).(\lambda (H16: (eq C x2 (CHead x3 (Bind 
Void) x4))).(\lambda (H17: (csuba g x3 d1)).(let H18 \def (eq_ind C x2 
(\lambda (c: C).(clear c2 c)) H13 (CHead x3 (Bind Void) x4) H16) in 
(or3_intro2 (ex2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abbr) u1))) 
(\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl O c2 (CHead d2 (Bind Abst) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T 
(\lambda (d2: C).(\lambda (u2: T).(getl O c2 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex2_2_intro C T (\lambda 
(d2: C).(\lambda (u2: T).(getl O c2 (CHead d2 (Bind Void) u2)))) (\lambda 
(d2: C).(\lambda (_: T).(csuba g d2 d1))) x3 x4 (getl_intro O c2 (CHead x3 
(Bind Void) x4) c2 (drop_refl c2) H18) H17))))))) H15)) H14)))))) H11)))))))) 
(\lambda (n: nat).(\lambda (H8: ((\forall (x1: C).((drop n O x1 (CHead x0 
(Flat f) t)) \to (\forall (c2: C).((csuba g c2 x1) \to (or3 (ex2 C (\lambda 
(d2: C).(getl n c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl n 
c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(getl n c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))))))))).(\lambda (x1: C).(\lambda (H9: (drop (S n) O x1 
(CHead x0 (Flat f) t))).(\lambda (c2: C).(\lambda (H10: (csuba g c2 x1)).(let 
H11 \def (drop_clear x1 (CHead x0 (Flat f) t) n H9) in (ex2_3_ind B C T 
(\lambda (b: B).(\lambda (e: C).(\lambda (v: T).(clear x1 (CHead e (Bind b) 
v))))) (\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop n O e (CHead x0 
(Flat f) t))))) (or3 (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl (S n) c2 (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda 
(x2: B).(\lambda (x3: C).(\lambda (x4: T).(\lambda (H12: (clear x1 (CHead x3 
(Bind x2) x4))).(\lambda (H13: (drop n O x3 (CHead x0 (Flat f) t))).(let H14 
\def (csuba_clear_trans g x1 c2 H10 (CHead x3 (Bind x2) x4) H12) in (ex2_ind 
C (\lambda (e2: C).(csuba g e2 (CHead x3 (Bind x2) x4))) (\lambda (e2: 
C).(clear c2 e2)) (or3 (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind 
Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl (S n) c2 (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda 
(x5: C).(\lambda (H15: (csuba g x5 (CHead x3 (Bind x2) x4))).(\lambda (H16: 
(clear c2 x5)).(let H_x \def (csuba_gen_bind_rev g x2 x3 x5 x4 H15) in (let 
H17 \def H_x in (ex2_3_ind B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda 
(v2: T).(eq C x5 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csuba g e2 x3)))) (or3 (ex2 C (\lambda (d2: C).(getl (S 
n) c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead 
d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(getl (S n) c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (x6: B).(\lambda (x7: C).(\lambda (x8: 
T).(\lambda (H18: (eq C x5 (CHead x7 (Bind x6) x8))).(\lambda (H19: (csuba g 
x7 x3)).(let H20 \def (eq_ind C x5 (\lambda (c: C).(clear c2 c)) H16 (CHead 
x7 (Bind x6) x8) H18) in (let H21 \def (H8 x3 H13 x7 H19) in (or3_ind (ex2 C 
(\lambda (d2: C).(getl n x7 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(getl n x7 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: 
C).(\lambda (u2: T).(getl n x7 (CHead d2 (Bind Void) u2)))) (\lambda (d2: 
C).(\lambda (_: T).(csuba g d2 d1)))) (or3 (ex2 C (\lambda (d2: C).(getl (S 
n) c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead 
d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(getl (S n) c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (H22: (ex2 C (\lambda (d2: C).(getl n x7 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1)))).(ex2_ind C 
(\lambda (d2: C).(getl n x7 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1)) (or3 (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl (S n) c2 (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))) (\lambda 
(x9: C).(\lambda (H23: (getl n x7 (CHead x9 (Bind Abbr) u1))).(\lambda (H24: 
(csuba g x9 d1)).(or3_intro0 (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 
(Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl (S n) c2 (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex_intro2 C 
(\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: 
C).(csuba g d2 d1)) x9 (getl_clear_bind x6 c2 x7 x8 H20 (CHead x9 (Bind Abbr) 
u1) n H23) H24))))) H22)) (\lambda (H22: (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl n x7 (CHead d2 (Bind Abst) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(getl n x7 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (a: A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda 
(_: T).(\lambda (a: A).(arity g d1 u1 a)))) (or3 (ex2 C (\lambda (d2: 
C).(getl (S n) c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S 
n) c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(getl (S n) c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (x9: C).(\lambda (x10: T).(\lambda (x11: 
A).(\lambda (H23: (getl n x7 (CHead x9 (Bind Abst) x10))).(\lambda (H24: 
(csuba g x9 d1)).(\lambda (H25: (arity g x9 x10 (asucc g x11))).(\lambda 
(H26: (arity g d1 u1 x11)).(or3_intro1 (ex2 C (\lambda (d2: C).(getl (S n) c2 
(CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 
(Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
(asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 
u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl (S n) c2 (CHead 
d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) 
(ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S 
n) c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a)))) x9 x10 x11 (getl_clear_bind x6 c2 x7 x8 H20 
(CHead x9 (Bind Abst) x10) n H23) H24 H25 H26))))))))) H22)) (\lambda (H22: 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl n x7 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))))).(ex2_2_ind C T 
(\lambda (d2: C).(\lambda (u2: T).(getl n x7 (CHead d2 (Bind Void) u2)))) 
(\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) (or3 (ex2 C (\lambda (d2: 
C).(getl (S n) c2 (CHead d2 (Bind Abbr) u1))) (\lambda (d2: C).(csuba g d2 
d1))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S 
n) c2 (CHead d2 (Bind Abst) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d2 d1)))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 (asucc g a))))) (\lambda (_: C).(\lambda (_: T).(\lambda 
(a: A).(arity g d1 u1 a))))) (ex2_2 C T (\lambda (d2: C).(\lambda (u2: 
T).(getl (S n) c2 (CHead d2 (Bind Void) u2)))) (\lambda (d2: C).(\lambda (_: 
T).(csuba g d2 d1))))) (\lambda (x9: C).(\lambda (x10: T).(\lambda (H23: 
(getl n x7 (CHead x9 (Bind Void) x10))).(\lambda (H24: (csuba g x9 
d1)).(or3_intro2 (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abbr) 
u1))) (\lambda (d2: C).(csuba g d2 d1))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abst) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d2 d1)))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 (asucc g 
a))))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 a))))) 
(ex2_2 C T (\lambda (d2: C).(\lambda (u2: T).(getl (S n) c2 (CHead d2 (Bind 
Void) u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1)))) (ex2_2_intro 
C T (\lambda (d2: C).(\lambda (u2: T).(getl (S n) c2 (CHead d2 (Bind Void) 
u2)))) (\lambda (d2: C).(\lambda (_: T).(csuba g d2 d1))) x9 x10 
(getl_clear_bind x6 c2 x7 x8 H20 (CHead x9 (Bind Void) x10) n H23) H24)))))) 
H22)) H21)))))))) H17)))))) H14))))))) H11)))))))) i) H7))))) k H3 H4))))))) 
x H1 H2)))) H0))))))).
(* COMMENTS
Initial nodes: 9091
END *)

