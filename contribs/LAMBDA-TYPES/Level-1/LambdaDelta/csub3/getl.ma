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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/csub3/getl".

include "csub3/fwd.ma".

include "csub3/clear.ma".

include "csub3/drop.ma".

include "getl/clear.ma".

theorem csub3_getl_abbr:
 \forall (g: G).(\forall (c1: C).(\forall (d1: C).(\forall (u: T).(\forall 
(n: nat).((getl n c1 (CHead d1 (Bind Abbr) u)) \to (\forall (c2: C).((csub3 g 
c1 c2) \to (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(getl n 
c2 (CHead d2 (Bind Abbr) u)))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (d1: C).(\lambda (u: T).(\lambda 
(n: nat).(\lambda (H: (getl n c1 (CHead d1 (Bind Abbr) u))).(let H0 \def 
(getl_gen_all c1 (CHead d1 (Bind Abbr) u) n H) in (ex2_ind C (\lambda (e: 
C).(drop n O c1 e)) (\lambda (e: C).(clear e (CHead d1 (Bind Abbr) u))) 
(\forall (c2: C).((csub3 g c1 c2) \to (ex2 C (\lambda (d2: C).(csub3 g d1 
d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) u)))))) (\lambda (x: 
C).(\lambda (H1: (drop n O c1 x)).(\lambda (H2: (clear x (CHead d1 (Bind 
Abbr) u))).((match x in C return (\lambda (c: C).((drop n O c1 c) \to ((clear 
c (CHead d1 (Bind Abbr) u)) \to (\forall (c2: C).((csub3 g c1 c2) \to (ex2 C 
(\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind 
Abbr) u))))))))) with [(CSort n0) \Rightarrow (\lambda (_: (drop n O c1 
(CSort n0))).(\lambda (H4: (clear (CSort n0) (CHead d1 (Bind Abbr) 
u))).(clear_gen_sort (CHead d1 (Bind Abbr) u) n0 H4 (\forall (c2: C).((csub3 
g c1 c2) \to (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(getl 
n c2 (CHead d2 (Bind Abbr) u))))))))) | (CHead c k t) \Rightarrow (\lambda 
(H3: (drop n O c1 (CHead c k t))).(\lambda (H4: (clear (CHead c k t) (CHead 
d1 (Bind Abbr) u))).((match k in K return (\lambda (k0: K).((drop n O c1 
(CHead c k0 t)) \to ((clear (CHead c k0 t) (CHead d1 (Bind Abbr) u)) \to 
(\forall (c2: C).((csub3 g c1 c2) \to (ex2 C (\lambda (d2: C).(csub3 g d1 
d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) u))))))))) with [(Bind 
b) \Rightarrow (\lambda (H5: (drop n O c1 (CHead c (Bind b) t))).(\lambda 
(H6: (clear (CHead c (Bind b) t) (CHead d1 (Bind Abbr) u))).(let H7 \def 
(f_equal C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow d1 | (CHead c0 _ _) \Rightarrow c0])) (CHead d1 (Bind 
Abbr) u) (CHead c (Bind b) t) (clear_gen_bind b c (CHead d1 (Bind Abbr) u) t 
H6)) in ((let H8 \def (f_equal C B (\lambda (e: C).(match e in C return 
(\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k0 _) 
\Rightarrow (match k0 in K return (\lambda (_: K).B) with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) (CHead d1 (Bind Abbr) u) 
(CHead c (Bind b) t) (clear_gen_bind b c (CHead d1 (Bind Abbr) u) t H6)) in 
((let H9 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: 
C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) (CHead 
d1 (Bind Abbr) u) (CHead c (Bind b) t) (clear_gen_bind b c (CHead d1 (Bind 
Abbr) u) t H6)) in (\lambda (H10: (eq B Abbr b)).(\lambda (H11: (eq C d1 
c)).(\lambda (c2: C).(\lambda (H12: (csub3 g c1 c2)).(let H13 \def (eq_ind_r 
T t (\lambda (t0: T).(drop n O c1 (CHead c (Bind b) t0))) H5 u H9) in (let 
H14 \def (eq_ind_r B b (\lambda (b0: B).(drop n O c1 (CHead c (Bind b0) u))) 
H13 Abbr H10) in (let H15 \def (eq_ind_r C c (\lambda (c0: C).(drop n O c1 
(CHead c0 (Bind Abbr) u))) H14 d1 H11) in (ex2_ind C (\lambda (d2: C).(csub3 
g d1 d2)) (\lambda (d2: C).(drop n O c2 (CHead d2 (Bind Abbr) u))) (ex2 C 
(\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind 
Abbr) u)))) (\lambda (x0: C).(\lambda (H16: (csub3 g d1 x0)).(\lambda (H17: 
(drop n O c2 (CHead x0 (Bind Abbr) u))).(ex_intro2 C (\lambda (d2: C).(csub3 
g d1 d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) u))) x0 H16 
(getl_intro n c2 (CHead x0 (Bind Abbr) u) (CHead x0 (Bind Abbr) u) H17 
(clear_bind Abbr x0 u)))))) (csub3_drop_abbr g n c1 c2 H12 d1 u H15)))))))))) 
H8)) H7)))) | (Flat f) \Rightarrow (\lambda (H5: (drop n O c1 (CHead c (Flat 
f) t))).(\lambda (H6: (clear (CHead c (Flat f) t) (CHead d1 (Bind Abbr) 
u))).(let H7 \def H5 in (unintro C c1 (\lambda (c0: C).((drop n O c0 (CHead c 
(Flat f) t)) \to (\forall (c2: C).((csub3 g c0 c2) \to (ex2 C (\lambda (d2: 
C).(csub3 g d1 d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) 
u)))))))) (nat_ind (\lambda (n0: nat).(\forall (x0: C).((drop n0 O x0 (CHead 
c (Flat f) t)) \to (\forall (c2: C).((csub3 g x0 c2) \to (ex2 C (\lambda (d2: 
C).(csub3 g d1 d2)) (\lambda (d2: C).(getl n0 c2 (CHead d2 (Bind Abbr) 
u))))))))) (\lambda (x0: C).(\lambda (H8: (drop O O x0 (CHead c (Flat f) 
t))).(\lambda (c2: C).(\lambda (H9: (csub3 g x0 c2)).(let H10 \def (eq_ind C 
x0 (\lambda (c0: C).(csub3 g c0 c2)) H9 (CHead c (Flat f) t) (drop_gen_refl 
x0 (CHead c (Flat f) t) H8)) in (let H_y \def (clear_flat c (CHead d1 (Bind 
Abbr) u) (clear_gen_flat f c (CHead d1 (Bind Abbr) u) t H6) f t) in (let H11 
\def (csub3_clear_conf g (CHead c (Flat f) t) c2 H10 (CHead d1 (Bind Abbr) u) 
H_y) in (ex2_ind C (\lambda (e2: C).(csub3 g (CHead d1 (Bind Abbr) u) e2)) 
(\lambda (e2: C).(clear c2 e2)) (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) 
(\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (x1: 
C).(\lambda (H12: (csub3 g (CHead d1 (Bind Abbr) u) x1)).(\lambda (H13: 
(clear c2 x1)).(let H14 \def (csub3_gen_abbr g d1 x1 u H12) in (ex2_ind C 
(\lambda (e2: C).(eq C x1 (CHead e2 (Bind Abbr) u))) (\lambda (e2: C).(csub3 
g d1 e2)) (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(getl O 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (x2: C).(\lambda (H15: (eq C x1 
(CHead x2 (Bind Abbr) u))).(\lambda (H16: (csub3 g d1 x2)).(let H17 \def 
(eq_ind C x1 (\lambda (c0: C).(clear c2 c0)) H13 (CHead x2 (Bind Abbr) u) 
H15) in (ex_intro2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(getl 
O c2 (CHead d2 (Bind Abbr) u))) x2 H16 (getl_intro O c2 (CHead x2 (Bind Abbr) 
u) c2 (drop_refl c2) H17)))))) H14))))) H11)))))))) (\lambda (n0: 
nat).(\lambda (H8: ((\forall (x0: C).((drop n0 O x0 (CHead c (Flat f) t)) \to 
(\forall (c2: C).((csub3 g x0 c2) \to (ex2 C (\lambda (d2: C).(csub3 g d1 
d2)) (\lambda (d2: C).(getl n0 c2 (CHead d2 (Bind Abbr) u)))))))))).(\lambda 
(x0: C).(\lambda (H9: (drop (S n0) O x0 (CHead c (Flat f) t))).(\lambda (c2: 
C).(\lambda (H10: (csub3 g x0 c2)).(let H11 \def (drop_clear x0 (CHead c 
(Flat f) t) n0 H9) in (ex2_3_ind B C T (\lambda (b: B).(\lambda (e: 
C).(\lambda (v: T).(clear x0 (CHead e (Bind b) v))))) (\lambda (_: 
B).(\lambda (e: C).(\lambda (_: T).(drop n0 O e (CHead c (Flat f) t))))) (ex2 
C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead 
d2 (Bind Abbr) u)))) (\lambda (x1: B).(\lambda (x2: C).(\lambda (x3: 
T).(\lambda (H12: (clear x0 (CHead x2 (Bind x1) x3))).(\lambda (H13: (drop n0 
O x2 (CHead c (Flat f) t))).(let H14 \def (csub3_clear_conf g x0 c2 H10 
(CHead x2 (Bind x1) x3) H12) in (ex2_ind C (\lambda (e2: C).(csub3 g (CHead 
x2 (Bind x1) x3) e2)) (\lambda (e2: C).(clear c2 e2)) (ex2 C (\lambda (d2: 
C).(csub3 g d1 d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abbr) 
u)))) (\lambda (x4: C).(\lambda (H15: (csub3 g (CHead x2 (Bind x1) x3) 
x4)).(\lambda (H16: (clear c2 x4)).(let H17 \def (csub3_gen_bind g x1 x2 x4 
x3 H15) in (ex2_3_ind B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: 
T).(eq C x4 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csub3 g x2 e2)))) (ex2 C (\lambda (d2: C).(csub3 g d1 
d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abbr) u)))) (\lambda 
(x5: B).(\lambda (x6: C).(\lambda (x7: T).(\lambda (H18: (eq C x4 (CHead x6 
(Bind x5) x7))).(\lambda (H19: (csub3 g x2 x6)).(let H20 \def (eq_ind C x4 
(\lambda (c0: C).(clear c2 c0)) H16 (CHead x6 (Bind x5) x7) H18) in (let H21 
\def (H8 x2 H13 x6 H19) in (ex2_ind C (\lambda (d2: C).(csub3 g d1 d2)) 
(\lambda (d2: C).(getl n0 x6 (CHead d2 (Bind Abbr) u))) (ex2 C (\lambda (d2: 
C).(csub3 g d1 d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abbr) 
u)))) (\lambda (x8: C).(\lambda (H22: (csub3 g d1 x8)).(\lambda (H23: (getl 
n0 x6 (CHead x8 (Bind Abbr) u))).(ex_intro2 C (\lambda (d2: C).(csub3 g d1 
d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abbr) u))) x8 H22 
(getl_clear_bind x5 c2 x6 x7 H20 (CHead x8 (Bind Abbr) u) n0 H23))))) 
H21)))))))) H17))))) H14))))))) H11)))))))) n) H7))))]) H3 H4)))]) H1 H2)))) 
H0))))))).

theorem csub3_getl_abst:
 \forall (g: G).(\forall (c1: C).(\forall (d1: C).(\forall (t: T).(\forall 
(n: nat).((getl n c1 (CHead d1 (Bind Abst) t)) \to (\forall (c2: C).((csub3 g 
c1 c2) \to (or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: 
C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t))))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (d1: C).(\lambda (t: T).(\lambda 
(n: nat).(\lambda (H: (getl n c1 (CHead d1 (Bind Abst) t))).(let H0 \def 
(getl_gen_all c1 (CHead d1 (Bind Abst) t) n H) in (ex2_ind C (\lambda (e: 
C).(drop n O c1 e)) (\lambda (e: C).(clear e (CHead d1 (Bind Abst) t))) 
(\forall (c2: C).((csub3 g c1 c2) \to (or (ex2 C (\lambda (d2: C).(csub3 g d1 
d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl n c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: 
T).(ty3 g d2 u t))))))) (\lambda (x: C).(\lambda (H1: (drop n O c1 
x)).(\lambda (H2: (clear x (CHead d1 (Bind Abst) t))).((match x in C return 
(\lambda (c: C).((drop n O c1 c) \to ((clear c (CHead d1 (Bind Abst) t)) \to 
(\forall (c2: C).((csub3 g c1 c2) \to (or (ex2 C (\lambda (d2: C).(csub3 g d1 
d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl n c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: 
T).(ty3 g d2 u t)))))))))) with [(CSort n0) \Rightarrow (\lambda (_: (drop n 
O c1 (CSort n0))).(\lambda (H4: (clear (CSort n0) (CHead d1 (Bind Abst) 
t))).(clear_gen_sort (CHead d1 (Bind Abst) t) n0 H4 (\forall (c2: C).((csub3 
g c1 c2) \to (or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: 
C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t)))))))))) | (CHead c k t0) \Rightarrow (\lambda (H3: (drop n O c1 (CHead c 
k t0))).(\lambda (H4: (clear (CHead c k t0) (CHead d1 (Bind Abst) 
t))).((match k in K return (\lambda (k0: K).((drop n O c1 (CHead c k0 t0)) 
\to ((clear (CHead c k0 t0) (CHead d1 (Bind Abst) t)) \to (\forall (c2: 
C).((csub3 g c1 c2) \to (or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda 
(d2: C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t)))))))))) with [(Bind b) \Rightarrow (\lambda (H5: (drop n O c1 (CHead c 
(Bind b) t0))).(\lambda (H6: (clear (CHead c (Bind b) t0) (CHead d1 (Bind 
Abst) t))).(let H7 \def (f_equal C C (\lambda (e: C).(match e in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow d1 | (CHead c0 _ _) 
\Rightarrow c0])) (CHead d1 (Bind Abst) t) (CHead c (Bind b) t0) 
(clear_gen_bind b c (CHead d1 (Bind Abst) t) t0 H6)) in ((let H8 \def 
(f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow Abst | (CHead _ k0 _) \Rightarrow (match k0 in K 
return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) 
\Rightarrow Abst])])) (CHead d1 (Bind Abst) t) (CHead c (Bind b) t0) 
(clear_gen_bind b c (CHead d1 (Bind Abst) t) t0 H6)) in ((let H9 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow t | (CHead _ _ t1) \Rightarrow t1])) (CHead d1 (Bind 
Abst) t) (CHead c (Bind b) t0) (clear_gen_bind b c (CHead d1 (Bind Abst) t) 
t0 H6)) in (\lambda (H10: (eq B Abst b)).(\lambda (H11: (eq C d1 c)).(\lambda 
(c2: C).(\lambda (H12: (csub3 g c1 c2)).(let H13 \def (eq_ind_r T t0 (\lambda 
(t1: T).(drop n O c1 (CHead c (Bind b) t1))) H5 t H9) in (let H14 \def 
(eq_ind_r B b (\lambda (b0: B).(drop n O c1 (CHead c (Bind b0) t))) H13 Abst 
H10) in (let H15 \def (eq_ind_r C c (\lambda (c0: C).(drop n O c1 (CHead c0 
(Bind Abst) t))) H14 d1 H11) in (or_ind (ex2 C (\lambda (d2: C).(csub3 g d1 
d2)) (\lambda (d2: C).(drop n O c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(drop n O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: 
T).(ty3 g d2 u t)))) (or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda 
(d2: C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t))))) (\lambda (H16: (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: 
C).(drop n O c2 (CHead d2 (Bind Abst) t))))).(ex2_ind C (\lambda (d2: 
C).(csub3 g d1 d2)) (\lambda (d2: C).(drop n O c2 (CHead d2 (Bind Abst) t))) 
(or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(getl n c2 
(CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n c2 (CHead d2 
(Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) 
(\lambda (x0: C).(\lambda (H17: (csub3 g d1 x0)).(\lambda (H18: (drop n O c2 
(CHead x0 (Bind Abst) t))).(or_introl (ex2 C (\lambda (d2: C).(csub3 g d1 
d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl n c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: 
T).(ty3 g d2 u t)))) (ex_intro2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda 
(d2: C).(getl n c2 (CHead d2 (Bind Abst) t))) x0 H17 (getl_intro n c2 (CHead 
x0 (Bind Abst) t) (CHead x0 (Bind Abst) t) H18 (clear_bind Abst x0 t))))))) 
H16)) (\lambda (H16: (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csub3 g d1 
d2))) (\lambda (d2: C).(\lambda (u: T).(drop n O c2 (CHead d2 (Bind Abbr) 
u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))).(ex3_2_ind C T 
(\lambda (d2: C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(drop n O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: 
T).(ty3 g d2 u t))) (or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda 
(d2: C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t))))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H17: (csub3 g d1 
x0)).(\lambda (H18: (drop n O c2 (CHead x0 (Bind Abbr) x1))).(\lambda (H19: 
(ty3 g x0 x1 t)).(or_intror (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda 
(d2: C).(getl n c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t)))) (ex3_2_intro C T (\lambda (d2: C).(\lambda (_: T).(csub3 g d1 d2))) 
(\lambda (d2: C).(\lambda (u: T).(getl n c2 (CHead d2 (Bind Abbr) u)))) 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) x0 x1 H17 (getl_intro n c2 
(CHead x0 (Bind Abbr) x1) (CHead x0 (Bind Abbr) x1) H18 (clear_bind Abbr x0 
x1)) H19))))))) H16)) (csub3_drop_abst g n c1 c2 H12 d1 t H15)))))))))) H8)) 
H7)))) | (Flat f) \Rightarrow (\lambda (H5: (drop n O c1 (CHead c (Flat f) 
t0))).(\lambda (H6: (clear (CHead c (Flat f) t0) (CHead d1 (Bind Abst) 
t))).(let H7 \def H5 in (unintro C c1 (\lambda (c0: C).((drop n O c0 (CHead c 
(Flat f) t0)) \to (\forall (c2: C).((csub3 g c0 c2) \to (or (ex2 C (\lambda 
(d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) 
t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda 
(d2: C).(\lambda (u: T).(getl n c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t))))))))) (nat_ind (\lambda (n0: 
nat).(\forall (x0: C).((drop n0 O x0 (CHead c (Flat f) t0)) \to (\forall (c2: 
C).((csub3 g x0 c2) \to (or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda 
(d2: C).(getl n0 c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl 
n0 c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 
u t)))))))))) (\lambda (x0: C).(\lambda (H8: (drop O O x0 (CHead c (Flat f) 
t0))).(\lambda (c2: C).(\lambda (H9: (csub3 g x0 c2)).(let H10 \def (eq_ind C 
x0 (\lambda (c0: C).(csub3 g c0 c2)) H9 (CHead c (Flat f) t0) (drop_gen_refl 
x0 (CHead c (Flat f) t0) H8)) in (let H_y \def (clear_flat c (CHead d1 (Bind 
Abst) t) (clear_gen_flat f c (CHead d1 (Bind Abst) t) t0 H6) f t0) in (let 
H11 \def (csub3_clear_conf g (CHead c (Flat f) t0) c2 H10 (CHead d1 (Bind 
Abst) t) H_y) in (ex2_ind C (\lambda (e2: C).(csub3 g (CHead d1 (Bind Abst) 
t) e2)) (\lambda (e2: C).(clear c2 e2)) (or (ex2 C (\lambda (d2: C).(csub3 g 
d1 d2)) (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: 
T).(ty3 g d2 u t))))) (\lambda (x1: C).(\lambda (H12: (csub3 g (CHead d1 
(Bind Abst) t) x1)).(\lambda (H13: (clear c2 x1)).(let H14 \def 
(csub3_gen_abst g d1 x1 t H12) in (or_ind (ex2 C (\lambda (e2: C).(eq C x1 
(CHead e2 (Bind Abst) t))) (\lambda (e2: C).(csub3 g d1 e2))) (ex3_2 C T 
(\lambda (e2: C).(\lambda (v2: T).(eq C x1 (CHead e2 (Bind Abbr) v2)))) 
(\lambda (e2: C).(\lambda (_: T).(csub3 g d1 e2))) (\lambda (e2: C).(\lambda 
(v2: T).(ty3 g e2 v2 t)))) (or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) 
(\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda 
(d2: C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: 
T).(getl O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: 
T).(ty3 g d2 u t))))) (\lambda (H15: (ex2 C (\lambda (e2: C).(eq C x1 (CHead 
e2 (Bind Abst) t))) (\lambda (e2: C).(csub3 g d1 e2)))).(ex2_ind C (\lambda 
(e2: C).(eq C x1 (CHead e2 (Bind Abst) t))) (\lambda (e2: C).(csub3 g d1 e2)) 
(or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(getl O c2 
(CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl O c2 (CHead d2 
(Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) 
(\lambda (x2: C).(\lambda (H16: (eq C x1 (CHead x2 (Bind Abst) t))).(\lambda 
(H17: (csub3 g d1 x2)).(let H18 \def (eq_ind C x1 (\lambda (c0: C).(clear c2 
c0)) H13 (CHead x2 (Bind Abst) t) H16) in (or_introl (ex2 C (\lambda (d2: 
C).(csub3 g d1 d2)) (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) t)))) 
(ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: 
C).(\lambda (u: T).(getl O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: 
C).(\lambda (u: T).(ty3 g d2 u t)))) (ex_intro2 C (\lambda (d2: C).(csub3 g 
d1 d2)) (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) t))) x2 H17 
(getl_intro O c2 (CHead x2 (Bind Abst) t) c2 (drop_refl c2) H18))))))) H15)) 
(\lambda (H15: (ex3_2 C T (\lambda (e2: C).(\lambda (v2: T).(eq C x1 (CHead 
e2 (Bind Abbr) v2)))) (\lambda (e2: C).(\lambda (_: T).(csub3 g d1 e2))) 
(\lambda (e2: C).(\lambda (v2: T).(ty3 g e2 v2 t))))).(ex3_2_ind C T (\lambda 
(e2: C).(\lambda (v2: T).(eq C x1 (CHead e2 (Bind Abbr) v2)))) (\lambda (e2: 
C).(\lambda (_: T).(csub3 g d1 e2))) (\lambda (e2: C).(\lambda (v2: T).(ty3 g 
e2 v2 t))) (or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: 
C).(getl O c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl O 
c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t))))) (\lambda (x2: C).(\lambda (x3: T).(\lambda (H16: (eq C x1 (CHead x2 
(Bind Abbr) x3))).(\lambda (H17: (csub3 g d1 x2)).(\lambda (H18: (ty3 g x2 x3 
t)).(let H19 \def (eq_ind C x1 (\lambda (c0: C).(clear c2 c0)) H13 (CHead x2 
(Bind Abbr) x3) H16) in (or_intror (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) 
(\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda 
(d2: C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: 
T).(getl O c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: 
T).(ty3 g d2 u t)))) (ex3_2_intro C T (\lambda (d2: C).(\lambda (_: T).(csub3 
g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl O c2 (CHead d2 (Bind Abbr) 
u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) x2 x3 H17 (getl_intro 
O c2 (CHead x2 (Bind Abbr) x3) c2 (drop_refl c2) H19) H18)))))))) H15)) 
H14))))) H11)))))))) (\lambda (n0: nat).(\lambda (H8: ((\forall (x0: 
C).((drop n0 O x0 (CHead c (Flat f) t0)) \to (\forall (c2: C).((csub3 g x0 
c2) \to (or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(getl 
n0 c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl n0 c2 (CHead d2 
(Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t))))))))))).(\lambda (x0: C).(\lambda (H9: (drop (S n0) O x0 (CHead c (Flat 
f) t0))).(\lambda (c2: C).(\lambda (H10: (csub3 g x0 c2)).(let H11 \def 
(drop_clear x0 (CHead c (Flat f) t0) n0 H9) in (ex2_3_ind B C T (\lambda (b: 
B).(\lambda (e: C).(\lambda (v: T).(clear x0 (CHead e (Bind b) v))))) 
(\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop n0 O e (CHead c (Flat 
f) t0))))) (or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: 
C).(getl (S n0) c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl 
(S n0) c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g 
d2 u t))))) (\lambda (x1: B).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H12: 
(clear x0 (CHead x2 (Bind x1) x3))).(\lambda (H13: (drop n0 O x2 (CHead c 
(Flat f) t0))).(let H14 \def (csub3_clear_conf g x0 c2 H10 (CHead x2 (Bind 
x1) x3) H12) in (ex2_ind C (\lambda (e2: C).(csub3 g (CHead x2 (Bind x1) x3) 
e2)) (\lambda (e2: C).(clear c2 e2)) (or (ex2 C (\lambda (d2: C).(csub3 g d1 
d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl (S n0) c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda 
(u: T).(ty3 g d2 u t))))) (\lambda (x4: C).(\lambda (H15: (csub3 g (CHead x2 
(Bind x1) x3) x4)).(\lambda (H16: (clear c2 x4)).(let H17 \def 
(csub3_gen_bind g x1 x2 x4 x3 H15) in (ex2_3_ind B C T (\lambda (b2: 
B).(\lambda (e2: C).(\lambda (v2: T).(eq C x4 (CHead e2 (Bind b2) v2))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (_: T).(csub3 g x2 e2)))) (or (ex2 
C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead 
d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csub3 g d1 
d2))) (\lambda (d2: C).(\lambda (u: T).(getl (S n0) c2 (CHead d2 (Bind Abbr) 
u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) (\lambda (x5: 
B).(\lambda (x6: C).(\lambda (x7: T).(\lambda (H18: (eq C x4 (CHead x6 (Bind 
x5) x7))).(\lambda (H19: (csub3 g x2 x6)).(let H20 \def (eq_ind C x4 (\lambda 
(c0: C).(clear c2 c0)) H16 (CHead x6 (Bind x5) x7) H18) in (let H21 \def (H8 
x2 H13 x6 H19) in (or_ind (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda 
(d2: C).(getl n0 x6 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl 
n0 x6 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 
u t)))) (or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(getl 
(S n0) c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda 
(_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl (S n0) c2 
(CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u 
t))))) (\lambda (H22: (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: 
C).(getl n0 x6 (CHead d2 (Bind Abst) t))))).(ex2_ind C (\lambda (d2: 
C).(csub3 g d1 d2)) (\lambda (d2: C).(getl n0 x6 (CHead d2 (Bind Abst) t))) 
(or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda (d2: C).(getl (S n0) c2 
(CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: C).(\lambda (_: 
T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl (S n0) c2 (CHead 
d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))) 
(\lambda (x8: C).(\lambda (H23: (csub3 g d1 x8)).(\lambda (H24: (getl n0 x6 
(CHead x8 (Bind Abst) t))).(or_introl (ex2 C (\lambda (d2: C).(csub3 g d1 
d2)) (\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T 
(\lambda (d2: C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda 
(u: T).(getl (S n0) c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda 
(u: T).(ty3 g d2 u t)))) (ex_intro2 C (\lambda (d2: C).(csub3 g d1 d2)) 
(\lambda (d2: C).(getl (S n0) c2 (CHead d2 (Bind Abst) t))) x8 H23 
(getl_clear_bind x5 c2 x6 x7 H20 (CHead x8 (Bind Abst) t) n0 H24)))))) H22)) 
(\lambda (H22: (ex3_2 C T (\lambda (d2: C).(\lambda (_: T).(csub3 g d1 d2))) 
(\lambda (d2: C).(\lambda (u: T).(getl n0 x6 (CHead d2 (Bind Abbr) u)))) 
(\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))))).(ex3_2_ind C T (\lambda 
(d2: C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: 
T).(getl n0 x6 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: 
T).(ty3 g d2 u t))) (or (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda 
(d2: C).(getl (S n0) c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl 
(S n0) c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g 
d2 u t))))) (\lambda (x8: C).(\lambda (x9: T).(\lambda (H23: (csub3 g d1 
x8)).(\lambda (H24: (getl n0 x6 (CHead x8 (Bind Abbr) x9))).(\lambda (H25: 
(ty3 g x8 x9 t)).(or_intror (ex2 C (\lambda (d2: C).(csub3 g d1 d2)) (\lambda 
(d2: C).(getl (S n0) c2 (CHead d2 (Bind Abst) t)))) (ex3_2 C T (\lambda (d2: 
C).(\lambda (_: T).(csub3 g d1 d2))) (\lambda (d2: C).(\lambda (u: T).(getl 
(S n0) c2 (CHead d2 (Bind Abbr) u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g 
d2 u t)))) (ex3_2_intro C T (\lambda (d2: C).(\lambda (_: T).(csub3 g d1 
d2))) (\lambda (d2: C).(\lambda (u: T).(getl (S n0) c2 (CHead d2 (Bind Abbr) 
u)))) (\lambda (d2: C).(\lambda (u: T).(ty3 g d2 u t))) x8 x9 H23 
(getl_clear_bind x5 c2 x6 x7 H20 (CHead x8 (Bind Abbr) x9) n0 H24) H25))))))) 
H22)) H21)))))))) H17))))) H14))))))) H11)))))))) n) H7))))]) H3 H4)))]) H1 
H2)))) H0))))))).

