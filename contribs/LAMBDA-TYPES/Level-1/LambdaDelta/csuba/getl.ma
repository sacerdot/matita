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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/csuba/getl".

include "csuba/drop.ma".

include "csuba/clear.ma".

include "getl/clear.ma".

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
Abbr) u))).((match x in C return (\lambda (c: C).((drop i O c1 c) \to ((clear 
c (CHead d1 (Bind Abbr) u)) \to (\forall (c2: C).((csuba g c1 c2) \to (ex2 C 
(\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: 
C).(csuba g d1 d2)))))))) with [(CSort n) \Rightarrow (\lambda (_: (drop i O 
c1 (CSort n))).(\lambda (H4: (clear (CSort n) (CHead d1 (Bind Abbr) 
u))).(clear_gen_sort (CHead d1 (Bind Abbr) u) n H4 (\forall (c2: C).((csuba g 
c1 c2) \to (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u))) 
(\lambda (d2: C).(csuba g d1 d2)))))))) | (CHead c k t) \Rightarrow (\lambda 
(H3: (drop i O c1 (CHead c k t))).(\lambda (H4: (clear (CHead c k t) (CHead 
d1 (Bind Abbr) u))).((match k in K return (\lambda (k0: K).((drop i O c1 
(CHead c k0 t)) \to ((clear (CHead c k0 t) (CHead d1 (Bind Abbr) u)) \to 
(\forall (c2: C).((csuba g c1 c2) \to (ex2 C (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)))))))) with 
[(Bind b) \Rightarrow (\lambda (H5: (drop i O c1 (CHead c (Bind b) 
t))).(\lambda (H6: (clear (CHead c (Bind b) t) (CHead d1 (Bind Abbr) 
u))).(let H7 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow d1 | (CHead c0 _ _) \Rightarrow c0])) 
(CHead d1 (Bind Abbr) u) (CHead c (Bind b) t) (clear_gen_bind b c (CHead d1 
(Bind Abbr) u) t H6)) in ((let H8 \def (f_equal C B (\lambda (e: C).(match e 
in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k0 
_) \Rightarrow (match k0 in K return (\lambda (_: K).B) with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) (CHead d1 (Bind Abbr) u) 
(CHead c (Bind b) t) (clear_gen_bind b c (CHead d1 (Bind Abbr) u) t H6)) in 
((let H9 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: 
C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) (CHead 
d1 (Bind Abbr) u) (CHead c (Bind b) t) (clear_gen_bind b c (CHead d1 (Bind 
Abbr) u) t H6)) in (\lambda (H10: (eq B Abbr b)).(\lambda (H11: (eq C d1 
c)).(\lambda (c2: C).(\lambda (H12: (csuba g c1 c2)).(let H13 \def (eq_ind_r 
T t (\lambda (t0: T).(drop i O c1 (CHead c (Bind b) t0))) H5 u H9) in (let 
H14 \def (eq_ind_r B b (\lambda (b0: B).(drop i O c1 (CHead c (Bind b0) u))) 
H13 Abbr H10) in (let H15 \def (eq_ind_r C c (\lambda (c0: C).(drop i O c1 
(CHead c0 (Bind Abbr) u))) H14 d1 H11) in (let H16 \def (csuba_drop_abbr i c1 
d1 u H15 g c2 H12) in (ex2_ind C (\lambda (d2: C).(drop i O c2 (CHead d2 
(Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)) (ex2 C (\lambda (d2: 
C).(getl i c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))) 
(\lambda (x0: C).(\lambda (H17: (drop i O c2 (CHead x0 (Bind Abbr) 
u))).(\lambda (H18: (csuba g d1 x0)).(ex_intro2 C (\lambda (d2: C).(getl i c2 
(CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)) x0 (getl_intro i 
c2 (CHead x0 (Bind Abbr) u) (CHead x0 (Bind Abbr) u) H17 (clear_bind Abbr x0 
u)) H18)))) H16)))))))))) H8)) H7)))) | (Flat f) \Rightarrow (\lambda (H5: 
(drop i O c1 (CHead c (Flat f) t))).(\lambda (H6: (clear (CHead c (Flat f) t) 
(CHead d1 (Bind Abbr) u))).(let H7 \def H5 in (unintro C c1 (\lambda (c0: 
C).((drop i O c0 (CHead c (Flat f) t)) \to (\forall (c2: C).((csuba g c0 c2) 
\to (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abbr) u))) (\lambda 
(d2: C).(csuba g d1 d2))))))) (nat_ind (\lambda (n: nat).(\forall (x0: 
C).((drop n O x0 (CHead c (Flat f) t)) \to (\forall (c2: C).((csuba g x0 c2) 
\to (ex2 C (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abbr) u))) (\lambda 
(d2: C).(csuba g d1 d2)))))))) (\lambda (x0: C).(\lambda (H8: (drop O O x0 
(CHead c (Flat f) t))).(\lambda (c2: C).(\lambda (H9: (csuba g x0 c2)).(let 
H10 \def (eq_ind C x0 (\lambda (c0: C).(csuba g c0 c2)) H9 (CHead c (Flat f) 
t) (drop_gen_refl x0 (CHead c (Flat f) t) H8)) in (let H_y \def (clear_flat c 
(CHead d1 (Bind Abbr) u) (clear_gen_flat f c (CHead d1 (Bind Abbr) u) t H6) f 
t) in (let H11 \def (csuba_clear_conf g (CHead c (Flat f) t) c2 H10 (CHead d1 
(Bind Abbr) u) H_y) in (ex2_ind C (\lambda (e2: C).(csuba g (CHead d1 (Bind 
Abbr) u) e2)) (\lambda (e2: C).(clear c2 e2)) (ex2 C (\lambda (d2: C).(getl O 
c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))) (\lambda 
(x1: C).(\lambda (H12: (csuba g (CHead d1 (Bind Abbr) u) x1)).(\lambda (H13: 
(clear c2 x1)).(let H14 \def (csuba_gen_abbr g d1 x1 u H12) in (ex2_ind C 
(\lambda (d2: C).(eq C x1 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba 
g d1 d2)) (ex2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abbr) u))) 
(\lambda (d2: C).(csuba g d1 d2))) (\lambda (x2: C).(\lambda (H15: (eq C x1 
(CHead x2 (Bind Abbr) u))).(\lambda (H16: (csuba g d1 x2)).(let H17 \def 
(eq_ind C x1 (\lambda (c0: C).(clear c2 c0)) H13 (CHead x2 (Bind Abbr) u) 
H15) in (ex_intro2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abbr) u))) 
(\lambda (d2: C).(csuba g d1 d2)) x2 (getl_intro O c2 (CHead x2 (Bind Abbr) 
u) c2 (drop_refl c2) H17) H16))))) H14))))) H11)))))))) (\lambda (n: 
nat).(\lambda (H8: ((\forall (x0: C).((drop n O x0 (CHead c (Flat f) t)) \to 
(\forall (c2: C).((csuba g x0 c2) \to (ex2 C (\lambda (d2: C).(getl n c2 
(CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))))))))).(\lambda 
(x0: C).(\lambda (H9: (drop (S n) O x0 (CHead c (Flat f) t))).(\lambda (c2: 
C).(\lambda (H10: (csuba g x0 c2)).(let H11 \def (drop_clear x0 (CHead c 
(Flat f) t) n H9) in (ex2_3_ind B C T (\lambda (b: B).(\lambda (e: 
C).(\lambda (v: T).(clear x0 (CHead e (Bind b) v))))) (\lambda (_: 
B).(\lambda (e: C).(\lambda (_: T).(drop n O e (CHead c (Flat f) t))))) (ex2 
C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: 
C).(csuba g d1 d2))) (\lambda (x1: B).(\lambda (x2: C).(\lambda (x3: 
T).(\lambda (H12: (clear x0 (CHead x2 (Bind x1) x3))).(\lambda (H13: (drop n 
O x2 (CHead c (Flat f) t))).(let H14 \def (csuba_clear_conf g x0 c2 H10 
(CHead x2 (Bind x1) x3) H12) in (ex2_ind C (\lambda (e2: C).(csuba g (CHead 
x2 (Bind x1) x3) e2)) (\lambda (e2: C).(clear c2 e2)) (ex2 C (\lambda (d2: 
C).(getl (S n) c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 
d2))) (\lambda (x4: C).(\lambda (H15: (csuba g (CHead x2 (Bind x1) x3) 
x4)).(\lambda (H16: (clear c2 x4)).(let H17 \def (csuba_gen_bind g x1 x2 x4 
x3 H15) in (ex2_3_ind B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: 
T).(eq C x4 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csuba g x2 e2)))) (ex2 C (\lambda (d2: C).(getl (S n) c2 
(CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))) (\lambda (x5: 
B).(\lambda (x6: C).(\lambda (x7: T).(\lambda (H18: (eq C x4 (CHead x6 (Bind 
x5) x7))).(\lambda (H19: (csuba g x2 x6)).(let H20 \def (eq_ind C x4 (\lambda 
(c0: C).(clear c2 c0)) H16 (CHead x6 (Bind x5) x7) H18) in (let H21 \def (H8 
x2 H13 x6 H19) in (ex2_ind C (\lambda (d2: C).(getl n x6 (CHead d2 (Bind 
Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)) (ex2 C (\lambda (d2: C).(getl (S 
n) c2 (CHead d2 (Bind Abbr) u))) (\lambda (d2: C).(csuba g d1 d2))) (\lambda 
(x8: C).(\lambda (H22: (getl n x6 (CHead x8 (Bind Abbr) u))).(\lambda (H23: 
(csuba g d1 x8)).(ex_intro2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind 
Abbr) u))) (\lambda (d2: C).(csuba g d1 d2)) x8 (getl_clear_bind x5 c2 x6 x7 
H20 (CHead x8 (Bind Abbr) u) n H22) H23)))) H21)))))))) H17))))) H14))))))) 
H11)))))))) i) H7))))]) H3 H4)))]) H1 H2)))) H0))))))).

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
x (CHead d1 (Bind Abst) u1))).((match x in C return (\lambda (c: C).((drop i 
O c1 c) \to ((clear c (CHead d1 (Bind Abst) u1)) \to (\forall (c2: C).((csuba 
g c1 c2) \to (or (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) 
u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))))))))) 
with [(CSort n) \Rightarrow (\lambda (_: (drop i O c1 (CSort n))).(\lambda 
(H4: (clear (CSort n) (CHead d1 (Bind Abst) u1))).(clear_gen_sort (CHead d1 
(Bind Abst) u1) n H4 (\forall (c2: C).((csuba g c1 c2) \to (or (ex2 C 
(\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(getl i c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a))))))))))) | (CHead c k t) 
\Rightarrow (\lambda (H3: (drop i O c1 (CHead c k t))).(\lambda (H4: (clear 
(CHead c k t) (CHead d1 (Bind Abst) u1))).((match k in K return (\lambda (k0: 
K).((drop i O c1 (CHead c k0 t)) \to ((clear (CHead c k0 t) (CHead d1 (Bind 
Abst) u1)) \to (\forall (c2: C).((csuba g c1 c2) \to (or (ex2 C (\lambda (d2: 
C).(getl i c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a))))))))))) with [(Bind b) \Rightarrow (\lambda (H5: (drop 
i O c1 (CHead c (Bind b) t))).(\lambda (H6: (clear (CHead c (Bind b) t) 
(CHead d1 (Bind Abst) u1))).(let H7 \def (f_equal C C (\lambda (e: C).(match 
e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d1 | (CHead c0 _ 
_) \Rightarrow c0])) (CHead d1 (Bind Abst) u1) (CHead c (Bind b) t) 
(clear_gen_bind b c (CHead d1 (Bind Abst) u1) t H6)) in ((let H8 \def 
(f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow Abst | (CHead _ k0 _) \Rightarrow (match k0 in K 
return (\lambda (_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) 
\Rightarrow Abst])])) (CHead d1 (Bind Abst) u1) (CHead c (Bind b) t) 
(clear_gen_bind b c (CHead d1 (Bind Abst) u1) t H6)) in ((let H9 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u1 | (CHead _ _ t0) \Rightarrow t0])) (CHead d1 (Bind 
Abst) u1) (CHead c (Bind b) t) (clear_gen_bind b c (CHead d1 (Bind Abst) u1) 
t H6)) in (\lambda (H10: (eq B Abst b)).(\lambda (H11: (eq C d1 c)).(\lambda 
(c2: C).(\lambda (H12: (csuba g c1 c2)).(let H13 \def (eq_ind_r T t (\lambda 
(t0: T).(drop i O c1 (CHead c (Bind b) t0))) H5 u1 H9) in (let H14 \def 
(eq_ind_r B b (\lambda (b0: B).(drop i O c1 (CHead c (Bind b0) u1))) H13 Abst 
H10) in (let H15 \def (eq_ind_r C c (\lambda (c0: C).(drop i O c1 (CHead c0 
(Bind Abst) u1))) H14 d1 H11) in (let H16 \def (csuba_drop_abst i c1 d1 u1 
H15 g c2 H12) in (or_ind (ex2 C (\lambda (d2: C).(drop i O c2 (CHead d2 (Bind 
Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(drop i O c2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))) (or (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abbr) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda 
(H17: (ex2 C (\lambda (d2: C).(drop i O c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2)))).(ex2_ind C (\lambda (d2: C).(drop i O c2 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2)) (or (ex2 C 
(\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(getl i c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (x0: C).(\lambda 
(H18: (drop i O c2 (CHead x0 (Bind Abst) u1))).(\lambda (H19: (csuba g d1 
x0)).(or_introl (ex2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) 
u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abbr) u2))))) 
(\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda 
(_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))) 
(ex_intro2 C (\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u1))) (\lambda 
(d2: C).(csuba g d1 d2)) x0 (getl_intro i c2 (CHead x0 (Bind Abst) u1) (CHead 
x0 (Bind Abst) u1) H18 (clear_bind Abst x0 u1)) H19))))) H17)) (\lambda (H17: 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(drop i O c2 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(drop i O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))) (or (ex2 C 
(\lambda (d2: C).(getl i c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(getl i c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (x2: A).(\lambda (H18: (drop i O c2 (CHead x0 (Bind Abbr) 
x1))).(\lambda (H19: (csuba g d1 x0)).(\lambda (H20: (arity g d1 u1 (asucc g 
x2))).(\lambda (H21: (arity g x0 x1 x2)).(or_intror (ex2 C (\lambda (d2: 
C).(getl i c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i c2 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a))))) (ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(getl i c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))) x0 x1 x2 
(getl_intro i c2 (CHead x0 (Bind Abbr) x1) (CHead x0 (Bind Abbr) x1) H18 
(clear_bind Abbr x0 x1)) H19 H20 H21))))))))) H17)) H16)))))))))) H8)) H7)))) 
| (Flat f) \Rightarrow (\lambda (H5: (drop i O c1 (CHead c (Flat f) 
t))).(\lambda (H6: (clear (CHead c (Flat f) t) (CHead d1 (Bind Abst) 
u1))).(let H7 \def H5 in (unintro C c1 (\lambda (c0: C).((drop i O c0 (CHead 
c (Flat f) t)) \to (\forall (c2: C).((csuba g c0 c2) \to (or (ex2 C (\lambda 
(d2: C).(getl i c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl i 
c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: 
A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(a: A).(arity g d2 u2 a)))))))))) (nat_ind (\lambda (n: nat).(\forall (x0: 
C).((drop n O x0 (CHead c (Flat f) t)) \to (\forall (c2: C).((csuba g x0 c2) 
\to (or (ex2 C (\lambda (d2: C).(getl n c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl n c2 (CHead d2 (Bind Abbr) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))))))))) (\lambda 
(x0: C).(\lambda (H8: (drop O O x0 (CHead c (Flat f) t))).(\lambda (c2: 
C).(\lambda (H9: (csuba g x0 c2)).(let H10 \def (eq_ind C x0 (\lambda (c0: 
C).(csuba g c0 c2)) H9 (CHead c (Flat f) t) (drop_gen_refl x0 (CHead c (Flat 
f) t) H8)) in (let H_y \def (clear_flat c (CHead d1 (Bind Abst) u1) 
(clear_gen_flat f c (CHead d1 (Bind Abst) u1) t H6) f t) in (let H11 \def 
(csuba_clear_conf g (CHead c (Flat f) t) c2 H10 (CHead d1 (Bind Abst) u1) 
H_y) in (ex2_ind C (\lambda (e2: C).(csuba g (CHead d1 (Bind Abst) u1) e2)) 
(\lambda (e2: C).(clear c2 e2)) (or (ex2 C (\lambda (d2: C).(getl O c2 (CHead 
d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O c2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))) (\lambda (x1: C).(\lambda (H12: (csuba g (CHead d1 (Bind Abst) u1) 
x1)).(\lambda (H13: (clear c2 x1)).(let H14 \def (csuba_gen_abst g d1 x1 u1 
H12) in (or_ind (ex2 C (\lambda (d2: C).(eq C x1 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(eq C x1 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (or (ex2 C 
(\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(getl O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (H15: (ex2 C (\lambda 
(d2: C).(eq C x1 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2)))).(ex2_ind C (\lambda (d2: C).(eq C x1 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2)) (or (ex2 C (\lambda (d2: C).(getl O c2 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O c2 (CHead d2 (Bind 
Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 
d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc 
g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))) (\lambda (x2: C).(\lambda (H16: (eq C x1 (CHead x2 (Bind Abst) 
u1))).(\lambda (H17: (csuba g d1 x2)).(let H18 \def (eq_ind C x1 (\lambda 
(c0: C).(clear c2 c0)) H13 (CHead x2 (Bind Abst) u1) H16) in (or_introl (ex2 
C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: 
C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(_: A).(getl O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (ex_intro2 C (\lambda (d2: 
C).(getl O c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2)) 
x2 (getl_intro O c2 (CHead x2 (Bind Abst) u1) c2 (drop_refl c2) H18) 
H17)))))) H15)) (\lambda (H15: (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: 
T).(\lambda (_: A).(eq C x1 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: 
C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))).(ex4_3_ind C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(eq C x1 (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
(asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 
u2 a)))) (or (ex2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (x2: 
C).(\lambda (x3: T).(\lambda (x4: A).(\lambda (H16: (eq C x1 (CHead x2 (Bind 
Abbr) x3))).(\lambda (H17: (csuba g d1 x2)).(\lambda (H18: (arity g d1 u1 
(asucc g x4))).(\lambda (H19: (arity g x2 x3 x4)).(let H20 \def (eq_ind C x1 
(\lambda (c0: C).(clear c2 c0)) H13 (CHead x2 (Bind Abbr) x3) H16) in 
(or_intror (ex2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl O c2 (CHead d2 (Bind Abbr) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a))))) (ex4_3_intro C 
T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl O c2 (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
(asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 
u2 a)))) x2 x3 x4 (getl_intro O c2 (CHead x2 (Bind Abbr) x3) c2 (drop_refl 
c2) H20) H17 H18 H19)))))))))) H15)) H14))))) H11)))))))) (\lambda (n: 
nat).(\lambda (H8: ((\forall (x0: C).((drop n O x0 (CHead c (Flat f) t)) \to 
(\forall (c2: C).((csuba g x0 c2) \to (or (ex2 C (\lambda (d2: C).(getl n c2 
(CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl n c2 (CHead d2 (Bind 
Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 
d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc 
g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))))))))).(\lambda (x0: C).(\lambda (H9: (drop (S n) O x0 (CHead c (Flat 
f) t))).(\lambda (c2: C).(\lambda (H10: (csuba g x0 c2)).(let H11 \def 
(drop_clear x0 (CHead c (Flat f) t) n H9) in (ex2_3_ind B C T (\lambda (b: 
B).(\lambda (e: C).(\lambda (v: T).(clear x0 (CHead e (Bind b) v))))) 
(\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop n O e (CHead c (Flat f) 
t))))) (or (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abbr) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (x1: 
B).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H12: (clear x0 (CHead x2 (Bind 
x1) x3))).(\lambda (H13: (drop n O x2 (CHead c (Flat f) t))).(let H14 \def 
(csuba_clear_conf g x0 c2 H10 (CHead x2 (Bind x1) x3) H12) in (ex2_ind C 
(\lambda (e2: C).(csuba g (CHead x2 (Bind x1) x3) e2)) (\lambda (e2: 
C).(clear c2 e2)) (or (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind 
Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: 
C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))) (\lambda (x4: C).(\lambda (H15: (csuba g (CHead x2 (Bind x1) x3) 
x4)).(\lambda (H16: (clear c2 x4)).(let H17 \def (csuba_gen_bind g x1 x2 x4 
x3 H15) in (ex2_3_ind B C T (\lambda (b2: B).(\lambda (e2: C).(\lambda (v2: 
T).(eq C x4 (CHead e2 (Bind b2) v2))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (_: T).(csuba g x2 e2)))) (or (ex2 C (\lambda (d2: C).(getl (S n) 
c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T 
A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 
(Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g 
d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 
(asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 
u2 a)))))) (\lambda (x5: B).(\lambda (x6: C).(\lambda (x7: T).(\lambda (H18: 
(eq C x4 (CHead x6 (Bind x5) x7))).(\lambda (H19: (csuba g x2 x6)).(let H20 
\def (eq_ind C x4 (\lambda (c0: C).(clear c2 c0)) H16 (CHead x6 (Bind x5) x7) 
H18) in (let H21 \def (H8 x2 H13 x6 H19) in (or_ind (ex2 C (\lambda (d2: 
C).(getl n x6 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) 
(ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl n x6 
(CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: 
A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity 
g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: 
A).(arity g d2 u2 a))))) (or (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))) (\lambda (H22: (ex2 C (\lambda (d2: C).(getl n x6 (CHead d2 (Bind 
Abst) u1))) (\lambda (d2: C).(csuba g d1 d2)))).(ex2_ind C (\lambda (d2: 
C).(getl n x6 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2)) 
(or (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abst) u1))) 
(\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abbr) u2))))) (\lambda 
(d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: 
C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 a)))))) (\lambda (x8: 
C).(\lambda (H23: (getl n x6 (CHead x8 (Bind Abst) u1))).(\lambda (H24: 
(csuba g d1 x8)).(or_introl (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 
(Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))) (ex_intro2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind Abst) 
u1))) (\lambda (d2: C).(csuba g d1 d2)) x8 (getl_clear_bind x5 c2 x6 x7 H20 
(CHead x8 (Bind Abst) u1) n H23) H24))))) H22)) (\lambda (H22: (ex4_3 C T A 
(\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl n x6 (CHead d2 (Bind 
Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 
d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc 
g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a)))))).(ex4_3_ind C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(getl n x6 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))) (or (ex2 C (\lambda (d2: 
C).(getl (S n) c2 (CHead d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 
d2))) (ex4_3 C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S 
n) c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda 
(_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: T).(\lambda (a: 
A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda 
(a: A).(arity g d2 u2 a)))))) (\lambda (x8: C).(\lambda (x9: T).(\lambda 
(x10: A).(\lambda (H23: (getl n x6 (CHead x8 (Bind Abbr) x9))).(\lambda (H24: 
(csuba g d1 x8)).(\lambda (H25: (arity g d1 u1 (asucc g x10))).(\lambda (H26: 
(arity g x8 x9 x10)).(or_intror (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead 
d2 (Bind Abst) u1))) (\lambda (d2: C).(csuba g d1 d2))) (ex4_3 C T A (\lambda 
(d2: C).(\lambda (u2: T).(\lambda (_: A).(getl (S n) c2 (CHead d2 (Bind Abbr) 
u2))))) (\lambda (d2: C).(\lambda (_: T).(\lambda (_: A).(csuba g d1 d2)))) 
(\lambda (_: C).(\lambda (_: T).(\lambda (a: A).(arity g d1 u1 (asucc g 
a))))) (\lambda (d2: C).(\lambda (u2: T).(\lambda (a: A).(arity g d2 u2 
a))))) (ex4_3_intro C T A (\lambda (d2: C).(\lambda (u2: T).(\lambda (_: 
A).(getl (S n) c2 (CHead d2 (Bind Abbr) u2))))) (\lambda (d2: C).(\lambda (_: 
T).(\lambda (_: A).(csuba g d1 d2)))) (\lambda (_: C).(\lambda (_: 
T).(\lambda (a: A).(arity g d1 u1 (asucc g a))))) (\lambda (d2: C).(\lambda 
(u2: T).(\lambda (a: A).(arity g d2 u2 a)))) x8 x9 x10 (getl_clear_bind x5 c2 
x6 x7 H20 (CHead x8 (Bind Abbr) x9) n H23) H24 H25 H26))))))))) H22)) 
H21)))))))) H17))))) H14))))))) H11)))))))) i) H7))))]) H3 H4)))]) H1 H2)))) 
H0))))))).

