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

include "Basic-1/csubst1/props.ma".

include "Basic-1/csubst0/getl.ma".

include "Basic-1/subst1/props.ma".

include "Basic-1/drop/props.ma".

theorem csubst1_getl_ge:
 \forall (i: nat).(\forall (n: nat).((le i n) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (v: T).((csubst1 i v c1 c2) \to (\forall (e: C).((getl n c1 
e) \to (getl n c2 e)))))))))
\def
 \lambda (i: nat).(\lambda (n: nat).(\lambda (H: (le i n)).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (v: T).(\lambda (H0: (csubst1 i v c1 
c2)).(csubst1_ind i v c1 (\lambda (c: C).(\forall (e: C).((getl n c1 e) \to 
(getl n c e)))) (\lambda (e: C).(\lambda (H1: (getl n c1 e)).H1)) (\lambda 
(c3: C).(\lambda (H1: (csubst0 i v c1 c3)).(\lambda (e: C).(\lambda (H2: 
(getl n c1 e)).(csubst0_getl_ge i n H c1 c3 v H1 e H2))))) c2 H0))))))).
(* COMMENTS
Initial nodes: 111
END *)

theorem csubst1_getl_lt:
 \forall (i: nat).(\forall (n: nat).((lt n i) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (v: T).((csubst1 i v c1 c2) \to (\forall (e1: C).((getl n c1 
e1) \to (ex2 C (\lambda (e2: C).(csubst1 (minus i n) v e1 e2)) (\lambda (e2: 
C).(getl n c2 e2)))))))))))
\def
 \lambda (i: nat).(\lambda (n: nat).(\lambda (H: (lt n i)).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (v: T).(\lambda (H0: (csubst1 i v c1 
c2)).(csubst1_ind i v c1 (\lambda (c: C).(\forall (e1: C).((getl n c1 e1) \to 
(ex2 C (\lambda (e2: C).(csubst1 (minus i n) v e1 e2)) (\lambda (e2: C).(getl 
n c e2)))))) (\lambda (e1: C).(\lambda (H1: (getl n c1 e1)).(eq_ind_r nat (S 
(minus i (S n))) (\lambda (n0: nat).(ex2 C (\lambda (e2: C).(csubst1 n0 v e1 
e2)) (\lambda (e2: C).(getl n c1 e2)))) (ex_intro2 C (\lambda (e2: 
C).(csubst1 (S (minus i (S n))) v e1 e2)) (\lambda (e2: C).(getl n c1 e2)) e1 
(csubst1_refl (S (minus i (S n))) v e1) H1) (minus i n) (minus_x_Sy i n H)))) 
(\lambda (c3: C).(\lambda (H1: (csubst0 i v c1 c3)).(\lambda (e1: C).(\lambda 
(H2: (getl n c1 e1)).(eq_ind_r nat (S (minus i (S n))) (\lambda (n0: 
nat).(ex2 C (\lambda (e2: C).(csubst1 n0 v e1 e2)) (\lambda (e2: C).(getl n 
c3 e2)))) (let H3 \def (csubst0_getl_lt i n H c1 c3 v H1 e1 H2) in (or4_ind 
(getl n c3 e1) (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e1 (CHead e0 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c3 (CHead e0 
(Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e2: C).(\lambda (_: C).(\lambda (u: T).(eq C e1 (CHead e2 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e3: C).(\lambda (u: 
T).(getl n c3 (CHead e3 (Bind b) u)))))) (\lambda (_: B).(\lambda (e2: 
C).(\lambda (e3: C).(\lambda (_: T).(csubst0 (minus i (S n)) v e2 e3)))))) 
(ex4_5 B C C T T (\lambda (b: B).(\lambda (e2: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e1 (CHead e2 (Bind b) u))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e3: C).(\lambda (_: T).(\lambda (w: T).(getl n 
c3 (CHead e3 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) 
(\lambda (_: B).(\lambda (e2: C).(\lambda (e3: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e2 e3))))))) (ex2 C (\lambda (e2: 
C).(csubst1 (S (minus i (S n))) v e1 e2)) (\lambda (e2: C).(getl n c3 e2))) 
(\lambda (H4: (getl n c3 e1)).(ex_intro2 C (\lambda (e2: C).(csubst1 (S 
(minus i (S n))) v e1 e2)) (\lambda (e2: C).(getl n c3 e2)) e1 (csubst1_refl 
(S (minus i (S n))) v e1) H4)) (\lambda (H4: (ex3_4 B C T T (\lambda (b: 
B).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e1 (CHead e0 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c3 (CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u 
w))))))).(ex3_4_ind B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e1 (CHead e0 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c3 (CHead e0 
(Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w))))) (ex2 C (\lambda (e2: C).(csubst1 (S 
(minus i (S n))) v e1 e2)) (\lambda (e2: C).(getl n c3 e2))) (\lambda (x0: 
B).(\lambda (x1: C).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H5: (eq C e1 
(CHead x1 (Bind x0) x2))).(\lambda (H6: (getl n c3 (CHead x1 (Bind x0) 
x3))).(\lambda (H7: (subst0 (minus i (S n)) v x2 x3)).(eq_ind_r C (CHead x1 
(Bind x0) x2) (\lambda (c: C).(ex2 C (\lambda (e2: C).(csubst1 (S (minus i (S 
n))) v c e2)) (\lambda (e2: C).(getl n c3 e2)))) (ex_intro2 C (\lambda (e2: 
C).(csubst1 (S (minus i (S n))) v (CHead x1 (Bind x0) x2) e2)) (\lambda (e2: 
C).(getl n c3 e2)) (CHead x1 (Bind x0) x3) (csubst1_sing (S (minus i (S n))) 
v (CHead x1 (Bind x0) x2) (CHead x1 (Bind x0) x3) (csubst0_snd_bind x0 (minus 
i (S n)) v x2 x3 H7 x1)) H6) e1 H5)))))))) H4)) (\lambda (H4: (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e2: C).(\lambda (_: C).(\lambda (u: T).(eq C e1 
(CHead e2 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e3: 
C).(\lambda (u: T).(getl n c3 (CHead e3 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e2: C).(\lambda (e3: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e2 e3))))))).(ex3_4_ind B C C T (\lambda (b: B).(\lambda (e2: C).(\lambda 
(_: C).(\lambda (u: T).(eq C e1 (CHead e2 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e3: C).(\lambda (u: T).(getl n c3 (CHead e3 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (e3: C).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e2 e3))))) (ex2 C (\lambda (e2: C).(csubst1 
(S (minus i (S n))) v e1 e2)) (\lambda (e2: C).(getl n c3 e2))) (\lambda (x0: 
B).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H5: (eq C e1 
(CHead x1 (Bind x0) x3))).(\lambda (H6: (getl n c3 (CHead x2 (Bind x0) 
x3))).(\lambda (H7: (csubst0 (minus i (S n)) v x1 x2)).(eq_ind_r C (CHead x1 
(Bind x0) x3) (\lambda (c: C).(ex2 C (\lambda (e2: C).(csubst1 (S (minus i (S 
n))) v c e2)) (\lambda (e2: C).(getl n c3 e2)))) (ex_intro2 C (\lambda (e2: 
C).(csubst1 (S (minus i (S n))) v (CHead x1 (Bind x0) x3) e2)) (\lambda (e2: 
C).(getl n c3 e2)) (CHead x2 (Bind x0) x3) (csubst1_sing (S (minus i (S n))) 
v (CHead x1 (Bind x0) x3) (CHead x2 (Bind x0) x3) (csubst0_fst_bind x0 (minus 
i (S n)) x1 x2 v H7 x3)) H6) e1 H5)))))))) H4)) (\lambda (H4: (ex4_5 B C C T 
T (\lambda (b: B).(\lambda (e2: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e1 (CHead e2 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e3: C).(\lambda (_: T).(\lambda (w: T).(getl n c3 (CHead e3 
(Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: 
B).(\lambda (e2: C).(\lambda (e3: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus i (S n)) v e2 e3)))))))).(ex4_5_ind B C C T T (\lambda (b: B).(\lambda 
(e2: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e1 (CHead e2 
(Bind b) u))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e3: C).(\lambda 
(_: T).(\lambda (w: T).(getl n c3 (CHead e3 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus i (S n)) v u w)))))) (\lambda (_: B).(\lambda (e2: C).(\lambda (e3: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) v e2 e3)))))) 
(ex2 C (\lambda (e2: C).(csubst1 (S (minus i (S n))) v e1 e2)) (\lambda (e2: 
C).(getl n c3 e2))) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: 
C).(\lambda (x3: T).(\lambda (x4: T).(\lambda (H5: (eq C e1 (CHead x1 (Bind 
x0) x3))).(\lambda (H6: (getl n c3 (CHead x2 (Bind x0) x4))).(\lambda (H7: 
(subst0 (minus i (S n)) v x3 x4)).(\lambda (H8: (csubst0 (minus i (S n)) v x1 
x2)).(eq_ind_r C (CHead x1 (Bind x0) x3) (\lambda (c: C).(ex2 C (\lambda (e2: 
C).(csubst1 (S (minus i (S n))) v c e2)) (\lambda (e2: C).(getl n c3 e2)))) 
(ex_intro2 C (\lambda (e2: C).(csubst1 (S (minus i (S n))) v (CHead x1 (Bind 
x0) x3) e2)) (\lambda (e2: C).(getl n c3 e2)) (CHead x2 (Bind x0) x4) 
(csubst1_sing (S (minus i (S n))) v (CHead x1 (Bind x0) x3) (CHead x2 (Bind 
x0) x4) (csubst0_both_bind x0 (minus i (S n)) v x3 x4 H7 x1 x2 H8)) H6) e1 
H5)))))))))) H4)) H3)) (minus i n) (minus_x_Sy i n H)))))) c2 H0))))))).
(* COMMENTS
Initial nodes: 2035
END *)

theorem csubst1_getl_ge_back:
 \forall (i: nat).(\forall (n: nat).((le i n) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (v: T).((csubst1 i v c1 c2) \to (\forall (e: C).((getl n c2 
e) \to (getl n c1 e)))))))))
\def
 \lambda (i: nat).(\lambda (n: nat).(\lambda (H: (le i n)).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (v: T).(\lambda (H0: (csubst1 i v c1 
c2)).(csubst1_ind i v c1 (\lambda (c: C).(\forall (e: C).((getl n c e) \to 
(getl n c1 e)))) (\lambda (e: C).(\lambda (H1: (getl n c1 e)).H1)) (\lambda 
(c3: C).(\lambda (H1: (csubst0 i v c1 c3)).(\lambda (e: C).(\lambda (H2: 
(getl n c3 e)).(csubst0_getl_ge_back i n H c1 c3 v H1 e H2))))) c2 H0))))))).
(* COMMENTS
Initial nodes: 111
END *)

theorem getl_csubst1:
 \forall (d: nat).(\forall (c: C).(\forall (e: C).(\forall (u: T).((getl d c 
(CHead e (Bind Abbr) u)) \to (ex2_2 C C (\lambda (a0: C).(\lambda (_: 
C).(csubst1 d u c a0))) (\lambda (a0: C).(\lambda (a: C).(drop (S O) d a0 
a))))))))
\def
 \lambda (d: nat).(nat_ind (\lambda (n: nat).(\forall (c: C).(\forall (e: 
C).(\forall (u: T).((getl n c (CHead e (Bind Abbr) u)) \to (ex2_2 C C 
(\lambda (a0: C).(\lambda (_: C).(csubst1 n u c a0))) (\lambda (a0: 
C).(\lambda (a: C).(drop (S O) n a0 a))))))))) (\lambda (c: C).(C_ind 
(\lambda (c0: C).(\forall (e: C).(\forall (u: T).((getl O c0 (CHead e (Bind 
Abbr) u)) \to (ex2_2 C C (\lambda (a0: C).(\lambda (_: C).(csubst1 O u c0 
a0))) (\lambda (a0: C).(\lambda (a: C).(drop (S O) O a0 a)))))))) (\lambda 
(n: nat).(\lambda (e: C).(\lambda (u: T).(\lambda (H: (getl O (CSort n) 
(CHead e (Bind Abbr) u))).(getl_gen_sort n O (CHead e (Bind Abbr) u) H (ex2_2 
C C (\lambda (a0: C).(\lambda (_: C).(csubst1 O u (CSort n) a0))) (\lambda 
(a0: C).(\lambda (a: C).(drop (S O) O a0 a))))))))) (\lambda (c0: C).(\lambda 
(H: ((\forall (e: C).(\forall (u: T).((getl O c0 (CHead e (Bind Abbr) u)) \to 
(ex2_2 C C (\lambda (a0: C).(\lambda (_: C).(csubst1 O u c0 a0))) (\lambda 
(a0: C).(\lambda (a: C).(drop (S O) O a0 a))))))))).(\lambda (k: K).(K_ind 
(\lambda (k0: K).(\forall (t: T).(\forall (e: C).(\forall (u: T).((getl O 
(CHead c0 k0 t) (CHead e (Bind Abbr) u)) \to (ex2_2 C C (\lambda (a0: 
C).(\lambda (_: C).(csubst1 O u (CHead c0 k0 t) a0))) (\lambda (a0: 
C).(\lambda (a: C).(drop (S O) O a0 a))))))))) (\lambda (b: B).(\lambda (t: 
T).(\lambda (e: C).(\lambda (u: T).(\lambda (H0: (getl O (CHead c0 (Bind b) 
t) (CHead e (Bind Abbr) u))).(let H1 \def (f_equal C C (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow e | 
(CHead c1 _ _) \Rightarrow c1])) (CHead e (Bind Abbr) u) (CHead c0 (Bind b) 
t) (clear_gen_bind b c0 (CHead e (Bind Abbr) u) t (getl_gen_O (CHead c0 (Bind 
b) t) (CHead e (Bind Abbr) u) H0))) in ((let H2 \def (f_equal C B (\lambda 
(e0: C).(match e0 in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow 
Abbr | (CHead _ k0 _) \Rightarrow (match k0 in K return (\lambda (_: K).B) 
with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) (CHead e 
(Bind Abbr) u) (CHead c0 (Bind b) t) (clear_gen_bind b c0 (CHead e (Bind 
Abbr) u) t (getl_gen_O (CHead c0 (Bind b) t) (CHead e (Bind Abbr) u) H0))) in 
((let H3 \def (f_equal C T (\lambda (e0: C).(match e0 in C return (\lambda 
(_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) 
(CHead e (Bind Abbr) u) (CHead c0 (Bind b) t) (clear_gen_bind b c0 (CHead e 
(Bind Abbr) u) t (getl_gen_O (CHead c0 (Bind b) t) (CHead e (Bind Abbr) u) 
H0))) in (\lambda (H4: (eq B Abbr b)).(\lambda (_: (eq C e c0)).(eq_ind_r T t 
(\lambda (t0: T).(ex2_2 C C (\lambda (a0: C).(\lambda (_: C).(csubst1 O t0 
(CHead c0 (Bind b) t) a0))) (\lambda (a0: C).(\lambda (a: C).(drop (S O) O a0 
a))))) (eq_ind B Abbr (\lambda (b0: B).(ex2_2 C C (\lambda (a0: C).(\lambda 
(_: C).(csubst1 O t (CHead c0 (Bind b0) t) a0))) (\lambda (a0: C).(\lambda 
(a: C).(drop (S O) O a0 a))))) (ex2_2_intro C C (\lambda (a0: C).(\lambda (_: 
C).(csubst1 O t (CHead c0 (Bind Abbr) t) a0))) (\lambda (a0: C).(\lambda (a: 
C).(drop (S O) O a0 a))) (CHead c0 (Bind Abbr) t) c0 (csubst1_refl O t (CHead 
c0 (Bind Abbr) t)) (drop_drop (Bind Abbr) O c0 c0 (drop_refl c0) t)) b H4) u 
H3)))) H2)) H1))))))) (\lambda (f: F).(\lambda (t: T).(\lambda (e: 
C).(\lambda (u: T).(\lambda (H0: (getl O (CHead c0 (Flat f) t) (CHead e (Bind 
Abbr) u))).(let H_x \def (subst1_ex u t O) in (let H1 \def H_x in (ex_ind T 
(\lambda (t2: T).(subst1 O u t (lift (S O) O t2))) (ex2_2 C C (\lambda (a0: 
C).(\lambda (_: C).(csubst1 O u (CHead c0 (Flat f) t) a0))) (\lambda (a0: 
C).(\lambda (a: C).(drop (S O) O a0 a)))) (\lambda (x: T).(\lambda (H2: 
(subst1 O u t (lift (S O) O x))).(let H3 \def (H e u (getl_intro O c0 (CHead 
e (Bind Abbr) u) c0 (drop_refl c0) (clear_gen_flat f c0 (CHead e (Bind Abbr) 
u) t (getl_gen_O (CHead c0 (Flat f) t) (CHead e (Bind Abbr) u) H0)))) in 
(ex2_2_ind C C (\lambda (a0: C).(\lambda (_: C).(csubst1 O u c0 a0))) 
(\lambda (a0: C).(\lambda (a: C).(drop (S O) O a0 a))) (ex2_2 C C (\lambda 
(a0: C).(\lambda (_: C).(csubst1 O u (CHead c0 (Flat f) t) a0))) (\lambda 
(a0: C).(\lambda (a: C).(drop (S O) O a0 a)))) (\lambda (x0: C).(\lambda (x1: 
C).(\lambda (H4: (csubst1 O u c0 x0)).(\lambda (H5: (drop (S O) O x0 
x1)).(ex2_2_intro C C (\lambda (a0: C).(\lambda (_: C).(csubst1 O u (CHead c0 
(Flat f) t) a0))) (\lambda (a0: C).(\lambda (a: C).(drop (S O) O a0 a))) 
(CHead x0 (Flat f) (lift (S O) O x)) x1 (csubst1_flat f O u t (lift (S O) O 
x) H2 c0 x0 H4) (drop_drop (Flat f) O x0 x1 H5 (lift (S O) O x))))))) H3)))) 
H1)))))))) k)))) c)) (\lambda (n: nat).(\lambda (H: ((\forall (c: C).(\forall 
(e: C).(\forall (u: T).((getl n c (CHead e (Bind Abbr) u)) \to (ex2_2 C C 
(\lambda (a0: C).(\lambda (_: C).(csubst1 n u c a0))) (\lambda (a0: 
C).(\lambda (a: C).(drop (S O) n a0 a)))))))))).(\lambda (c: C).(C_ind 
(\lambda (c0: C).(\forall (e: C).(\forall (u: T).((getl (S n) c0 (CHead e 
(Bind Abbr) u)) \to (ex2_2 C C (\lambda (a0: C).(\lambda (_: C).(csubst1 (S 
n) u c0 a0))) (\lambda (a0: C).(\lambda (a: C).(drop (S O) (S n) a0 a)))))))) 
(\lambda (n0: nat).(\lambda (e: C).(\lambda (u: T).(\lambda (H0: (getl (S n) 
(CSort n0) (CHead e (Bind Abbr) u))).(getl_gen_sort n0 (S n) (CHead e (Bind 
Abbr) u) H0 (ex2_2 C C (\lambda (a0: C).(\lambda (_: C).(csubst1 (S n) u 
(CSort n0) a0))) (\lambda (a0: C).(\lambda (a: C).(drop (S O) (S n) a0 
a))))))))) (\lambda (c0: C).(\lambda (H0: ((\forall (e: C).(\forall (u: 
T).((getl (S n) c0 (CHead e (Bind Abbr) u)) \to (ex2_2 C C (\lambda (a0: 
C).(\lambda (_: C).(csubst1 (S n) u c0 a0))) (\lambda (a0: C).(\lambda (a: 
C).(drop (S O) (S n) a0 a))))))))).(\lambda (k: K).(K_ind (\lambda (k0: 
K).(\forall (t: T).(\forall (e: C).(\forall (u: T).((getl (S n) (CHead c0 k0 
t) (CHead e (Bind Abbr) u)) \to (ex2_2 C C (\lambda (a0: C).(\lambda (_: 
C).(csubst1 (S n) u (CHead c0 k0 t) a0))) (\lambda (a0: C).(\lambda (a: 
C).(drop (S O) (S n) a0 a))))))))) (\lambda (b: B).(\lambda (t: T).(\lambda 
(e: C).(\lambda (u: T).(\lambda (H1: (getl (S n) (CHead c0 (Bind b) t) (CHead 
e (Bind Abbr) u))).(let H_x \def (subst1_ex u t n) in (let H2 \def H_x in 
(ex_ind T (\lambda (t2: T).(subst1 n u t (lift (S O) n t2))) (ex2_2 C C 
(\lambda (a0: C).(\lambda (_: C).(csubst1 (S n) u (CHead c0 (Bind b) t) a0))) 
(\lambda (a0: C).(\lambda (a: C).(drop (S O) (S n) a0 a)))) (\lambda (x: 
T).(\lambda (H3: (subst1 n u t (lift (S O) n x))).(let H4 \def (H c0 e u 
(getl_gen_S (Bind b) c0 (CHead e (Bind Abbr) u) t n H1)) in (ex2_2_ind C C 
(\lambda (a0: C).(\lambda (_: C).(csubst1 n u c0 a0))) (\lambda (a0: 
C).(\lambda (a: C).(drop (S O) n a0 a))) (ex2_2 C C (\lambda (a0: C).(\lambda 
(_: C).(csubst1 (S n) u (CHead c0 (Bind b) t) a0))) (\lambda (a0: C).(\lambda 
(a: C).(drop (S O) (S n) a0 a)))) (\lambda (x0: C).(\lambda (x1: C).(\lambda 
(H5: (csubst1 n u c0 x0)).(\lambda (H6: (drop (S O) n x0 x1)).(ex2_2_intro C 
C (\lambda (a0: C).(\lambda (_: C).(csubst1 (S n) u (CHead c0 (Bind b) t) 
a0))) (\lambda (a0: C).(\lambda (a: C).(drop (S O) (S n) a0 a))) (CHead x0 
(Bind b) (lift (S O) n x)) (CHead x1 (Bind b) x) (csubst1_bind b n u t (lift 
(S O) n x) H3 c0 x0 H5) (drop_skip_bind (S O) n x0 x1 H6 b x)))))) H4)))) 
H2)))))))) (\lambda (f: F).(\lambda (t: T).(\lambda (e: C).(\lambda (u: 
T).(\lambda (H1: (getl (S n) (CHead c0 (Flat f) t) (CHead e (Bind Abbr) 
u))).(let H_x \def (subst1_ex u t (S n)) in (let H2 \def H_x in (ex_ind T 
(\lambda (t2: T).(subst1 (S n) u t (lift (S O) (S n) t2))) (ex2_2 C C 
(\lambda (a0: C).(\lambda (_: C).(csubst1 (S n) u (CHead c0 (Flat f) t) a0))) 
(\lambda (a0: C).(\lambda (a: C).(drop (S O) (S n) a0 a)))) (\lambda (x: 
T).(\lambda (H3: (subst1 (S n) u t (lift (S O) (S n) x))).(let H4 \def (H0 e 
u (getl_gen_S (Flat f) c0 (CHead e (Bind Abbr) u) t n H1)) in (ex2_2_ind C C 
(\lambda (a0: C).(\lambda (_: C).(csubst1 (S n) u c0 a0))) (\lambda (a0: 
C).(\lambda (a: C).(drop (S O) (S n) a0 a))) (ex2_2 C C (\lambda (a0: 
C).(\lambda (_: C).(csubst1 (S n) u (CHead c0 (Flat f) t) a0))) (\lambda (a0: 
C).(\lambda (a: C).(drop (S O) (S n) a0 a)))) (\lambda (x0: C).(\lambda (x1: 
C).(\lambda (H5: (csubst1 (S n) u c0 x0)).(\lambda (H6: (drop (S O) (S n) x0 
x1)).(ex2_2_intro C C (\lambda (a0: C).(\lambda (_: C).(csubst1 (S n) u 
(CHead c0 (Flat f) t) a0))) (\lambda (a0: C).(\lambda (a: C).(drop (S O) (S 
n) a0 a))) (CHead x0 (Flat f) (lift (S O) (S n) x)) (CHead x1 (Flat f) x) 
(csubst1_flat f (S n) u t (lift (S O) (S n) x) H3 c0 x0 H5) (drop_skip_flat 
(S O) n x0 x1 H6 f x)))))) H4)))) H2)))))))) k)))) c)))) d).
(* COMMENTS
Initial nodes: 2467
END *)

