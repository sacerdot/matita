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

include "Basic-1/ty3/props.ma".

include "Basic-1/pc3/fsubst0.ma".

include "Basic-1/getl/getl.ma".

theorem ty3_fsubst0:
 \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t: T).((ty3 g c1 
t1 t) \to (\forall (i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t2: 
T).((fsubst0 i u c1 t1 c2 t2) \to (\forall (e: C).((getl i c1 (CHead e (Bind 
Abbr) u)) \to (ty3 g c2 t2 t))))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t1: T).(\lambda (t: T).(\lambda 
(H: (ty3 g c1 t1 t)).(ty3_ind g (\lambda (c: C).(\lambda (t0: T).(\lambda 
(t2: T).(\forall (i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t3: 
T).((fsubst0 i u c t0 c2 t3) \to (\forall (e: C).((getl i c (CHead e (Bind 
Abbr) u)) \to (ty3 g c2 t3 t2))))))))))) (\lambda (c: C).(\lambda (t2: 
T).(\lambda (t0: T).(\lambda (H0: (ty3 g c t2 t0)).(\lambda (H1: ((\forall 
(i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t3: T).((fsubst0 i u c t2 
c2 t3) \to (\forall (e: C).((getl i c (CHead e (Bind Abbr) u)) \to (ty3 g c2 
t3 t0)))))))))).(\lambda (u: T).(\lambda (t3: T).(\lambda (_: (ty3 g c u 
t3)).(\lambda (H3: ((\forall (i: nat).(\forall (u0: T).(\forall (c2: 
C).(\forall (t4: T).((fsubst0 i u0 c u c2 t4) \to (\forall (e: C).((getl i c 
(CHead e (Bind Abbr) u0)) \to (ty3 g c2 t4 t3)))))))))).(\lambda (H4: (pc3 c 
t3 t2)).(\lambda (i: nat).(\lambda (u0: T).(\lambda (c2: C).(\lambda (t4: 
T).(\lambda (H5: (fsubst0 i u0 c u c2 t4)).(fsubst0_ind i u0 c u (\lambda 
(c0: C).(\lambda (t5: T).(\forall (e: C).((getl i c (CHead e (Bind Abbr) u0)) 
\to (ty3 g c0 t5 t2))))) (\lambda (t5: T).(\lambda (H6: (subst0 i u0 u 
t5)).(\lambda (e: C).(\lambda (H7: (getl i c (CHead e (Bind Abbr) 
u0))).(ty3_conv g c t2 t0 H0 t5 t3 (H3 i u0 c t5 (fsubst0_snd i u0 c u t5 H6) 
e H7) H4))))) (\lambda (c3: C).(\lambda (H6: (csubst0 i u0 c c3)).(\lambda 
(e: C).(\lambda (H7: (getl i c (CHead e (Bind Abbr) u0))).(ty3_conv g c3 t2 
t0 (H1 i u0 c3 t2 (fsubst0_fst i u0 c t2 c3 H6) e H7) u t3 (H3 i u0 c3 u 
(fsubst0_fst i u0 c u c3 H6) e H7) (pc3_fsubst0 c t3 t2 H4 i u0 c3 t3 
(fsubst0_fst i u0 c t3 c3 H6) e H7)))))) (\lambda (t5: T).(\lambda (H6: 
(subst0 i u0 u t5)).(\lambda (c3: C).(\lambda (H7: (csubst0 i u0 c 
c3)).(\lambda (e: C).(\lambda (H8: (getl i c (CHead e (Bind Abbr) 
u0))).(ty3_conv g c3 t2 t0 (H1 i u0 c3 t2 (fsubst0_fst i u0 c t2 c3 H7) e H8) 
t5 t3 (H3 i u0 c3 t5 (fsubst0_both i u0 c u t5 H6 c3 H7) e H8) (pc3_fsubst0 c 
t3 t2 H4 i u0 c3 t3 (fsubst0_fst i u0 c t3 c3 H7) e H8)))))))) c2 t4 
H5)))))))))))))))) (\lambda (c: C).(\lambda (m: nat).(\lambda (i: 
nat).(\lambda (u: T).(\lambda (c2: C).(\lambda (t2: T).(\lambda (H0: (fsubst0 
i u c (TSort m) c2 t2)).(fsubst0_ind i u c (TSort m) (\lambda (c0: 
C).(\lambda (t0: T).(\forall (e: C).((getl i c (CHead e (Bind Abbr) u)) \to 
(ty3 g c0 t0 (TSort (next g m))))))) (\lambda (t3: T).(\lambda (H1: (subst0 i 
u (TSort m) t3)).(\lambda (e: C).(\lambda (_: (getl i c (CHead e (Bind Abbr) 
u))).(subst0_gen_sort u t3 i m H1 (ty3 g c t3 (TSort (next g m)))))))) 
(\lambda (c3: C).(\lambda (_: (csubst0 i u c c3)).(\lambda (e: C).(\lambda 
(_: (getl i c (CHead e (Bind Abbr) u))).(ty3_sort g c3 m))))) (\lambda (t3: 
T).(\lambda (H1: (subst0 i u (TSort m) t3)).(\lambda (c3: C).(\lambda (_: 
(csubst0 i u c c3)).(\lambda (e: C).(\lambda (_: (getl i c (CHead e (Bind 
Abbr) u))).(subst0_gen_sort u t3 i m H1 (ty3 g c3 t3 (TSort (next g 
m)))))))))) c2 t2 H0)))))))) (\lambda (n: nat).(\lambda (c: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (H0: (getl n c (CHead d (Bind Abbr) u))).(\lambda 
(t0: T).(\lambda (H1: (ty3 g d u t0)).(\lambda (H2: ((\forall (i: 
nat).(\forall (u0: T).(\forall (c2: C).(\forall (t2: T).((fsubst0 i u0 d u c2 
t2) \to (\forall (e: C).((getl i d (CHead e (Bind Abbr) u0)) \to (ty3 g c2 t2 
t0)))))))))).(\lambda (i: nat).(\lambda (u0: T).(\lambda (c2: C).(\lambda 
(t2: T).(\lambda (H3: (fsubst0 i u0 c (TLRef n) c2 t2)).(fsubst0_ind i u0 c 
(TLRef n) (\lambda (c0: C).(\lambda (t3: T).(\forall (e: C).((getl i c (CHead 
e (Bind Abbr) u0)) \to (ty3 g c0 t3 (lift (S n) O t0)))))) (\lambda (t3: 
T).(\lambda (H4: (subst0 i u0 (TLRef n) t3)).(\lambda (e: C).(\lambda (H5: 
(getl i c (CHead e (Bind Abbr) u0))).(land_ind (eq nat n i) (eq T t3 (lift (S 
n) O u0)) (ty3 g c t3 (lift (S n) O t0)) (\lambda (H6: (eq nat n i)).(\lambda 
(H7: (eq T t3 (lift (S n) O u0))).(eq_ind_r T (lift (S n) O u0) (\lambda (t4: 
T).(ty3 g c t4 (lift (S n) O t0))) (let H8 \def (eq_ind_r nat i (\lambda (n0: 
nat).(getl n0 c (CHead e (Bind Abbr) u0))) H5 n H6) in (let H9 \def (eq_ind C 
(CHead d (Bind Abbr) u) (\lambda (c0: C).(getl n c c0)) H0 (CHead e (Bind 
Abbr) u0) (getl_mono c (CHead d (Bind Abbr) u) n H0 (CHead e (Bind Abbr) u0) 
H8)) in (let H10 \def (f_equal C C (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c0 _ _) \Rightarrow 
c0])) (CHead d (Bind Abbr) u) (CHead e (Bind Abbr) u0) (getl_mono c (CHead d 
(Bind Abbr) u) n H0 (CHead e (Bind Abbr) u0) H8)) in ((let H11 \def (f_equal 
C T (\lambda (e0: C).(match e0 in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow u | (CHead _ _ t4) \Rightarrow t4])) (CHead d (Bind Abbr) u) 
(CHead e (Bind Abbr) u0) (getl_mono c (CHead d (Bind Abbr) u) n H0 (CHead e 
(Bind Abbr) u0) H8)) in (\lambda (H12: (eq C d e)).(let H13 \def (eq_ind_r C 
e (\lambda (c0: C).(getl n c (CHead c0 (Bind Abbr) u0))) H9 d H12) in (let 
H14 \def (eq_ind_r T u0 (\lambda (t4: T).(getl n c (CHead d (Bind Abbr) t4))) 
H13 u H11) in (eq_ind T u (\lambda (t4: T).(ty3 g c (lift (S n) O t4) (lift 
(S n) O t0))) (ty3_lift g d u t0 H1 c O (S n) (getl_drop Abbr c d u n H14)) 
u0 H11))))) H10)))) t3 H7))) (subst0_gen_lref u0 t3 i n H4)))))) (\lambda 
(c3: C).(\lambda (H4: (csubst0 i u0 c c3)).(\lambda (e: C).(\lambda (H5: 
(getl i c (CHead e (Bind Abbr) u0))).(lt_le_e n i (ty3 g c3 (TLRef n) (lift 
(S n) O t0)) (\lambda (H6: (lt n i)).(let H7 \def (csubst0_getl_lt i n H6 c 
c3 u0 H4 (CHead d (Bind Abbr) u) H0) in (or4_ind (getl n c3 (CHead d (Bind 
Abbr) u)) (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e0 (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c3 
(CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (w: T).(subst0 (minus i (S n)) u0 u1 w)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq C 
(CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u1: T).(getl n c3 (CHead e2 (Bind b) 
u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus i (S n)) u0 e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C 
(CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl n c3 (CHead e2 
(Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (w: T).(subst0 (minus i (S n)) u0 u1 w)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus i (S n)) u0 e1 e2))))))) (ty3 g c3 (TLRef n) (lift (S n) O t0)) 
(\lambda (H8: (getl n c3 (CHead d (Bind Abbr) u))).(ty3_abbr g n c3 d u H8 t0 
H1)) (\lambda (H8: (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e0 (Bind b) 
u1)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c3 (CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i (S n)) u0 u1 
w))))))).(ex3_4_ind B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C (CHead d (Bind Abbr) u) (CHead e0 (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c3 
(CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (w: T).(subst0 (minus i (S n)) u0 u1 w))))) (ty3 g c3 (TLRef n) 
(lift (S n) O t0)) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: 
T).(\lambda (x3: T).(\lambda (H9: (eq C (CHead d (Bind Abbr) u) (CHead x1 
(Bind x0) x2))).(\lambda (H10: (getl n c3 (CHead x1 (Bind x0) x3))).(\lambda 
(H11: (subst0 (minus i (S n)) u0 x2 x3)).(let H12 \def (f_equal C C (\lambda 
(e0: C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow 
d | (CHead c0 _ _) \Rightarrow c0])) (CHead d (Bind Abbr) u) (CHead x1 (Bind 
x0) x2) H9) in ((let H13 \def (f_equal C B (\lambda (e0: C).(match e0 in C 
return (\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u) (CHead 
x1 (Bind x0) x2) H9) in ((let H14 \def (f_equal C T (\lambda (e0: C).(match 
e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ 
t3) \Rightarrow t3])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x2) H9) in 
(\lambda (H15: (eq B Abbr x0)).(\lambda (H16: (eq C d x1)).(let H17 \def 
(eq_ind_r T x2 (\lambda (t3: T).(subst0 (minus i (S n)) u0 t3 x3)) H11 u H14) 
in (let H18 \def (eq_ind_r C x1 (\lambda (c0: C).(getl n c3 (CHead c0 (Bind 
x0) x3))) H10 d H16) in (let H19 \def (eq_ind_r B x0 (\lambda (b: B).(getl n 
c3 (CHead d (Bind b) x3))) H18 Abbr H15) in (let H20 \def (eq_ind nat (minus 
i n) (\lambda (n0: nat).(getl n0 (CHead d (Bind Abbr) x3) (CHead e (Bind 
Abbr) u0))) (getl_conf_le i (CHead e (Bind Abbr) u0) c3 (csubst0_getl_ge i i 
(le_n i) c c3 u0 H4 (CHead e (Bind Abbr) u0) H5) (CHead d (Bind Abbr) x3) n 
H19 (le_S_n n i (le_S (S n) i H6))) (S (minus i (S n))) (minus_x_Sy i n H6)) 
in (ty3_abbr g n c3 d x3 H19 t0 (H2 (minus i (S n)) u0 d x3 (fsubst0_snd 
(minus i (S n)) u0 d u x3 H17) e (getl_gen_S (Bind Abbr) d (CHead e (Bind 
Abbr) u0) x3 (minus i (S n)) H20)))))))))) H13)) H12))))))))) H8)) (\lambda 
(H8: (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(eq C (CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1)))))) (\lambda 
(b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u1: T).(getl n c3 (CHead e2 
(Bind b) u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 (minus i (S n)) u0 e1 e2))))))).(ex3_4_ind B C C T (\lambda 
(b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq C (CHead d (Bind 
Abbr) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: B).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u1: T).(getl n c3 (CHead e2 (Bind b) u1)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
u0 e1 e2))))) (ty3 g c3 (TLRef n) (lift (S n) O t0)) (\lambda (x0: 
B).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H9: (eq C 
(CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x3))).(\lambda (H10: (getl n c3 
(CHead x2 (Bind x0) x3))).(\lambda (H11: (csubst0 (minus i (S n)) u0 x1 
x2)).(let H12 \def (f_equal C C (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c0 _ _) \Rightarrow 
c0])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x3) H9) in ((let H13 \def 
(f_equal C B (\lambda (e0: C).(match e0 in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow Abbr | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow 
Abbr])])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x3) H9) in ((let H14 
\def (f_equal C T (\lambda (e0: C).(match e0 in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u | (CHead _ _ t3) \Rightarrow t3])) (CHead d 
(Bind Abbr) u) (CHead x1 (Bind x0) x3) H9) in (\lambda (H15: (eq B Abbr 
x0)).(\lambda (H16: (eq C d x1)).(let H17 \def (eq_ind_r T x3 (\lambda (t3: 
T).(getl n c3 (CHead x2 (Bind x0) t3))) H10 u H14) in (let H18 \def (eq_ind_r 
C x1 (\lambda (c0: C).(csubst0 (minus i (S n)) u0 c0 x2)) H11 d H16) in (let 
H19 \def (eq_ind_r B x0 (\lambda (b: B).(getl n c3 (CHead x2 (Bind b) u))) 
H17 Abbr H15) in (let H20 \def (eq_ind nat (minus i n) (\lambda (n0: 
nat).(getl n0 (CHead x2 (Bind Abbr) u) (CHead e (Bind Abbr) u0))) 
(getl_conf_le i (CHead e (Bind Abbr) u0) c3 (csubst0_getl_ge i i (le_n i) c 
c3 u0 H4 (CHead e (Bind Abbr) u0) H5) (CHead x2 (Bind Abbr) u) n H19 (le_S_n 
n i (le_S (S n) i H6))) (S (minus i (S n))) (minus_x_Sy i n H6)) in (ty3_abbr 
g n c3 x2 u H19 t0 (H2 (minus i (S n)) u0 x2 u (fsubst0_fst (minus i (S n)) 
u0 d u x2 H18) e (csubst0_getl_ge_back (minus i (S n)) (minus i (S n)) (le_n 
(minus i (S n))) d x2 u0 H18 (CHead e (Bind Abbr) u0) (getl_gen_S (Bind Abbr) 
x2 (CHead e (Bind Abbr) u0) u (minus i (S n)) H20))))))))))) H13)) 
H12))))))))) H8)) (\lambda (H8: (ex4_5 B C C T T (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind 
Abbr) u) (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl n c3 (CHead e2 
(Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (w: T).(subst0 (minus i (S n)) u0 u1 w)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus i (S n)) u0 e1 e2)))))))).(ex4_5_ind B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C 
(CHead d (Bind Abbr) u) (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl n c3 (CHead e2 
(Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (w: T).(subst0 (minus i (S n)) u0 u1 w)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus i (S n)) u0 e1 e2)))))) (ty3 g c3 (TLRef n) (lift (S n) O t0)) 
(\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda 
(x4: T).(\lambda (H9: (eq C (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) 
x3))).(\lambda (H10: (getl n c3 (CHead x2 (Bind x0) x4))).(\lambda (H11: 
(subst0 (minus i (S n)) u0 x3 x4)).(\lambda (H12: (csubst0 (minus i (S n)) u0 
x1 x2)).(let H13 \def (f_equal C C (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c0 _ _) \Rightarrow 
c0])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x3) H9) in ((let H14 \def 
(f_equal C B (\lambda (e0: C).(match e0 in C return (\lambda (_: C).B) with 
[(CSort _) \Rightarrow Abbr | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).B) with [(Bind b) \Rightarrow b | (Flat _) \Rightarrow 
Abbr])])) (CHead d (Bind Abbr) u) (CHead x1 (Bind x0) x3) H9) in ((let H15 
\def (f_equal C T (\lambda (e0: C).(match e0 in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u | (CHead _ _ t3) \Rightarrow t3])) (CHead d 
(Bind Abbr) u) (CHead x1 (Bind x0) x3) H9) in (\lambda (H16: (eq B Abbr 
x0)).(\lambda (H17: (eq C d x1)).(let H18 \def (eq_ind_r T x3 (\lambda (t3: 
T).(subst0 (minus i (S n)) u0 t3 x4)) H11 u H15) in (let H19 \def (eq_ind_r C 
x1 (\lambda (c0: C).(csubst0 (minus i (S n)) u0 c0 x2)) H12 d H17) in (let 
H20 \def (eq_ind_r B x0 (\lambda (b: B).(getl n c3 (CHead x2 (Bind b) x4))) 
H10 Abbr H16) in (let H21 \def (eq_ind nat (minus i n) (\lambda (n0: 
nat).(getl n0 (CHead x2 (Bind Abbr) x4) (CHead e (Bind Abbr) u0))) 
(getl_conf_le i (CHead e (Bind Abbr) u0) c3 (csubst0_getl_ge i i (le_n i) c 
c3 u0 H4 (CHead e (Bind Abbr) u0) H5) (CHead x2 (Bind Abbr) x4) n H20 (le_S_n 
n i (le_S (S n) i H6))) (S (minus i (S n))) (minus_x_Sy i n H6)) in (ty3_abbr 
g n c3 x2 x4 H20 t0 (H2 (minus i (S n)) u0 x2 x4 (fsubst0_both (minus i (S 
n)) u0 d u x4 H18 x2 H19) e (csubst0_getl_ge_back (minus i (S n)) (minus i (S 
n)) (le_n (minus i (S n))) d x2 u0 H19 (CHead e (Bind Abbr) u0) (getl_gen_S 
(Bind Abbr) x2 (CHead e (Bind Abbr) u0) x4 (minus i (S n)) H21))))))))))) 
H14)) H13))))))))))) H8)) H7))) (\lambda (H6: (le i n)).(ty3_abbr g n c3 d u 
(csubst0_getl_ge i n H6 c c3 u0 H4 (CHead d (Bind Abbr) u) H0) t0 H1))))))) 
(\lambda (t3: T).(\lambda (H4: (subst0 i u0 (TLRef n) t3)).(\lambda (c3: 
C).(\lambda (H5: (csubst0 i u0 c c3)).(\lambda (e: C).(\lambda (H6: (getl i c 
(CHead e (Bind Abbr) u0))).(land_ind (eq nat n i) (eq T t3 (lift (S n) O u0)) 
(ty3 g c3 t3 (lift (S n) O t0)) (\lambda (H7: (eq nat n i)).(\lambda (H8: (eq 
T t3 (lift (S n) O u0))).(eq_ind_r T (lift (S n) O u0) (\lambda (t4: T).(ty3 
g c3 t4 (lift (S n) O t0))) (let H9 \def (eq_ind_r nat i (\lambda (n0: 
nat).(getl n0 c (CHead e (Bind Abbr) u0))) H6 n H7) in (let H10 \def 
(eq_ind_r nat i (\lambda (n0: nat).(csubst0 n0 u0 c c3)) H5 n H7) in (let H11 
\def (eq_ind C (CHead d (Bind Abbr) u) (\lambda (c0: C).(getl n c c0)) H0 
(CHead e (Bind Abbr) u0) (getl_mono c (CHead d (Bind Abbr) u) n H0 (CHead e 
(Bind Abbr) u0) H9)) in (let H12 \def (f_equal C C (\lambda (e0: C).(match e0 
in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c0 _ _) 
\Rightarrow c0])) (CHead d (Bind Abbr) u) (CHead e (Bind Abbr) u0) (getl_mono 
c (CHead d (Bind Abbr) u) n H0 (CHead e (Bind Abbr) u0) H9)) in ((let H13 
\def (f_equal C T (\lambda (e0: C).(match e0 in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u | (CHead _ _ t4) \Rightarrow t4])) (CHead d 
(Bind Abbr) u) (CHead e (Bind Abbr) u0) (getl_mono c (CHead d (Bind Abbr) u) 
n H0 (CHead e (Bind Abbr) u0) H9)) in (\lambda (H14: (eq C d e)).(let H15 
\def (eq_ind_r C e (\lambda (c0: C).(getl n c (CHead c0 (Bind Abbr) u0))) H11 
d H14) in (let H16 \def (eq_ind_r T u0 (\lambda (t4: T).(getl n c (CHead d 
(Bind Abbr) t4))) H15 u H13) in (let H17 \def (eq_ind_r T u0 (\lambda (t4: 
T).(csubst0 n t4 c c3)) H10 u H13) in (eq_ind T u (\lambda (t4: T).(ty3 g c3 
(lift (S n) O t4) (lift (S n) O t0))) (ty3_lift g d u t0 H1 c3 O (S n) 
(getl_drop Abbr c3 d u n (csubst0_getl_ge n n (le_n n) c c3 u H17 (CHead d 
(Bind Abbr) u) H16))) u0 H13)))))) H12))))) t3 H8))) (subst0_gen_lref u0 t3 i 
n H4)))))))) c2 t2 H3)))))))))))))) (\lambda (n: nat).(\lambda (c: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (H0: (getl n c (CHead d (Bind 
Abst) u))).(\lambda (t0: T).(\lambda (H1: (ty3 g d u t0)).(\lambda (H2: 
((\forall (i: nat).(\forall (u0: T).(\forall (c2: C).(\forall (t2: 
T).((fsubst0 i u0 d u c2 t2) \to (\forall (e: C).((getl i d (CHead e (Bind 
Abbr) u0)) \to (ty3 g c2 t2 t0)))))))))).(\lambda (i: nat).(\lambda (u0: 
T).(\lambda (c2: C).(\lambda (t2: T).(\lambda (H3: (fsubst0 i u0 c (TLRef n) 
c2 t2)).(fsubst0_ind i u0 c (TLRef n) (\lambda (c0: C).(\lambda (t3: 
T).(\forall (e: C).((getl i c (CHead e (Bind Abbr) u0)) \to (ty3 g c0 t3 
(lift (S n) O u)))))) (\lambda (t3: T).(\lambda (H4: (subst0 i u0 (TLRef n) 
t3)).(\lambda (e: C).(\lambda (H5: (getl i c (CHead e (Bind Abbr) 
u0))).(land_ind (eq nat n i) (eq T t3 (lift (S n) O u0)) (ty3 g c t3 (lift (S 
n) O u)) (\lambda (H6: (eq nat n i)).(\lambda (H7: (eq T t3 (lift (S n) O 
u0))).(eq_ind_r T (lift (S n) O u0) (\lambda (t4: T).(ty3 g c t4 (lift (S n) 
O u))) (let H8 \def (eq_ind_r nat i (\lambda (n0: nat).(getl n0 c (CHead e 
(Bind Abbr) u0))) H5 n H6) in (let H9 \def (eq_ind C (CHead d (Bind Abst) u) 
(\lambda (c0: C).(getl n c c0)) H0 (CHead e (Bind Abbr) u0) (getl_mono c 
(CHead d (Bind Abst) u) n H0 (CHead e (Bind Abbr) u0) H8)) in (let H10 \def 
(eq_ind C (CHead d (Bind Abst) u) (\lambda (ee: C).(match ee in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind b) 
\Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow 
False | Abst \Rightarrow True | Void \Rightarrow False]) | (Flat _) 
\Rightarrow False])])) I (CHead e (Bind Abbr) u0) (getl_mono c (CHead d (Bind 
Abst) u) n H0 (CHead e (Bind Abbr) u0) H8)) in (False_ind (ty3 g c (lift (S 
n) O u0) (lift (S n) O u)) H10)))) t3 H7))) (subst0_gen_lref u0 t3 i n 
H4)))))) (\lambda (c3: C).(\lambda (H4: (csubst0 i u0 c c3)).(\lambda (e: 
C).(\lambda (H5: (getl i c (CHead e (Bind Abbr) u0))).(lt_le_e n i (ty3 g c3 
(TLRef n) (lift (S n) O u)) (\lambda (H6: (lt n i)).(let H7 \def 
(csubst0_getl_lt i n H6 c c3 u0 H4 (CHead d (Bind Abst) u) H0) in (or4_ind 
(getl n c3 (CHead d (Bind Abst) u)) (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abst) u) (CHead 
e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl n c3 (CHead e0 (Bind b) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i (S n)) 
u0 u1 w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(eq C (CHead d (Bind Abst) u) (CHead e1 (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u1: T).(getl n c3 
(CHead e2 (Bind b) u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus i (S n)) u0 e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C (CHead d (Bind Abst) u) (CHead e1 (Bind b) u1))))))) (\lambda 
(b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl 
n c3 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i (S n)) u0 u1 w)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i (S n)) u0 e1 e2))))))) (ty3 g c3 (TLRef n) (lift (S 
n) O u)) (\lambda (H8: (getl n c3 (CHead d (Bind Abst) u))).(ty3_abst g n c3 
d u H8 t0 H1)) (\lambda (H8: (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead d (Bind Abst) u) (CHead e0 
(Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(getl n c3 (CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i (S n)) u0 u1 
w))))))).(ex3_4_ind B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C (CHead d (Bind Abst) u) (CHead e0 (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c3 
(CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (w: T).(subst0 (minus i (S n)) u0 u1 w))))) (ty3 g c3 (TLRef n) 
(lift (S n) O u)) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: T).(\lambda 
(x3: T).(\lambda (H9: (eq C (CHead d (Bind Abst) u) (CHead x1 (Bind x0) 
x2))).(\lambda (H10: (getl n c3 (CHead x1 (Bind x0) x3))).(\lambda (H11: 
(subst0 (minus i (S n)) u0 x2 x3)).(let H12 \def (f_equal C C (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | 
(CHead c0 _ _) \Rightarrow c0])) (CHead d (Bind Abst) u) (CHead x1 (Bind x0) 
x2) H9) in ((let H13 \def (f_equal C B (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).B) with [(CSort _) \Rightarrow Abst | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow Abst])])) (CHead d (Bind Abst) u) (CHead 
x1 (Bind x0) x2) H9) in ((let H14 \def (f_equal C T (\lambda (e0: C).(match 
e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ 
t3) \Rightarrow t3])) (CHead d (Bind Abst) u) (CHead x1 (Bind x0) x2) H9) in 
(\lambda (H15: (eq B Abst x0)).(\lambda (H16: (eq C d x1)).(let H17 \def 
(eq_ind_r T x2 (\lambda (t3: T).(subst0 (minus i (S n)) u0 t3 x3)) H11 u H14) 
in (let H18 \def (eq_ind_r C x1 (\lambda (c0: C).(getl n c3 (CHead c0 (Bind 
x0) x3))) H10 d H16) in (let H19 \def (eq_ind_r B x0 (\lambda (b: B).(getl n 
c3 (CHead d (Bind b) x3))) H18 Abst H15) in (let H20 \def (eq_ind nat (minus 
i n) (\lambda (n0: nat).(getl n0 (CHead d (Bind Abst) x3) (CHead e (Bind 
Abbr) u0))) (getl_conf_le i (CHead e (Bind Abbr) u0) c3 (csubst0_getl_ge i i 
(le_n i) c c3 u0 H4 (CHead e (Bind Abbr) u0) H5) (CHead d (Bind Abst) x3) n 
H19 (le_S_n n i (le_S (S n) i H6))) (S (minus i (S n))) (minus_x_Sy i n H6)) 
in (ty3_conv g c3 (lift (S n) O u) (lift (S n) O t0) (ty3_lift g d u t0 H1 c3 
O (S n) (getl_drop Abst c3 d x3 n H19)) (TLRef n) (lift (S n) O x3) (ty3_abst 
g n c3 d x3 H19 t0 (H2 (minus i (S n)) u0 d x3 (fsubst0_snd (minus i (S n)) 
u0 d u x3 H17) e (getl_gen_S (Bind Abst) d (CHead e (Bind Abbr) u0) x3 (minus 
i (S n)) H20))) (pc3_lift c3 d (S n) O (getl_drop Abst c3 d x3 n H19) x3 u 
(pc3_pr2_x d x3 u (pr2_delta d e u0 (r (Bind Abst) (minus i (S n))) 
(getl_gen_S (Bind Abst) d (CHead e (Bind Abbr) u0) x3 (minus i (S n)) H20) u 
u (pr0_refl u) x3 H17))))))))))) H13)) H12))))))))) H8)) (\lambda (H8: (ex3_4 
B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq 
C (CHead d (Bind Abst) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u1: T).(getl n c3 (CHead e2 
(Bind b) u1)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 (minus i (S n)) u0 e1 e2))))))).(ex3_4_ind B C C T (\lambda 
(b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(eq C (CHead d (Bind 
Abst) u) (CHead e1 (Bind b) u1)))))) (\lambda (b: B).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u1: T).(getl n c3 (CHead e2 (Bind b) u1)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
u0 e1 e2))))) (ty3 g c3 (TLRef n) (lift (S n) O u)) (\lambda (x0: B).(\lambda 
(x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H9: (eq C (CHead d (Bind 
Abst) u) (CHead x1 (Bind x0) x3))).(\lambda (H10: (getl n c3 (CHead x2 (Bind 
x0) x3))).(\lambda (H11: (csubst0 (minus i (S n)) u0 x1 x2)).(let H12 \def 
(f_equal C C (\lambda (e0: C).(match e0 in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow d | (CHead c0 _ _) \Rightarrow c0])) (CHead d (Bind 
Abst) u) (CHead x1 (Bind x0) x3) H9) in ((let H13 \def (f_equal C B (\lambda 
(e0: C).(match e0 in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow 
Abst | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).B) with 
[(Bind b) \Rightarrow b | (Flat _) \Rightarrow Abst])])) (CHead d (Bind Abst) 
u) (CHead x1 (Bind x0) x3) H9) in ((let H14 \def (f_equal C T (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u | 
(CHead _ _ t3) \Rightarrow t3])) (CHead d (Bind Abst) u) (CHead x1 (Bind x0) 
x3) H9) in (\lambda (H15: (eq B Abst x0)).(\lambda (H16: (eq C d x1)).(let 
H17 \def (eq_ind_r T x3 (\lambda (t3: T).(getl n c3 (CHead x2 (Bind x0) t3))) 
H10 u H14) in (let H18 \def (eq_ind_r C x1 (\lambda (c0: C).(csubst0 (minus i 
(S n)) u0 c0 x2)) H11 d H16) in (let H19 \def (eq_ind_r B x0 (\lambda (b: 
B).(getl n c3 (CHead x2 (Bind b) u))) H17 Abst H15) in (let H20 \def (eq_ind 
nat (minus i n) (\lambda (n0: nat).(getl n0 (CHead x2 (Bind Abst) u) (CHead e 
(Bind Abbr) u0))) (getl_conf_le i (CHead e (Bind Abbr) u0) c3 
(csubst0_getl_ge i i (le_n i) c c3 u0 H4 (CHead e (Bind Abbr) u0) H5) (CHead 
x2 (Bind Abst) u) n H19 (le_S_n n i (le_S (S n) i H6))) (S (minus i (S n))) 
(minus_x_Sy i n H6)) in (ty3_abst g n c3 x2 u H19 t0 (H2 (minus i (S n)) u0 
x2 u (fsubst0_fst (minus i (S n)) u0 d u x2 H18) e (csubst0_getl_ge_back 
(minus i (S n)) (minus i (S n)) (le_n (minus i (S n))) d x2 u0 H18 (CHead e 
(Bind Abbr) u0) (getl_gen_S (Bind Abst) x2 (CHead e (Bind Abbr) u0) u (minus 
i (S n)) H20))))))))))) H13)) H12))))))))) H8)) (\lambda (H8: (ex4_5 B C C T 
T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C (CHead d (Bind Abst) u) (CHead e1 (Bind b) u1))))))) (\lambda 
(b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl 
n c3 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i (S n)) u0 u1 w)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i (S n)) u0 e1 e2)))))))).(ex4_5_ind B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C (CHead d (Bind Abst) u) (CHead e1 (Bind b) u1))))))) (\lambda 
(b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl 
n c3 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (w: T).(subst0 (minus i (S n)) u0 u1 w)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i (S n)) u0 e1 e2)))))) (ty3 g c3 (TLRef n) (lift (S 
n) O u)) (\lambda (x0: B).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: 
T).(\lambda (x4: T).(\lambda (H9: (eq C (CHead d (Bind Abst) u) (CHead x1 
(Bind x0) x3))).(\lambda (H10: (getl n c3 (CHead x2 (Bind x0) x4))).(\lambda 
(H11: (subst0 (minus i (S n)) u0 x3 x4)).(\lambda (H12: (csubst0 (minus i (S 
n)) u0 x1 x2)).(let H13 \def (f_equal C C (\lambda (e0: C).(match e0 in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c0 _ _) 
\Rightarrow c0])) (CHead d (Bind Abst) u) (CHead x1 (Bind x0) x3) H9) in 
((let H14 \def (f_equal C B (\lambda (e0: C).(match e0 in C return (\lambda 
(_: C).B) with [(CSort _) \Rightarrow Abst | (CHead _ k _) \Rightarrow (match 
k in K return (\lambda (_: K).B) with [(Bind b) \Rightarrow b | (Flat _) 
\Rightarrow Abst])])) (CHead d (Bind Abst) u) (CHead x1 (Bind x0) x3) H9) in 
((let H15 \def (f_equal C T (\lambda (e0: C).(match e0 in C return (\lambda 
(_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t3) \Rightarrow t3])) 
(CHead d (Bind Abst) u) (CHead x1 (Bind x0) x3) H9) in (\lambda (H16: (eq B 
Abst x0)).(\lambda (H17: (eq C d x1)).(let H18 \def (eq_ind_r T x3 (\lambda 
(t3: T).(subst0 (minus i (S n)) u0 t3 x4)) H11 u H15) in (let H19 \def 
(eq_ind_r C x1 (\lambda (c0: C).(csubst0 (minus i (S n)) u0 c0 x2)) H12 d 
H17) in (let H20 \def (eq_ind_r B x0 (\lambda (b: B).(getl n c3 (CHead x2 
(Bind b) x4))) H10 Abst H16) in (let H21 \def (eq_ind nat (minus i n) 
(\lambda (n0: nat).(getl n0 (CHead x2 (Bind Abst) x4) (CHead e (Bind Abbr) 
u0))) (getl_conf_le i (CHead e (Bind Abbr) u0) c3 (csubst0_getl_ge i i (le_n 
i) c c3 u0 H4 (CHead e (Bind Abbr) u0) H5) (CHead x2 (Bind Abst) x4) n H20 
(le_S_n n i (le_S (S n) i H6))) (S (minus i (S n))) (minus_x_Sy i n H6)) in 
(ty3_conv g c3 (lift (S n) O u) (lift (S n) O t0) (ty3_lift g x2 u t0 (H2 
(minus i (S n)) u0 x2 u (fsubst0_fst (minus i (S n)) u0 d u x2 H19) e 
(csubst0_getl_ge_back (minus i (S n)) (minus i (S n)) (le_n (minus i (S n))) 
d x2 u0 H19 (CHead e (Bind Abbr) u0) (getl_gen_S (Bind Abst) x2 (CHead e 
(Bind Abbr) u0) x4 (minus i (S n)) H21))) c3 O (S n) (getl_drop Abst c3 x2 x4 
n H20)) (TLRef n) (lift (S n) O x4) (ty3_abst g n c3 x2 x4 H20 t0 (H2 (minus 
i (S n)) u0 x2 x4 (fsubst0_both (minus i (S n)) u0 d u x4 H18 x2 H19) e 
(csubst0_getl_ge_back (minus i (S n)) (minus i (S n)) (le_n (minus i (S n))) 
d x2 u0 H19 (CHead e (Bind Abbr) u0) (getl_gen_S (Bind Abst) x2 (CHead e 
(Bind Abbr) u0) x4 (minus i (S n)) H21)))) (pc3_lift c3 x2 (S n) O (getl_drop 
Abst c3 x2 x4 n H20) x4 u (pc3_fsubst0 d u u (pc3_refl d u) (minus i (S n)) 
u0 x2 x4 (fsubst0_both (minus i (S n)) u0 d u x4 H18 x2 H19) e 
(csubst0_getl_ge_back (minus i (S n)) (minus i (S n)) (le_n (minus i (S n))) 
d x2 u0 H19 (CHead e (Bind Abbr) u0) (getl_gen_S (Bind Abst) x2 (CHead e 
(Bind Abbr) u0) x4 (minus i (S n)) H21)))))))))))) H14)) H13))))))))))) H8)) 
H7))) (\lambda (H6: (le i n)).(ty3_abst g n c3 d u (csubst0_getl_ge i n H6 c 
c3 u0 H4 (CHead d (Bind Abst) u) H0) t0 H1))))))) (\lambda (t3: T).(\lambda 
(H4: (subst0 i u0 (TLRef n) t3)).(\lambda (c3: C).(\lambda (H5: (csubst0 i u0 
c c3)).(\lambda (e: C).(\lambda (H6: (getl i c (CHead e (Bind Abbr) 
u0))).(land_ind (eq nat n i) (eq T t3 (lift (S n) O u0)) (ty3 g c3 t3 (lift 
(S n) O u)) (\lambda (H7: (eq nat n i)).(\lambda (H8: (eq T t3 (lift (S n) O 
u0))).(eq_ind_r T (lift (S n) O u0) (\lambda (t4: T).(ty3 g c3 t4 (lift (S n) 
O u))) (let H9 \def (eq_ind_r nat i (\lambda (n0: nat).(getl n0 c (CHead e 
(Bind Abbr) u0))) H6 n H7) in (let H10 \def (eq_ind_r nat i (\lambda (n0: 
nat).(csubst0 n0 u0 c c3)) H5 n H7) in (let H11 \def (eq_ind C (CHead d (Bind 
Abst) u) (\lambda (c0: C).(getl n c c0)) H0 (CHead e (Bind Abbr) u0) 
(getl_mono c (CHead d (Bind Abst) u) n H0 (CHead e (Bind Abbr) u0) H9)) in 
(let H12 \def (eq_ind C (CHead d (Bind Abst) u) (\lambda (ee: C).(match ee in 
C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k 
_) \Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind b) 
\Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow 
False | Abst \Rightarrow True | Void \Rightarrow False]) | (Flat _) 
\Rightarrow False])])) I (CHead e (Bind Abbr) u0) (getl_mono c (CHead d (Bind 
Abst) u) n H0 (CHead e (Bind Abbr) u0) H9)) in (False_ind (ty3 g c3 (lift (S 
n) O u0) (lift (S n) O u)) H12))))) t3 H8))) (subst0_gen_lref u0 t3 i n 
H4)))))))) c2 t2 H3)))))))))))))) (\lambda (c: C).(\lambda (u: T).(\lambda 
(t0: T).(\lambda (H0: (ty3 g c u t0)).(\lambda (H1: ((\forall (i: 
nat).(\forall (u0: T).(\forall (c2: C).(\forall (t2: T).((fsubst0 i u0 c u c2 
t2) \to (\forall (e: C).((getl i c (CHead e (Bind Abbr) u0)) \to (ty3 g c2 t2 
t0)))))))))).(\lambda (b: B).(\lambda (t2: T).(\lambda (t3: T).(\lambda (H2: 
(ty3 g (CHead c (Bind b) u) t2 t3)).(\lambda (H3: ((\forall (i: nat).(\forall 
(u0: T).(\forall (c2: C).(\forall (t4: T).((fsubst0 i u0 (CHead c (Bind b) u) 
t2 c2 t4) \to (\forall (e: C).((getl i (CHead c (Bind b) u) (CHead e (Bind 
Abbr) u0)) \to (ty3 g c2 t4 t3)))))))))).(\lambda (i: nat).(\lambda (u0: 
T).(\lambda (c2: C).(\lambda (t4: T).(\lambda (H4: (fsubst0 i u0 c (THead 
(Bind b) u t2) c2 t4)).(fsubst0_ind i u0 c (THead (Bind b) u t2) (\lambda 
(c0: C).(\lambda (t5: T).(\forall (e: C).((getl i c (CHead e (Bind Abbr) u0)) 
\to (ty3 g c0 t5 (THead (Bind b) u t3)))))) (\lambda (t5: T).(\lambda (H5: 
(subst0 i u0 (THead (Bind b) u t2) t5)).(\lambda (e: C).(\lambda (H6: (getl i 
c (CHead e (Bind Abbr) u0))).(or3_ind (ex2 T (\lambda (u2: T).(eq T t5 (THead 
(Bind b) u2 t2))) (\lambda (u2: T).(subst0 i u0 u u2))) (ex2 T (\lambda (t6: 
T).(eq T t5 (THead (Bind b) u t6))) (\lambda (t6: T).(subst0 (s (Bind b) i) 
u0 t2 t6))) (ex3_2 T T (\lambda (u2: T).(\lambda (t6: T).(eq T t5 (THead 
(Bind b) u2 t6)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u0 u u2))) 
(\lambda (_: T).(\lambda (t6: T).(subst0 (s (Bind b) i) u0 t2 t6)))) (ty3 g c 
t5 (THead (Bind b) u t3)) (\lambda (H7: (ex2 T (\lambda (u2: T).(eq T t5 
(THead (Bind b) u2 t2))) (\lambda (u2: T).(subst0 i u0 u u2)))).(ex2_ind T 
(\lambda (u2: T).(eq T t5 (THead (Bind b) u2 t2))) (\lambda (u2: T).(subst0 i 
u0 u u2)) (ty3 g c t5 (THead (Bind b) u t3)) (\lambda (x: T).(\lambda (H8: 
(eq T t5 (THead (Bind b) x t2))).(\lambda (H9: (subst0 i u0 u x)).(eq_ind_r T 
(THead (Bind b) x t2) (\lambda (t6: T).(ty3 g c t6 (THead (Bind b) u t3))) 
(ex_ind T (\lambda (t6: T).(ty3 g (CHead c (Bind b) u) t3 t6)) (ty3 g c 
(THead (Bind b) x t2) (THead (Bind b) u t3)) (\lambda (x0: T).(\lambda (H10: 
(ty3 g (CHead c (Bind b) u) t3 x0)).(ex_ind T (\lambda (t6: T).(ty3 g (CHead 
c (Bind b) x) t3 t6)) (ty3 g c (THead (Bind b) x t2) (THead (Bind b) u t3)) 
(\lambda (x1: T).(\lambda (_: (ty3 g (CHead c (Bind b) x) t3 x1)).(ty3_conv g 
c (THead (Bind b) u t3) (THead (Bind b) u x0) (ty3_bind g c u t0 H0 b t3 x0 
H10) (THead (Bind b) x t2) (THead (Bind b) x t3) (ty3_bind g c x t0 (H1 i u0 
c x (fsubst0_snd i u0 c u x H9) e H6) b t2 t3 (H3 (S i) u0 (CHead c (Bind b) 
x) t2 (fsubst0_fst (S i) u0 (CHead c (Bind b) u) t2 (CHead c (Bind b) x) 
(csubst0_snd_bind b i u0 u x H9 c)) e (getl_head (Bind b) i c (CHead e (Bind 
Abbr) u0) H6 u))) (pc3_fsubst0 c (THead (Bind b) u t3) (THead (Bind b) u t3) 
(pc3_refl c (THead (Bind b) u t3)) i u0 c (THead (Bind b) x t3) (fsubst0_snd 
i u0 c (THead (Bind b) u t3) (THead (Bind b) x t3) (subst0_fst u0 x u i H9 t3 
(Bind b))) e H6)))) (ty3_correct g (CHead c (Bind b) x) t2 t3 (H3 (S i) u0 
(CHead c (Bind b) x) t2 (fsubst0_fst (S i) u0 (CHead c (Bind b) u) t2 (CHead 
c (Bind b) x) (csubst0_snd_bind b i u0 u x H9 c)) e (getl_head (Bind b) i c 
(CHead e (Bind Abbr) u0) H6 u)))))) (ty3_correct g (CHead c (Bind b) u) t2 t3 
H2)) t5 H8)))) H7)) (\lambda (H7: (ex2 T (\lambda (t6: T).(eq T t5 (THead 
(Bind b) u t6))) (\lambda (t6: T).(subst0 (s (Bind b) i) u0 t2 
t6)))).(ex2_ind T (\lambda (t6: T).(eq T t5 (THead (Bind b) u t6))) (\lambda 
(t6: T).(subst0 (s (Bind b) i) u0 t2 t6)) (ty3 g c t5 (THead (Bind b) u t3)) 
(\lambda (x: T).(\lambda (H8: (eq T t5 (THead (Bind b) u x))).(\lambda (H9: 
(subst0 (s (Bind b) i) u0 t2 x)).(eq_ind_r T (THead (Bind b) u x) (\lambda 
(t6: T).(ty3 g c t6 (THead (Bind b) u t3))) (ex_ind T (\lambda (t6: T).(ty3 g 
(CHead c (Bind b) u) t3 t6)) (ty3 g c (THead (Bind b) u x) (THead (Bind b) u 
t3)) (\lambda (x0: T).(\lambda (_: (ty3 g (CHead c (Bind b) u) t3 
x0)).(ty3_bind g c u t0 H0 b x t3 (H3 (S i) u0 (CHead c (Bind b) u) x 
(fsubst0_snd (S i) u0 (CHead c (Bind b) u) t2 x H9) e (getl_head (Bind b) i c 
(CHead e (Bind Abbr) u0) H6 u))))) (ty3_correct g (CHead c (Bind b) u) x t3 
(H3 (S i) u0 (CHead c (Bind b) u) x (fsubst0_snd (S i) u0 (CHead c (Bind b) 
u) t2 x H9) e (getl_head (Bind b) i c (CHead e (Bind Abbr) u0) H6 u)))) t5 
H8)))) H7)) (\lambda (H7: (ex3_2 T T (\lambda (u2: T).(\lambda (t6: T).(eq T 
t5 (THead (Bind b) u2 t6)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u0 u 
u2))) (\lambda (_: T).(\lambda (t6: T).(subst0 (s (Bind b) i) u0 t2 
t6))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t6: T).(eq T t5 (THead 
(Bind b) u2 t6)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u0 u u2))) 
(\lambda (_: T).(\lambda (t6: T).(subst0 (s (Bind b) i) u0 t2 t6))) (ty3 g c 
t5 (THead (Bind b) u t3)) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H8: (eq 
T t5 (THead (Bind b) x0 x1))).(\lambda (H9: (subst0 i u0 u x0)).(\lambda 
(H10: (subst0 (s (Bind b) i) u0 t2 x1)).(eq_ind_r T (THead (Bind b) x0 x1) 
(\lambda (t6: T).(ty3 g c t6 (THead (Bind b) u t3))) (ex_ind T (\lambda (t6: 
T).(ty3 g (CHead c (Bind b) u) t3 t6)) (ty3 g c (THead (Bind b) x0 x1) (THead 
(Bind b) u t3)) (\lambda (x: T).(\lambda (H11: (ty3 g (CHead c (Bind b) u) t3 
x)).(ex_ind T (\lambda (t6: T).(ty3 g (CHead c (Bind b) x0) t3 t6)) (ty3 g c 
(THead (Bind b) x0 x1) (THead (Bind b) u t3)) (\lambda (x2: T).(\lambda (_: 
(ty3 g (CHead c (Bind b) x0) t3 x2)).(ty3_conv g c (THead (Bind b) u t3) 
(THead (Bind b) u x) (ty3_bind g c u t0 H0 b t3 x H11) (THead (Bind b) x0 x1) 
(THead (Bind b) x0 t3) (ty3_bind g c x0 t0 (H1 i u0 c x0 (fsubst0_snd i u0 c 
u x0 H9) e H6) b x1 t3 (H3 (S i) u0 (CHead c (Bind b) x0) x1 (fsubst0_both (S 
i) u0 (CHead c (Bind b) u) t2 x1 H10 (CHead c (Bind b) x0) (csubst0_snd_bind 
b i u0 u x0 H9 c)) e (getl_head (Bind b) i c (CHead e (Bind Abbr) u0) H6 u))) 
(pc3_fsubst0 c (THead (Bind b) u t3) (THead (Bind b) u t3) (pc3_refl c (THead 
(Bind b) u t3)) i u0 c (THead (Bind b) x0 t3) (fsubst0_snd i u0 c (THead 
(Bind b) u t3) (THead (Bind b) x0 t3) (subst0_fst u0 x0 u i H9 t3 (Bind b))) 
e H6)))) (ty3_correct g (CHead c (Bind b) x0) x1 t3 (H3 (S i) u0 (CHead c 
(Bind b) x0) x1 (fsubst0_both (S i) u0 (CHead c (Bind b) u) t2 x1 H10 (CHead 
c (Bind b) x0) (csubst0_snd_bind b i u0 u x0 H9 c)) e (getl_head (Bind b) i c 
(CHead e (Bind Abbr) u0) H6 u)))))) (ty3_correct g (CHead c (Bind b) u) t2 t3 
H2)) t5 H8)))))) H7)) (subst0_gen_head (Bind b) u0 u t2 t5 i H5)))))) 
(\lambda (c3: C).(\lambda (H5: (csubst0 i u0 c c3)).(\lambda (e: C).(\lambda 
(H6: (getl i c (CHead e (Bind Abbr) u0))).(ex_ind T (\lambda (t5: T).(ty3 g 
(CHead c3 (Bind b) u) t3 t5)) (ty3 g c3 (THead (Bind b) u t2) (THead (Bind b) 
u t3)) (\lambda (x: T).(\lambda (_: (ty3 g (CHead c3 (Bind b) u) t3 
x)).(ty3_bind g c3 u t0 (H1 i u0 c3 u (fsubst0_fst i u0 c u c3 H5) e H6) b t2 
t3 (H3 (S i) u0 (CHead c3 (Bind b) u) t2 (fsubst0_fst (S i) u0 (CHead c (Bind 
b) u) t2 (CHead c3 (Bind b) u) (csubst0_fst_bind b i c c3 u0 H5 u)) e 
(getl_head (Bind b) i c (CHead e (Bind Abbr) u0) H6 u))))) (ty3_correct g 
(CHead c3 (Bind b) u) t2 t3 (H3 (S i) u0 (CHead c3 (Bind b) u) t2 
(fsubst0_fst (S i) u0 (CHead c (Bind b) u) t2 (CHead c3 (Bind b) u) 
(csubst0_fst_bind b i c c3 u0 H5 u)) e (getl_head (Bind b) i c (CHead e (Bind 
Abbr) u0) H6 u)))))))) (\lambda (t5: T).(\lambda (H5: (subst0 i u0 (THead 
(Bind b) u t2) t5)).(\lambda (c3: C).(\lambda (H6: (csubst0 i u0 c 
c3)).(\lambda (e: C).(\lambda (H7: (getl i c (CHead e (Bind Abbr) 
u0))).(or3_ind (ex2 T (\lambda (u2: T).(eq T t5 (THead (Bind b) u2 t2))) 
(\lambda (u2: T).(subst0 i u0 u u2))) (ex2 T (\lambda (t6: T).(eq T t5 (THead 
(Bind b) u t6))) (\lambda (t6: T).(subst0 (s (Bind b) i) u0 t2 t6))) (ex3_2 T 
T (\lambda (u2: T).(\lambda (t6: T).(eq T t5 (THead (Bind b) u2 t6)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u0 u u2))) (\lambda (_: 
T).(\lambda (t6: T).(subst0 (s (Bind b) i) u0 t2 t6)))) (ty3 g c3 t5 (THead 
(Bind b) u t3)) (\lambda (H8: (ex2 T (\lambda (u2: T).(eq T t5 (THead (Bind 
b) u2 t2))) (\lambda (u2: T).(subst0 i u0 u u2)))).(ex2_ind T (\lambda (u2: 
T).(eq T t5 (THead (Bind b) u2 t2))) (\lambda (u2: T).(subst0 i u0 u u2)) 
(ty3 g c3 t5 (THead (Bind b) u t3)) (\lambda (x: T).(\lambda (H9: (eq T t5 
(THead (Bind b) x t2))).(\lambda (H10: (subst0 i u0 u x)).(eq_ind_r T (THead 
(Bind b) x t2) (\lambda (t6: T).(ty3 g c3 t6 (THead (Bind b) u t3))) (ex_ind 
T (\lambda (t6: T).(ty3 g (CHead c3 (Bind b) u) t3 t6)) (ty3 g c3 (THead 
(Bind b) x t2) (THead (Bind b) u t3)) (\lambda (x0: T).(\lambda (H11: (ty3 g 
(CHead c3 (Bind b) u) t3 x0)).(ex_ind T (\lambda (t6: T).(ty3 g (CHead c3 
(Bind b) u) x0 t6)) (ty3 g c3 (THead (Bind b) x t2) (THead (Bind b) u t3)) 
(\lambda (x1: T).(\lambda (_: (ty3 g (CHead c3 (Bind b) u) x0 x1)).(ex_ind T 
(\lambda (t6: T).(ty3 g (CHead c3 (Bind b) x) t3 t6)) (ty3 g c3 (THead (Bind 
b) x t2) (THead (Bind b) u t3)) (\lambda (x2: T).(\lambda (_: (ty3 g (CHead 
c3 (Bind b) x) t3 x2)).(ty3_conv g c3 (THead (Bind b) u t3) (THead (Bind b) u 
x0) (ty3_bind g c3 u t0 (H1 i u0 c3 u (fsubst0_fst i u0 c u c3 H6) e H7) b t3 
x0 H11) (THead (Bind b) x t2) (THead (Bind b) x t3) (ty3_bind g c3 x t0 (H1 i 
u0 c3 x (fsubst0_both i u0 c u x H10 c3 H6) e H7) b t2 t3 (H3 (S i) u0 (CHead 
c3 (Bind b) x) t2 (fsubst0_fst (S i) u0 (CHead c (Bind b) u) t2 (CHead c3 
(Bind b) x) (csubst0_both_bind b i u0 u x H10 c c3 H6)) e (getl_head (Bind b) 
i c (CHead e (Bind Abbr) u0) H7 u))) (pc3_fsubst0 c (THead (Bind b) u t3) 
(THead (Bind b) u t3) (pc3_refl c (THead (Bind b) u t3)) i u0 c3 (THead (Bind 
b) x t3) (fsubst0_both i u0 c (THead (Bind b) u t3) (THead (Bind b) x t3) 
(subst0_fst u0 x u i H10 t3 (Bind b)) c3 H6) e H7)))) (ty3_correct g (CHead 
c3 (Bind b) x) t2 t3 (H3 (S i) u0 (CHead c3 (Bind b) x) t2 (fsubst0_fst (S i) 
u0 (CHead c (Bind b) u) t2 (CHead c3 (Bind b) x) (csubst0_both_bind b i u0 u 
x H10 c c3 H6)) e (getl_head (Bind b) i c (CHead e (Bind Abbr) u0) H7 u)))))) 
(ty3_correct g (CHead c3 (Bind b) u) t3 x0 H11)))) (ty3_correct g (CHead c3 
(Bind b) u) t2 t3 (H3 (S i) u0 (CHead c3 (Bind b) u) t2 (fsubst0_fst (S i) u0 
(CHead c (Bind b) u) t2 (CHead c3 (Bind b) u) (csubst0_fst_bind b i c c3 u0 
H6 u)) e (getl_head (Bind b) i c (CHead e (Bind Abbr) u0) H7 u)))) t5 H9)))) 
H8)) (\lambda (H8: (ex2 T (\lambda (t6: T).(eq T t5 (THead (Bind b) u t6))) 
(\lambda (t6: T).(subst0 (s (Bind b) i) u0 t2 t6)))).(ex2_ind T (\lambda (t6: 
T).(eq T t5 (THead (Bind b) u t6))) (\lambda (t6: T).(subst0 (s (Bind b) i) 
u0 t2 t6)) (ty3 g c3 t5 (THead (Bind b) u t3)) (\lambda (x: T).(\lambda (H9: 
(eq T t5 (THead (Bind b) u x))).(\lambda (H10: (subst0 (s (Bind b) i) u0 t2 
x)).(eq_ind_r T (THead (Bind b) u x) (\lambda (t6: T).(ty3 g c3 t6 (THead 
(Bind b) u t3))) (ex_ind T (\lambda (t6: T).(ty3 g (CHead c3 (Bind b) u) t3 
t6)) (ty3 g c3 (THead (Bind b) u x) (THead (Bind b) u t3)) (\lambda (x0: 
T).(\lambda (_: (ty3 g (CHead c3 (Bind b) u) t3 x0)).(ty3_bind g c3 u t0 (H1 
i u0 c3 u (fsubst0_fst i u0 c u c3 H6) e H7) b x t3 (H3 (S i) u0 (CHead c3 
(Bind b) u) x (fsubst0_both (S i) u0 (CHead c (Bind b) u) t2 x H10 (CHead c3 
(Bind b) u) (csubst0_fst_bind b i c c3 u0 H6 u)) e (getl_head (Bind b) i c 
(CHead e (Bind Abbr) u0) H7 u))))) (ty3_correct g (CHead c3 (Bind b) u) x t3 
(H3 (S i) u0 (CHead c3 (Bind b) u) x (fsubst0_both (S i) u0 (CHead c (Bind b) 
u) t2 x H10 (CHead c3 (Bind b) u) (csubst0_fst_bind b i c c3 u0 H6 u)) e 
(getl_head (Bind b) i c (CHead e (Bind Abbr) u0) H7 u)))) t5 H9)))) H8)) 
(\lambda (H8: (ex3_2 T T (\lambda (u2: T).(\lambda (t6: T).(eq T t5 (THead 
(Bind b) u2 t6)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u0 u u2))) 
(\lambda (_: T).(\lambda (t6: T).(subst0 (s (Bind b) i) u0 t2 
t6))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t6: T).(eq T t5 (THead 
(Bind b) u2 t6)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u0 u u2))) 
(\lambda (_: T).(\lambda (t6: T).(subst0 (s (Bind b) i) u0 t2 t6))) (ty3 g c3 
t5 (THead (Bind b) u t3)) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H9: (eq 
T t5 (THead (Bind b) x0 x1))).(\lambda (H10: (subst0 i u0 u x0)).(\lambda 
(H11: (subst0 (s (Bind b) i) u0 t2 x1)).(eq_ind_r T (THead (Bind b) x0 x1) 
(\lambda (t6: T).(ty3 g c3 t6 (THead (Bind b) u t3))) (ex_ind T (\lambda (t6: 
T).(ty3 g (CHead c3 (Bind b) u) t3 t6)) (ty3 g c3 (THead (Bind b) x0 x1) 
(THead (Bind b) u t3)) (\lambda (x: T).(\lambda (H12: (ty3 g (CHead c3 (Bind 
b) u) t3 x)).(ex_ind T (\lambda (t6: T).(ty3 g (CHead c3 (Bind b) u) x t6)) 
(ty3 g c3 (THead (Bind b) x0 x1) (THead (Bind b) u t3)) (\lambda (x2: 
T).(\lambda (_: (ty3 g (CHead c3 (Bind b) u) x x2)).(ex_ind T (\lambda (t6: 
T).(ty3 g (CHead c3 (Bind b) x0) t3 t6)) (ty3 g c3 (THead (Bind b) x0 x1) 
(THead (Bind b) u t3)) (\lambda (x3: T).(\lambda (_: (ty3 g (CHead c3 (Bind 
b) x0) t3 x3)).(ty3_conv g c3 (THead (Bind b) u t3) (THead (Bind b) u x) 
(ty3_bind g c3 u t0 (H1 i u0 c3 u (fsubst0_fst i u0 c u c3 H6) e H7) b t3 x 
H12) (THead (Bind b) x0 x1) (THead (Bind b) x0 t3) (ty3_bind g c3 x0 t0 (H1 i 
u0 c3 x0 (fsubst0_both i u0 c u x0 H10 c3 H6) e H7) b x1 t3 (H3 (S i) u0 
(CHead c3 (Bind b) x0) x1 (fsubst0_both (S i) u0 (CHead c (Bind b) u) t2 x1 
H11 (CHead c3 (Bind b) x0) (csubst0_both_bind b i u0 u x0 H10 c c3 H6)) e 
(getl_head (Bind b) i c (CHead e (Bind Abbr) u0) H7 u))) (pc3_fsubst0 c 
(THead (Bind b) u t3) (THead (Bind b) u t3) (pc3_refl c (THead (Bind b) u 
t3)) i u0 c3 (THead (Bind b) x0 t3) (fsubst0_both i u0 c (THead (Bind b) u 
t3) (THead (Bind b) x0 t3) (subst0_fst u0 x0 u i H10 t3 (Bind b)) c3 H6) e 
H7)))) (ty3_correct g (CHead c3 (Bind b) x0) x1 t3 (H3 (S i) u0 (CHead c3 
(Bind b) x0) x1 (fsubst0_both (S i) u0 (CHead c (Bind b) u) t2 x1 H11 (CHead 
c3 (Bind b) x0) (csubst0_both_bind b i u0 u x0 H10 c c3 H6)) e (getl_head 
(Bind b) i c (CHead e (Bind Abbr) u0) H7 u)))))) (ty3_correct g (CHead c3 
(Bind b) u) t3 x H12)))) (ty3_correct g (CHead c3 (Bind b) u) t2 t3 (H3 (S i) 
u0 (CHead c3 (Bind b) u) t2 (fsubst0_fst (S i) u0 (CHead c (Bind b) u) t2 
(CHead c3 (Bind b) u) (csubst0_fst_bind b i c c3 u0 H6 u)) e (getl_head (Bind 
b) i c (CHead e (Bind Abbr) u0) H7 u)))) t5 H9)))))) H8)) (subst0_gen_head 
(Bind b) u0 u t2 t5 i H5)))))))) c2 t4 H4)))))))))))))))) (\lambda (c: 
C).(\lambda (w: T).(\lambda (u: T).(\lambda (H0: (ty3 g c w u)).(\lambda (H1: 
((\forall (i: nat).(\forall (u0: T).(\forall (c2: C).(\forall (t2: 
T).((fsubst0 i u0 c w c2 t2) \to (\forall (e: C).((getl i c (CHead e (Bind 
Abbr) u0)) \to (ty3 g c2 t2 u)))))))))).(\lambda (v: T).(\lambda (t0: 
T).(\lambda (H2: (ty3 g c v (THead (Bind Abst) u t0))).(\lambda (H3: 
((\forall (i: nat).(\forall (u0: T).(\forall (c2: C).(\forall (t2: 
T).((fsubst0 i u0 c v c2 t2) \to (\forall (e: C).((getl i c (CHead e (Bind 
Abbr) u0)) \to (ty3 g c2 t2 (THead (Bind Abst) u t0))))))))))).(\lambda (i: 
nat).(\lambda (u0: T).(\lambda (c2: C).(\lambda (t2: T).(\lambda (H4: 
(fsubst0 i u0 c (THead (Flat Appl) w v) c2 t2)).(fsubst0_ind i u0 c (THead 
(Flat Appl) w v) (\lambda (c0: C).(\lambda (t3: T).(\forall (e: C).((getl i c 
(CHead e (Bind Abbr) u0)) \to (ty3 g c0 t3 (THead (Flat Appl) w (THead (Bind 
Abst) u t0))))))) (\lambda (t3: T).(\lambda (H5: (subst0 i u0 (THead (Flat 
Appl) w v) t3)).(\lambda (e: C).(\lambda (H6: (getl i c (CHead e (Bind Abbr) 
u0))).(or3_ind (ex2 T (\lambda (u2: T).(eq T t3 (THead (Flat Appl) u2 v))) 
(\lambda (u2: T).(subst0 i u0 w u2))) (ex2 T (\lambda (t4: T).(eq T t3 (THead 
(Flat Appl) w t4))) (\lambda (t4: T).(subst0 (s (Flat Appl) i) u0 v t4))) 
(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 
t4)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u0 w u2))) (\lambda (_: 
T).(\lambda (t4: T).(subst0 (s (Flat Appl) i) u0 v t4)))) (ty3 g c t3 (THead 
(Flat Appl) w (THead (Bind Abst) u t0))) (\lambda (H7: (ex2 T (\lambda (u2: 
T).(eq T t3 (THead (Flat Appl) u2 v))) (\lambda (u2: T).(subst0 i u0 w 
u2)))).(ex2_ind T (\lambda (u2: T).(eq T t3 (THead (Flat Appl) u2 v))) 
(\lambda (u2: T).(subst0 i u0 w u2)) (ty3 g c t3 (THead (Flat Appl) w (THead 
(Bind Abst) u t0))) (\lambda (x: T).(\lambda (H8: (eq T t3 (THead (Flat Appl) 
x v))).(\lambda (H9: (subst0 i u0 w x)).(eq_ind_r T (THead (Flat Appl) x v) 
(\lambda (t4: T).(ty3 g c t4 (THead (Flat Appl) w (THead (Bind Abst) u t0)))) 
(ex_ind T (\lambda (t4: T).(ty3 g c (THead (Bind Abst) u t0) t4)) (ty3 g c 
(THead (Flat Appl) x v) (THead (Flat Appl) w (THead (Bind Abst) u t0))) 
(\lambda (x0: T).(\lambda (H10: (ty3 g c (THead (Bind Abst) u t0) 
x0)).(ex3_2_ind T T (\lambda (t4: T).(\lambda (_: T).(pc3 c (THead (Bind 
Abst) u t4) x0))) (\lambda (_: T).(\lambda (t5: T).(ty3 g c u t5))) (\lambda 
(t4: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) u) t0 t4))) (ty3 g c 
(THead (Flat Appl) x v) (THead (Flat Appl) w (THead (Bind Abst) u t0))) 
(\lambda (x1: T).(\lambda (x2: T).(\lambda (_: (pc3 c (THead (Bind Abst) u 
x1) x0)).(\lambda (_: (ty3 g c u x2)).(\lambda (H13: (ty3 g (CHead c (Bind 
Abst) u) t0 x1)).(ex_ind T (\lambda (t4: T).(ty3 g c u t4)) (ty3 g c (THead 
(Flat Appl) x v) (THead (Flat Appl) w (THead (Bind Abst) u t0))) (\lambda 
(x3: T).(\lambda (H14: (ty3 g c u x3)).(ty3_conv g c (THead (Flat Appl) w 
(THead (Bind Abst) u t0)) (THead (Flat Appl) w (THead (Bind Abst) u x1)) 
(ty3_appl g c w u H0 (THead (Bind Abst) u t0) x1 (ty3_bind g c u x3 H14 Abst 
t0 x1 H13)) (THead (Flat Appl) x v) (THead (Flat Appl) x (THead (Bind Abst) u 
t0)) (ty3_appl g c x u (H1 i u0 c x (fsubst0_snd i u0 c w x H9) e H6) v t0 
H2) (pc3_fsubst0 c (THead (Flat Appl) w (THead (Bind Abst) u t0)) (THead 
(Flat Appl) w (THead (Bind Abst) u t0)) (pc3_refl c (THead (Flat Appl) w 
(THead (Bind Abst) u t0))) i u0 c (THead (Flat Appl) x (THead (Bind Abst) u 
t0)) (fsubst0_snd i u0 c (THead (Flat Appl) w (THead (Bind Abst) u t0)) 
(THead (Flat Appl) x (THead (Bind Abst) u t0)) (subst0_fst u0 x w i H9 (THead 
(Bind Abst) u t0) (Flat Appl))) e H6)))) (ty3_correct g c x u (H1 i u0 c x 
(fsubst0_snd i u0 c w x H9) e H6)))))))) (ty3_gen_bind g Abst c u t0 x0 
H10)))) (ty3_correct g c v (THead (Bind Abst) u t0) H2)) t3 H8)))) H7)) 
(\lambda (H7: (ex2 T (\lambda (t4: T).(eq T t3 (THead (Flat Appl) w t4))) 
(\lambda (t4: T).(subst0 (s (Flat Appl) i) u0 v t4)))).(ex2_ind T (\lambda 
(t4: T).(eq T t3 (THead (Flat Appl) w t4))) (\lambda (t4: T).(subst0 (s (Flat 
Appl) i) u0 v t4)) (ty3 g c t3 (THead (Flat Appl) w (THead (Bind Abst) u 
t0))) (\lambda (x: T).(\lambda (H8: (eq T t3 (THead (Flat Appl) w 
x))).(\lambda (H9: (subst0 (s (Flat Appl) i) u0 v x)).(eq_ind_r T (THead 
(Flat Appl) w x) (\lambda (t4: T).(ty3 g c t4 (THead (Flat Appl) w (THead 
(Bind Abst) u t0)))) (ty3_appl g c w u H0 x t0 (H3 (s (Flat Appl) i) u0 c x 
(fsubst0_snd (s (Flat Appl) i) u0 c v x H9) e H6)) t3 H8)))) H7)) (\lambda 
(H7: (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) 
u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u0 w u2))) (\lambda (_: 
T).(\lambda (t4: T).(subst0 (s (Flat Appl) i) u0 v t4))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u0 w u2))) (\lambda (_: 
T).(\lambda (t4: T).(subst0 (s (Flat Appl) i) u0 v t4))) (ty3 g c t3 (THead 
(Flat Appl) w (THead (Bind Abst) u t0))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H8: (eq T t3 (THead (Flat Appl) x0 x1))).(\lambda (H9: (subst0 i 
u0 w x0)).(\lambda (H10: (subst0 (s (Flat Appl) i) u0 v x1)).(eq_ind_r T 
(THead (Flat Appl) x0 x1) (\lambda (t4: T).(ty3 g c t4 (THead (Flat Appl) w 
(THead (Bind Abst) u t0)))) (ex_ind T (\lambda (t4: T).(ty3 g c (THead (Bind 
Abst) u t0) t4)) (ty3 g c (THead (Flat Appl) x0 x1) (THead (Flat Appl) w 
(THead (Bind Abst) u t0))) (\lambda (x: T).(\lambda (H11: (ty3 g c (THead 
(Bind Abst) u t0) x)).(ex3_2_ind T T (\lambda (t4: T).(\lambda (_: T).(pc3 c 
(THead (Bind Abst) u t4) x))) (\lambda (_: T).(\lambda (t5: T).(ty3 g c u 
t5))) (\lambda (t4: T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) u) t0 
t4))) (ty3 g c (THead (Flat Appl) x0 x1) (THead (Flat Appl) w (THead (Bind 
Abst) u t0))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (_: (pc3 c (THead 
(Bind Abst) u x2) x)).(\lambda (_: (ty3 g c u x3)).(\lambda (H14: (ty3 g 
(CHead c (Bind Abst) u) t0 x2)).(ex_ind T (\lambda (t4: T).(ty3 g c u t4)) 
(ty3 g c (THead (Flat Appl) x0 x1) (THead (Flat Appl) w (THead (Bind Abst) u 
t0))) (\lambda (x4: T).(\lambda (H15: (ty3 g c u x4)).(ty3_conv g c (THead 
(Flat Appl) w (THead (Bind Abst) u t0)) (THead (Flat Appl) w (THead (Bind 
Abst) u x2)) (ty3_appl g c w u H0 (THead (Bind Abst) u t0) x2 (ty3_bind g c u 
x4 H15 Abst t0 x2 H14)) (THead (Flat Appl) x0 x1) (THead (Flat Appl) x0 
(THead (Bind Abst) u t0)) (ty3_appl g c x0 u (H1 i u0 c x0 (fsubst0_snd i u0 
c w x0 H9) e H6) x1 t0 (H3 (s (Flat Appl) i) u0 c x1 (fsubst0_snd (s (Flat 
Appl) i) u0 c v x1 H10) e H6)) (pc3_fsubst0 c (THead (Flat Appl) w (THead 
(Bind Abst) u t0)) (THead (Flat Appl) w (THead (Bind Abst) u t0)) (pc3_refl c 
(THead (Flat Appl) w (THead (Bind Abst) u t0))) i u0 c (THead (Flat Appl) x0 
(THead (Bind Abst) u t0)) (fsubst0_snd i u0 c (THead (Flat Appl) w (THead 
(Bind Abst) u t0)) (THead (Flat Appl) x0 (THead (Bind Abst) u t0)) 
(subst0_fst u0 x0 w i H9 (THead (Bind Abst) u t0) (Flat Appl))) e H6)))) 
(ty3_correct g c w u H0))))))) (ty3_gen_bind g Abst c u t0 x H11)))) 
(ty3_correct g c v (THead (Bind Abst) u t0) H2)) t3 H8)))))) H7)) 
(subst0_gen_head (Flat Appl) u0 w v t3 i H5)))))) (\lambda (c3: C).(\lambda 
(H5: (csubst0 i u0 c c3)).(\lambda (e: C).(\lambda (H6: (getl i c (CHead e 
(Bind Abbr) u0))).(ty3_appl g c3 w u (H1 i u0 c3 w (fsubst0_fst i u0 c w c3 
H5) e H6) v t0 (H3 i u0 c3 v (fsubst0_fst i u0 c v c3 H5) e H6)))))) (\lambda 
(t3: T).(\lambda (H5: (subst0 i u0 (THead (Flat Appl) w v) t3)).(\lambda (c3: 
C).(\lambda (H6: (csubst0 i u0 c c3)).(\lambda (e: C).(\lambda (H7: (getl i c 
(CHead e (Bind Abbr) u0))).(or3_ind (ex2 T (\lambda (u2: T).(eq T t3 (THead 
(Flat Appl) u2 v))) (\lambda (u2: T).(subst0 i u0 w u2))) (ex2 T (\lambda 
(t4: T).(eq T t3 (THead (Flat Appl) w t4))) (\lambda (t4: T).(subst0 (s (Flat 
Appl) i) u0 v t4))) (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 
(THead (Flat Appl) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u0 w 
u2))) (\lambda (_: T).(\lambda (t4: T).(subst0 (s (Flat Appl) i) u0 v t4)))) 
(ty3 g c3 t3 (THead (Flat Appl) w (THead (Bind Abst) u t0))) (\lambda (H8: 
(ex2 T (\lambda (u2: T).(eq T t3 (THead (Flat Appl) u2 v))) (\lambda (u2: 
T).(subst0 i u0 w u2)))).(ex2_ind T (\lambda (u2: T).(eq T t3 (THead (Flat 
Appl) u2 v))) (\lambda (u2: T).(subst0 i u0 w u2)) (ty3 g c3 t3 (THead (Flat 
Appl) w (THead (Bind Abst) u t0))) (\lambda (x: T).(\lambda (H9: (eq T t3 
(THead (Flat Appl) x v))).(\lambda (H10: (subst0 i u0 w x)).(eq_ind_r T 
(THead (Flat Appl) x v) (\lambda (t4: T).(ty3 g c3 t4 (THead (Flat Appl) w 
(THead (Bind Abst) u t0)))) (ex_ind T (\lambda (t4: T).(ty3 g c3 (THead (Bind 
Abst) u t0) t4)) (ty3 g c3 (THead (Flat Appl) x v) (THead (Flat Appl) w 
(THead (Bind Abst) u t0))) (\lambda (x0: T).(\lambda (H11: (ty3 g c3 (THead 
(Bind Abst) u t0) x0)).(ex3_2_ind T T (\lambda (t4: T).(\lambda (_: T).(pc3 
c3 (THead (Bind Abst) u t4) x0))) (\lambda (_: T).(\lambda (t5: T).(ty3 g c3 
u t5))) (\lambda (t4: T).(\lambda (_: T).(ty3 g (CHead c3 (Bind Abst) u) t0 
t4))) (ty3 g c3 (THead (Flat Appl) x v) (THead (Flat Appl) w (THead (Bind 
Abst) u t0))) (\lambda (x1: T).(\lambda (x2: T).(\lambda (_: (pc3 c3 (THead 
(Bind Abst) u x1) x0)).(\lambda (H13: (ty3 g c3 u x2)).(\lambda (H14: (ty3 g 
(CHead c3 (Bind Abst) u) t0 x1)).(ty3_conv g c3 (THead (Flat Appl) w (THead 
(Bind Abst) u t0)) (THead (Flat Appl) w (THead (Bind Abst) u x1)) (ty3_appl g 
c3 w u (H1 i u0 c3 w (fsubst0_fst i u0 c w c3 H6) e H7) (THead (Bind Abst) u 
t0) x1 (ty3_bind g c3 u x2 H13 Abst t0 x1 H14)) (THead (Flat Appl) x v) 
(THead (Flat Appl) x (THead (Bind Abst) u t0)) (ty3_appl g c3 x u (H1 i u0 c3 
x (fsubst0_both i u0 c w x H10 c3 H6) e H7) v t0 (H3 i u0 c3 v (fsubst0_fst i 
u0 c v c3 H6) e H7)) (pc3_fsubst0 c (THead (Flat Appl) w (THead (Bind Abst) u 
t0)) (THead (Flat Appl) w (THead (Bind Abst) u t0)) (pc3_refl c (THead (Flat 
Appl) w (THead (Bind Abst) u t0))) i u0 c3 (THead (Flat Appl) x (THead (Bind 
Abst) u t0)) (fsubst0_both i u0 c (THead (Flat Appl) w (THead (Bind Abst) u 
t0)) (THead (Flat Appl) x (THead (Bind Abst) u t0)) (subst0_fst u0 x w i H10 
(THead (Bind Abst) u t0) (Flat Appl)) c3 H6) e H7))))))) (ty3_gen_bind g Abst 
c3 u t0 x0 H11)))) (ty3_correct g c3 v (THead (Bind Abst) u t0) (H3 i u0 c3 v 
(fsubst0_fst i u0 c v c3 H6) e H7))) t3 H9)))) H8)) (\lambda (H8: (ex2 T 
(\lambda (t4: T).(eq T t3 (THead (Flat Appl) w t4))) (\lambda (t4: T).(subst0 
(s (Flat Appl) i) u0 v t4)))).(ex2_ind T (\lambda (t4: T).(eq T t3 (THead 
(Flat Appl) w t4))) (\lambda (t4: T).(subst0 (s (Flat Appl) i) u0 v t4)) (ty3 
g c3 t3 (THead (Flat Appl) w (THead (Bind Abst) u t0))) (\lambda (x: 
T).(\lambda (H9: (eq T t3 (THead (Flat Appl) w x))).(\lambda (H10: (subst0 (s 
(Flat Appl) i) u0 v x)).(eq_ind_r T (THead (Flat Appl) w x) (\lambda (t4: 
T).(ty3 g c3 t4 (THead (Flat Appl) w (THead (Bind Abst) u t0)))) (ty3_appl g 
c3 w u (H1 i u0 c3 w (fsubst0_fst i u0 c w c3 H6) e H7) x t0 (H3 i u0 c3 x 
(fsubst0_both i u0 c v x H10 c3 H6) e H7)) t3 H9)))) H8)) (\lambda (H8: 
(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 
t4)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u0 w u2))) (\lambda (_: 
T).(\lambda (t4: T).(subst0 (s (Flat Appl) i) u0 v t4))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Flat Appl) u2 t4)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u0 w u2))) (\lambda (_: 
T).(\lambda (t4: T).(subst0 (s (Flat Appl) i) u0 v t4))) (ty3 g c3 t3 (THead 
(Flat Appl) w (THead (Bind Abst) u t0))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H9: (eq T t3 (THead (Flat Appl) x0 x1))).(\lambda (H10: (subst0 
i u0 w x0)).(\lambda (H11: (subst0 (s (Flat Appl) i) u0 v x1)).(eq_ind_r T 
(THead (Flat Appl) x0 x1) (\lambda (t4: T).(ty3 g c3 t4 (THead (Flat Appl) w 
(THead (Bind Abst) u t0)))) (ex_ind T (\lambda (t4: T).(ty3 g c3 (THead (Bind 
Abst) u t0) t4)) (ty3 g c3 (THead (Flat Appl) x0 x1) (THead (Flat Appl) w 
(THead (Bind Abst) u t0))) (\lambda (x: T).(\lambda (H12: (ty3 g c3 (THead 
(Bind Abst) u t0) x)).(ex3_2_ind T T (\lambda (t4: T).(\lambda (_: T).(pc3 c3 
(THead (Bind Abst) u t4) x))) (\lambda (_: T).(\lambda (t5: T).(ty3 g c3 u 
t5))) (\lambda (t4: T).(\lambda (_: T).(ty3 g (CHead c3 (Bind Abst) u) t0 
t4))) (ty3 g c3 (THead (Flat Appl) x0 x1) (THead (Flat Appl) w (THead (Bind 
Abst) u t0))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (_: (pc3 c3 (THead 
(Bind Abst) u x2) x)).(\lambda (_: (ty3 g c3 u x3)).(\lambda (H15: (ty3 g 
(CHead c3 (Bind Abst) u) t0 x2)).(ex_ind T (\lambda (t4: T).(ty3 g c3 u t4)) 
(ty3 g c3 (THead (Flat Appl) x0 x1) (THead (Flat Appl) w (THead (Bind Abst) u 
t0))) (\lambda (x4: T).(\lambda (H16: (ty3 g c3 u x4)).(ty3_conv g c3 (THead 
(Flat Appl) w (THead (Bind Abst) u t0)) (THead (Flat Appl) w (THead (Bind 
Abst) u x2)) (ty3_appl g c3 w u (H1 i u0 c3 w (fsubst0_fst i u0 c w c3 H6) e 
H7) (THead (Bind Abst) u t0) x2 (ty3_bind g c3 u x4 H16 Abst t0 x2 H15)) 
(THead (Flat Appl) x0 x1) (THead (Flat Appl) x0 (THead (Bind Abst) u t0)) 
(ty3_appl g c3 x0 u (H1 i u0 c3 x0 (fsubst0_both i u0 c w x0 H10 c3 H6) e H7) 
x1 t0 (H3 i u0 c3 x1 (fsubst0_both i u0 c v x1 H11 c3 H6) e H7)) (pc3_fsubst0 
c (THead (Flat Appl) w (THead (Bind Abst) u t0)) (THead (Flat Appl) w (THead 
(Bind Abst) u t0)) (pc3_refl c (THead (Flat Appl) w (THead (Bind Abst) u 
t0))) i u0 c3 (THead (Flat Appl) x0 (THead (Bind Abst) u t0)) (fsubst0_both i 
u0 c (THead (Flat Appl) w (THead (Bind Abst) u t0)) (THead (Flat Appl) x0 
(THead (Bind Abst) u t0)) (subst0_fst u0 x0 w i H10 (THead (Bind Abst) u t0) 
(Flat Appl)) c3 H6) e H7)))) (ty3_correct g c3 w u (H1 i u0 c3 w (fsubst0_fst 
i u0 c w c3 H6) e H7)))))))) (ty3_gen_bind g Abst c3 u t0 x H12)))) 
(ty3_correct g c3 v (THead (Bind Abst) u t0) (H3 i u0 c3 v (fsubst0_fst i u0 
c v c3 H6) e H7))) t3 H9)))))) H8)) (subst0_gen_head (Flat Appl) u0 w v t3 i 
H5)))))))) c2 t2 H4))))))))))))))) (\lambda (c: C).(\lambda (t2: T).(\lambda 
(t3: T).(\lambda (H0: (ty3 g c t2 t3)).(\lambda (H1: ((\forall (i: 
nat).(\forall (u: T).(\forall (c2: C).(\forall (t4: T).((fsubst0 i u c t2 c2 
t4) \to (\forall (e: C).((getl i c (CHead e (Bind Abbr) u)) \to (ty3 g c2 t4 
t3)))))))))).(\lambda (t0: T).(\lambda (H2: (ty3 g c t3 t0)).(\lambda (H3: 
((\forall (i: nat).(\forall (u: T).(\forall (c2: C).(\forall (t4: 
T).((fsubst0 i u c t3 c2 t4) \to (\forall (e: C).((getl i c (CHead e (Bind 
Abbr) u)) \to (ty3 g c2 t4 t0)))))))))).(\lambda (i: nat).(\lambda (u: 
T).(\lambda (c2: C).(\lambda (t4: T).(\lambda (H4: (fsubst0 i u c (THead 
(Flat Cast) t3 t2) c2 t4)).(fsubst0_ind i u c (THead (Flat Cast) t3 t2) 
(\lambda (c0: C).(\lambda (t5: T).(\forall (e: C).((getl i c (CHead e (Bind 
Abbr) u)) \to (ty3 g c0 t5 (THead (Flat Cast) t0 t3)))))) (\lambda (t5: 
T).(\lambda (H5: (subst0 i u (THead (Flat Cast) t3 t2) t5)).(\lambda (e: 
C).(\lambda (H6: (getl i c (CHead e (Bind Abbr) u))).(or3_ind (ex2 T (\lambda 
(u2: T).(eq T t5 (THead (Flat Cast) u2 t2))) (\lambda (u2: T).(subst0 i u t3 
u2))) (ex2 T (\lambda (t6: T).(eq T t5 (THead (Flat Cast) t3 t6))) (\lambda 
(t6: T).(subst0 (s (Flat Cast) i) u t2 t6))) (ex3_2 T T (\lambda (u2: 
T).(\lambda (t6: T).(eq T t5 (THead (Flat Cast) u2 t6)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i u t3 u2))) (\lambda (_: T).(\lambda (t6: 
T).(subst0 (s (Flat Cast) i) u t2 t6)))) (ty3 g c t5 (THead (Flat Cast) t0 
t3)) (\lambda (H7: (ex2 T (\lambda (u2: T).(eq T t5 (THead (Flat Cast) u2 
t2))) (\lambda (u2: T).(subst0 i u t3 u2)))).(ex2_ind T (\lambda (u2: T).(eq 
T t5 (THead (Flat Cast) u2 t2))) (\lambda (u2: T).(subst0 i u t3 u2)) (ty3 g 
c t5 (THead (Flat Cast) t0 t3)) (\lambda (x: T).(\lambda (H8: (eq T t5 (THead 
(Flat Cast) x t2))).(\lambda (H9: (subst0 i u t3 x)).(eq_ind_r T (THead (Flat 
Cast) x t2) (\lambda (t6: T).(ty3 g c t6 (THead (Flat Cast) t0 t3))) (ex_ind 
T (\lambda (t6: T).(ty3 g c t0 t6)) (ty3 g c (THead (Flat Cast) x t2) (THead 
(Flat Cast) t0 t3)) (\lambda (x0: T).(\lambda (H10: (ty3 g c t0 
x0)).(ty3_conv g c (THead (Flat Cast) t0 t3) (THead (Flat Cast) x0 t0) 
(ty3_cast g c t3 t0 H2 x0 H10) (THead (Flat Cast) x t2) (THead (Flat Cast) t0 
x) (ty3_cast g c t2 x (ty3_conv g c x t0 (H3 i u c x (fsubst0_snd i u c t3 x 
H9) e H6) t2 t3 H0 (pc3_s c t3 x (pc3_fsubst0 c t3 t3 (pc3_refl c t3) i u c x 
(fsubst0_snd i u c t3 x H9) e H6))) t0 (H3 i u c x (fsubst0_snd i u c t3 x 
H9) e H6)) (pc3_fsubst0 c (THead (Flat Cast) t0 t3) (THead (Flat Cast) t0 t3) 
(pc3_refl c (THead (Flat Cast) t0 t3)) i u c (THead (Flat Cast) t0 x) 
(fsubst0_snd i u c (THead (Flat Cast) t0 t3) (THead (Flat Cast) t0 x) 
(subst0_snd (Flat Cast) u x t3 i H9 t0)) e H6)))) (ty3_correct g c x t0 (H3 i 
u c x (fsubst0_snd i u c t3 x H9) e H6))) t5 H8)))) H7)) (\lambda (H7: (ex2 T 
(\lambda (t6: T).(eq T t5 (THead (Flat Cast) t3 t6))) (\lambda (t6: 
T).(subst0 (s (Flat Cast) i) u t2 t6)))).(ex2_ind T (\lambda (t6: T).(eq T t5 
(THead (Flat Cast) t3 t6))) (\lambda (t6: T).(subst0 (s (Flat Cast) i) u t2 
t6)) (ty3 g c t5 (THead (Flat Cast) t0 t3)) (\lambda (x: T).(\lambda (H8: (eq 
T t5 (THead (Flat Cast) t3 x))).(\lambda (H9: (subst0 (s (Flat Cast) i) u t2 
x)).(eq_ind_r T (THead (Flat Cast) t3 x) (\lambda (t6: T).(ty3 g c t6 (THead 
(Flat Cast) t0 t3))) (ty3_cast g c x t3 (H1 (s (Flat Cast) i) u c x 
(fsubst0_snd (s (Flat Cast) i) u c t2 x H9) e H6) t0 H2) t5 H8)))) H7)) 
(\lambda (H7: (ex3_2 T T (\lambda (u2: T).(\lambda (t6: T).(eq T t5 (THead 
(Flat Cast) u2 t6)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u t3 u2))) 
(\lambda (_: T).(\lambda (t6: T).(subst0 (s (Flat Cast) i) u t2 
t6))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t6: T).(eq T t5 (THead 
(Flat Cast) u2 t6)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u t3 u2))) 
(\lambda (_: T).(\lambda (t6: T).(subst0 (s (Flat Cast) i) u t2 t6))) (ty3 g 
c t5 (THead (Flat Cast) t0 t3)) (\lambda (x0: T).(\lambda (x1: T).(\lambda 
(H8: (eq T t5 (THead (Flat Cast) x0 x1))).(\lambda (H9: (subst0 i u t3 
x0)).(\lambda (H10: (subst0 (s (Flat Cast) i) u t2 x1)).(eq_ind_r T (THead 
(Flat Cast) x0 x1) (\lambda (t6: T).(ty3 g c t6 (THead (Flat Cast) t0 t3))) 
(ex_ind T (\lambda (t6: T).(ty3 g c t0 t6)) (ty3 g c (THead (Flat Cast) x0 
x1) (THead (Flat Cast) t0 t3)) (\lambda (x: T).(\lambda (H11: (ty3 g c t0 
x)).(ty3_conv g c (THead (Flat Cast) t0 t3) (THead (Flat Cast) x t0) 
(ty3_cast g c t3 t0 H2 x H11) (THead (Flat Cast) x0 x1) (THead (Flat Cast) t0 
x0) (ty3_cast g c x1 x0 (ty3_conv g c x0 t0 (H3 i u c x0 (fsubst0_snd i u c 
t3 x0 H9) e H6) x1 t3 (H1 (s (Flat Cast) i) u c x1 (fsubst0_snd (s (Flat 
Cast) i) u c t2 x1 H10) e H6) (pc3_s c t3 x0 (pc3_fsubst0 c t3 t3 (pc3_refl c 
t3) i u c x0 (fsubst0_snd i u c t3 x0 H9) e H6))) t0 (H3 i u c x0 
(fsubst0_snd i u c t3 x0 H9) e H6)) (pc3_fsubst0 c (THead (Flat Cast) t0 t3) 
(THead (Flat Cast) t0 t3) (pc3_refl c (THead (Flat Cast) t0 t3)) i u c (THead 
(Flat Cast) t0 x0) (fsubst0_snd i u c (THead (Flat Cast) t0 t3) (THead (Flat 
Cast) t0 x0) (subst0_snd (Flat Cast) u x0 t3 i H9 t0)) e H6)))) (ty3_correct 
g c x0 t0 (H3 i u c x0 (fsubst0_snd i u c t3 x0 H9) e H6))) t5 H8)))))) H7)) 
(subst0_gen_head (Flat Cast) u t3 t2 t5 i H5)))))) (\lambda (c3: C).(\lambda 
(H5: (csubst0 i u c c3)).(\lambda (e: C).(\lambda (H6: (getl i c (CHead e 
(Bind Abbr) u))).(ty3_cast g c3 t2 t3 (H1 i u c3 t2 (fsubst0_fst i u c t2 c3 
H5) e H6) t0 (H3 i u c3 t3 (fsubst0_fst i u c t3 c3 H5) e H6)))))) (\lambda 
(t5: T).(\lambda (H5: (subst0 i u (THead (Flat Cast) t3 t2) t5)).(\lambda 
(c3: C).(\lambda (H6: (csubst0 i u c c3)).(\lambda (e: C).(\lambda (H7: (getl 
i c (CHead e (Bind Abbr) u))).(or3_ind (ex2 T (\lambda (u2: T).(eq T t5 
(THead (Flat Cast) u2 t2))) (\lambda (u2: T).(subst0 i u t3 u2))) (ex2 T 
(\lambda (t6: T).(eq T t5 (THead (Flat Cast) t3 t6))) (\lambda (t6: 
T).(subst0 (s (Flat Cast) i) u t2 t6))) (ex3_2 T T (\lambda (u2: T).(\lambda 
(t6: T).(eq T t5 (THead (Flat Cast) u2 t6)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 i u t3 u2))) (\lambda (_: T).(\lambda (t6: T).(subst0 (s (Flat 
Cast) i) u t2 t6)))) (ty3 g c3 t5 (THead (Flat Cast) t0 t3)) (\lambda (H8: 
(ex2 T (\lambda (u2: T).(eq T t5 (THead (Flat Cast) u2 t2))) (\lambda (u2: 
T).(subst0 i u t3 u2)))).(ex2_ind T (\lambda (u2: T).(eq T t5 (THead (Flat 
Cast) u2 t2))) (\lambda (u2: T).(subst0 i u t3 u2)) (ty3 g c3 t5 (THead (Flat 
Cast) t0 t3)) (\lambda (x: T).(\lambda (H9: (eq T t5 (THead (Flat Cast) x 
t2))).(\lambda (H10: (subst0 i u t3 x)).(eq_ind_r T (THead (Flat Cast) x t2) 
(\lambda (t6: T).(ty3 g c3 t6 (THead (Flat Cast) t0 t3))) (ex_ind T (\lambda 
(t6: T).(ty3 g c3 t0 t6)) (ty3 g c3 (THead (Flat Cast) x t2) (THead (Flat 
Cast) t0 t3)) (\lambda (x0: T).(\lambda (H11: (ty3 g c3 t0 x0)).(ty3_conv g 
c3 (THead (Flat Cast) t0 t3) (THead (Flat Cast) x0 t0) (ty3_cast g c3 t3 t0 
(H3 i u c3 t3 (fsubst0_fst i u c t3 c3 H6) e H7) x0 H11) (THead (Flat Cast) x 
t2) (THead (Flat Cast) t0 x) (ty3_cast g c3 t2 x (ty3_conv g c3 x t0 (H3 i u 
c3 x (fsubst0_both i u c t3 x H10 c3 H6) e H7) t2 t3 (H1 i u c3 t2 
(fsubst0_fst i u c t2 c3 H6) e H7) (pc3_s c3 t3 x (pc3_fsubst0 c t3 t3 
(pc3_refl c t3) i u c3 x (fsubst0_both i u c t3 x H10 c3 H6) e H7))) t0 (H3 i 
u c3 x (fsubst0_both i u c t3 x H10 c3 H6) e H7)) (pc3_fsubst0 c (THead (Flat 
Cast) t0 t3) (THead (Flat Cast) t0 t3) (pc3_refl c (THead (Flat Cast) t0 t3)) 
i u c3 (THead (Flat Cast) t0 x) (fsubst0_both i u c (THead (Flat Cast) t0 t3) 
(THead (Flat Cast) t0 x) (subst0_snd (Flat Cast) u x t3 i H10 t0) c3 H6) e 
H7)))) (ty3_correct g c3 t3 t0 (H3 i u c3 t3 (fsubst0_fst i u c t3 c3 H6) e 
H7))) t5 H9)))) H8)) (\lambda (H8: (ex2 T (\lambda (t6: T).(eq T t5 (THead 
(Flat Cast) t3 t6))) (\lambda (t6: T).(subst0 (s (Flat Cast) i) u t2 
t6)))).(ex2_ind T (\lambda (t6: T).(eq T t5 (THead (Flat Cast) t3 t6))) 
(\lambda (t6: T).(subst0 (s (Flat Cast) i) u t2 t6)) (ty3 g c3 t5 (THead 
(Flat Cast) t0 t3)) (\lambda (x: T).(\lambda (H9: (eq T t5 (THead (Flat Cast) 
t3 x))).(\lambda (H10: (subst0 (s (Flat Cast) i) u t2 x)).(eq_ind_r T (THead 
(Flat Cast) t3 x) (\lambda (t6: T).(ty3 g c3 t6 (THead (Flat Cast) t0 t3))) 
(ty3_cast g c3 x t3 (H1 i u c3 x (fsubst0_both i u c t2 x H10 c3 H6) e H7) t0 
(H3 i u c3 t3 (fsubst0_fst i u c t3 c3 H6) e H7)) t5 H9)))) H8)) (\lambda 
(H8: (ex3_2 T T (\lambda (u2: T).(\lambda (t6: T).(eq T t5 (THead (Flat Cast) 
u2 t6)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i u t3 u2))) (\lambda (_: 
T).(\lambda (t6: T).(subst0 (s (Flat Cast) i) u t2 t6))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t6: T).(eq T t5 (THead (Flat Cast) u2 t6)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i u t3 u2))) (\lambda (_: 
T).(\lambda (t6: T).(subst0 (s (Flat Cast) i) u t2 t6))) (ty3 g c3 t5 (THead 
(Flat Cast) t0 t3)) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H9: (eq T t5 
(THead (Flat Cast) x0 x1))).(\lambda (H10: (subst0 i u t3 x0)).(\lambda (H11: 
(subst0 (s (Flat Cast) i) u t2 x1)).(eq_ind_r T (THead (Flat Cast) x0 x1) 
(\lambda (t6: T).(ty3 g c3 t6 (THead (Flat Cast) t0 t3))) (ex_ind T (\lambda 
(t6: T).(ty3 g c3 t0 t6)) (ty3 g c3 (THead (Flat Cast) x0 x1) (THead (Flat 
Cast) t0 t3)) (\lambda (x: T).(\lambda (H12: (ty3 g c3 t0 x)).(ty3_conv g c3 
(THead (Flat Cast) t0 t3) (THead (Flat Cast) x t0) (ty3_cast g c3 t3 t0 (H3 i 
u c3 t3 (fsubst0_fst i u c t3 c3 H6) e H7) x H12) (THead (Flat Cast) x0 x1) 
(THead (Flat Cast) t0 x0) (ty3_cast g c3 x1 x0 (ty3_conv g c3 x0 t0 (H3 i u 
c3 x0 (fsubst0_both i u c t3 x0 H10 c3 H6) e H7) x1 t3 (H1 i u c3 x1 
(fsubst0_both i u c t2 x1 H11 c3 H6) e H7) (pc3_s c3 t3 x0 (pc3_fsubst0 c t3 
t3 (pc3_refl c t3) i u c3 x0 (fsubst0_both i u c t3 x0 H10 c3 H6) e H7))) t0 
(H3 i u c3 x0 (fsubst0_both i u c t3 x0 H10 c3 H6) e H7)) (pc3_fsubst0 c 
(THead (Flat Cast) t0 t3) (THead (Flat Cast) t0 t3) (pc3_refl c (THead (Flat 
Cast) t0 t3)) i u c3 (THead (Flat Cast) t0 x0) (fsubst0_both i u c (THead 
(Flat Cast) t0 t3) (THead (Flat Cast) t0 x0) (subst0_snd (Flat Cast) u x0 t3 
i H10 t0) c3 H6) e H7)))) (ty3_correct g c3 t3 t0 (H3 i u c3 t3 (fsubst0_fst 
i u c t3 c3 H6) e H7))) t5 H9)))))) H8)) (subst0_gen_head (Flat Cast) u t3 t2 
t5 i H5)))))))) c2 t4 H4)))))))))))))) c1 t1 t H))))).
(* COMMENTS
Initial nodes: 23439
END *)

theorem ty3_csubst0:
 \forall (g: G).(\forall (c1: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c1 
t1 t2) \to (\forall (e: C).(\forall (u: T).(\forall (i: nat).((getl i c1 
(CHead e (Bind Abbr) u)) \to (\forall (c2: C).((csubst0 i u c1 c2) \to (ty3 g 
c2 t1 t2)))))))))))
\def
 \lambda (g: G).(\lambda (c1: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (ty3 g c1 t1 t2)).(\lambda (e: C).(\lambda (u: T).(\lambda (i: 
nat).(\lambda (H0: (getl i c1 (CHead e (Bind Abbr) u))).(\lambda (c2: 
C).(\lambda (H1: (csubst0 i u c1 c2)).(ty3_fsubst0 g c1 t1 t2 H i u c2 t1 
(fsubst0_fst i u c1 t1 c2 H1) e H0))))))))))).
(* COMMENTS
Initial nodes: 89
END *)

theorem ty3_subst0:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t: T).((ty3 g c t1 
t) \to (\forall (e: C).(\forall (u: T).(\forall (i: nat).((getl i c (CHead e 
(Bind Abbr) u)) \to (\forall (t2: T).((subst0 i u t1 t2) \to (ty3 g c t2 
t)))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (t: T).(\lambda (H: 
(ty3 g c t1 t)).(\lambda (e: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H0: (getl i c (CHead e (Bind Abbr) u))).(\lambda (t2: T).(\lambda (H1: 
(subst0 i u t1 t2)).(ty3_fsubst0 g c t1 t H i u c t2 (fsubst0_snd i u c t1 t2 
H1) e H0))))))))))).
(* COMMENTS
Initial nodes: 89
END *)

