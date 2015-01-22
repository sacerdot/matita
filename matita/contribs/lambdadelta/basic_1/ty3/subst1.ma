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

include "Basic-1/pc3/subst1.ma".

include "Basic-1/getl/getl.ma".

theorem ty3_gen_cabbr:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c 
t1 t2) \to (\forall (e: C).(\forall (u: T).(\forall (d: nat).((getl d c 
(CHead e (Bind Abbr) u)) \to (\forall (a0: C).((csubst1 d u c a0) \to 
(\forall (a: C).((drop (S O) d a0 a) \to (ex3_2 T T (\lambda (y1: T).(\lambda 
(_: T).(subst1 d u t1 (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: 
T).(subst1 d u t2 (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 
g a y1 y2))))))))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (ty3 g c t1 t2)).(ty3_ind g (\lambda (c0: C).(\lambda (t: T).(\lambda 
(t0: T).(\forall (e: C).(\forall (u: T).(\forall (d: nat).((getl d c0 (CHead 
e (Bind Abbr) u)) \to (\forall (a0: C).((csubst1 d u c0 a0) \to (\forall (a: 
C).((drop (S O) d a0 a) \to (ex3_2 T T (\lambda (y1: T).(\lambda (_: 
T).(subst1 d u t (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: 
T).(subst1 d u t0 (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 
g a y1 y2))))))))))))))) (\lambda (c0: C).(\lambda (t3: T).(\lambda (t: 
T).(\lambda (_: (ty3 g c0 t3 t)).(\lambda (H1: ((\forall (e: C).(\forall (u: 
T).(\forall (d: nat).((getl d c0 (CHead e (Bind Abbr) u)) \to (\forall (a0: 
C).((csubst1 d u c0 a0) \to (\forall (a: C).((drop (S O) d a0 a) \to (ex3_2 T 
T (\lambda (y1: T).(\lambda (_: T).(subst1 d u t3 (lift (S O) d y1)))) 
(\lambda (_: T).(\lambda (y2: T).(subst1 d u t (lift (S O) d y2)))) (\lambda 
(y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))))))))))))).(\lambda (u: 
T).(\lambda (t4: T).(\lambda (_: (ty3 g c0 u t4)).(\lambda (H3: ((\forall (e: 
C).(\forall (u0: T).(\forall (d: nat).((getl d c0 (CHead e (Bind Abbr) u0)) 
\to (\forall (a0: C).((csubst1 d u0 c0 a0) \to (\forall (a: C).((drop (S O) d 
a0 a) \to (ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 d u0 u (lift (S 
O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d u0 t4 (lift (S O) d 
y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 
y2)))))))))))))).(\lambda (H4: (pc3 c0 t4 t3)).(\lambda (e: C).(\lambda (u0: 
T).(\lambda (d: nat).(\lambda (H5: (getl d c0 (CHead e (Bind Abbr) 
u0))).(\lambda (a0: C).(\lambda (H6: (csubst1 d u0 c0 a0)).(\lambda (a: 
C).(\lambda (H7: (drop (S O) d a0 a)).(let H8 \def (H3 e u0 d H5 a0 H6 a H7) 
in (ex3_2_ind T T (\lambda (y1: T).(\lambda (_: T).(subst1 d u0 u (lift (S O) 
d y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d u0 t4 (lift (S O) d 
y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) (ex3_2 T T 
(\lambda (y1: T).(\lambda (_: T).(subst1 d u0 u (lift (S O) d y1)))) (\lambda 
(_: T).(\lambda (y2: T).(subst1 d u0 t3 (lift (S O) d y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda (x0: T).(\lambda (x1: 
T).(\lambda (H9: (subst1 d u0 u (lift (S O) d x0))).(\lambda (H10: (subst1 d 
u0 t4 (lift (S O) d x1))).(\lambda (H11: (ty3 g a x0 x1)).(let H12 \def (H1 e 
u0 d H5 a0 H6 a H7) in (ex3_2_ind T T (\lambda (y1: T).(\lambda (_: 
T).(subst1 d u0 t3 (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: 
T).(subst1 d u0 t (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 
g a y1 y2))) (ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 d u0 u (lift 
(S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d u0 t3 (lift (S O) d 
y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda (x2: 
T).(\lambda (x3: T).(\lambda (H13: (subst1 d u0 t3 (lift (S O) d 
x2))).(\lambda (_: (subst1 d u0 t (lift (S O) d x3))).(\lambda (H15: (ty3 g a 
x2 x3)).(ex3_2_intro T T (\lambda (y1: T).(\lambda (_: T).(subst1 d u0 u 
(lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d u0 t3 (lift 
(S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) x0 x2 H9 
H13 (ty3_conv g a x2 x3 H15 x0 x1 H11 (pc3_gen_cabbr c0 t4 t3 H4 e u0 d H5 a0 
H6 a H7 x1 H10 x2 H13)))))))) H12))))))) H8)))))))))))))))))))) (\lambda (c0: 
C).(\lambda (m: nat).(\lambda (e: C).(\lambda (u: T).(\lambda (d: 
nat).(\lambda (_: (getl d c0 (CHead e (Bind Abbr) u))).(\lambda (a0: 
C).(\lambda (_: (csubst1 d u c0 a0)).(\lambda (a: C).(\lambda (_: (drop (S O) 
d a0 a)).(ex3_2_intro T T (\lambda (y1: T).(\lambda (_: T).(subst1 d u (TSort 
m) (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d u (TSort 
(next g m)) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a 
y1 y2))) (TSort m) (TSort (next g m)) (eq_ind_r T (TSort m) (\lambda (t: 
T).(subst1 d u (TSort m) t)) (subst1_refl d u (TSort m)) (lift (S O) d (TSort 
m)) (lift_sort m (S O) d)) (eq_ind_r T (TSort (next g m)) (\lambda (t: 
T).(subst1 d u (TSort (next g m)) t)) (subst1_refl d u (TSort (next g m))) 
(lift (S O) d (TSort (next g m))) (lift_sort (next g m) (S O) d)) (ty3_sort g 
a m)))))))))))) (\lambda (n: nat).(\lambda (c0: C).(\lambda (d: C).(\lambda 
(u: T).(\lambda (H0: (getl n c0 (CHead d (Bind Abbr) u))).(\lambda (t: 
T).(\lambda (H1: (ty3 g d u t)).(\lambda (H2: ((\forall (e: C).(\forall (u0: 
T).(\forall (d0: nat).((getl d0 d (CHead e (Bind Abbr) u0)) \to (\forall (a0: 
C).((csubst1 d0 u0 d a0) \to (\forall (a: C).((drop (S O) d0 a0 a) \to (ex3_2 
T T (\lambda (y1: T).(\lambda (_: T).(subst1 d0 u0 u (lift (S O) d0 y1)))) 
(\lambda (_: T).(\lambda (y2: T).(subst1 d0 u0 t (lift (S O) d0 y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))))))))))))).(\lambda (e: 
C).(\lambda (u0: T).(\lambda (d0: nat).(\lambda (H3: (getl d0 c0 (CHead e 
(Bind Abbr) u0))).(\lambda (a0: C).(\lambda (H4: (csubst1 d0 u0 c0 
a0)).(\lambda (a: C).(\lambda (H5: (drop (S O) d0 a0 a)).(lt_eq_gt_e n d0 
(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 d0 u0 (TLRef n) (lift (S 
O) d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d0 u0 (lift (S n) O t) 
(lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) 
(\lambda (H6: (lt n d0)).(let H7 \def (eq_ind nat (minus d0 n) (\lambda (n0: 
nat).(getl n0 (CHead d (Bind Abbr) u) (CHead e (Bind Abbr) u0))) 
(getl_conf_le d0 (CHead e (Bind Abbr) u0) c0 H3 (CHead d (Bind Abbr) u) n H0 
(le_S_n n d0 (le_S (S n) d0 H6))) (S (minus d0 (S n))) (minus_x_Sy d0 n H6)) 
in (ex2_ind C (\lambda (e2: C).(csubst1 (minus d0 n) u0 (CHead d (Bind Abbr) 
u) e2)) (\lambda (e2: C).(getl n a0 e2)) (ex3_2 T T (\lambda (y1: T).(\lambda 
(_: T).(subst1 d0 u0 (TLRef n) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda 
(y2: T).(subst1 d0 u0 (lift (S n) O t) (lift (S O) d0 y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda (x: C).(\lambda (H8: (csubst1 
(minus d0 n) u0 (CHead d (Bind Abbr) u) x)).(\lambda (H9: (getl n a0 x)).(let 
H10 \def (eq_ind nat (minus d0 n) (\lambda (n0: nat).(csubst1 n0 u0 (CHead d 
(Bind Abbr) u) x)) H8 (S (minus d0 (S n))) (minus_x_Sy d0 n H6)) in (let H11 
\def (csubst1_gen_head (Bind Abbr) d x u u0 (minus d0 (S n)) H10) in 
(ex3_2_ind T C (\lambda (u2: T).(\lambda (c2: C).(eq C x (CHead c2 (Bind 
Abbr) u2)))) (\lambda (u2: T).(\lambda (_: C).(subst1 (minus d0 (S n)) u0 u 
u2))) (\lambda (_: T).(\lambda (c2: C).(csubst1 (minus d0 (S n)) u0 d c2))) 
(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 d0 u0 (TLRef n) (lift (S 
O) d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d0 u0 (lift (S n) O t) 
(lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) 
(\lambda (x0: T).(\lambda (x1: C).(\lambda (H12: (eq C x (CHead x1 (Bind 
Abbr) x0))).(\lambda (H13: (subst1 (minus d0 (S n)) u0 u x0)).(\lambda (H14: 
(csubst1 (minus d0 (S n)) u0 d x1)).(let H15 \def (eq_ind C x (\lambda (c1: 
C).(getl n a0 c1)) H9 (CHead x1 (Bind Abbr) x0) H12) in (let H16 \def (eq_ind 
nat d0 (\lambda (n0: nat).(drop (S O) n0 a0 a)) H5 (S (plus n (minus d0 (S 
n)))) (lt_plus_minus n d0 H6)) in (ex3_2_ind T C (\lambda (v: T).(\lambda (_: 
C).(eq T x0 (lift (S O) (minus d0 (S n)) v)))) (\lambda (v: T).(\lambda (e0: 
C).(getl n a (CHead e0 (Bind Abbr) v)))) (\lambda (_: T).(\lambda (e0: 
C).(drop (S O) (minus d0 (S n)) x1 e0))) (ex3_2 T T (\lambda (y1: T).(\lambda 
(_: T).(subst1 d0 u0 (TLRef n) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda 
(y2: T).(subst1 d0 u0 (lift (S n) O t) (lift (S O) d0 y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda (x2: T).(\lambda (x3: 
C).(\lambda (H17: (eq T x0 (lift (S O) (minus d0 (S n)) x2))).(\lambda (H18: 
(getl n a (CHead x3 (Bind Abbr) x2))).(\lambda (H19: (drop (S O) (minus d0 (S 
n)) x1 x3)).(let H20 \def (eq_ind T x0 (\lambda (t0: T).(subst1 (minus d0 (S 
n)) u0 u t0)) H13 (lift (S O) (minus d0 (S n)) x2) H17) in (let H21 \def (H2 
e u0 (minus d0 (S n)) (getl_gen_S (Bind Abbr) d (CHead e (Bind Abbr) u0) u 
(minus d0 (S n)) H7) x1 H14 x3 H19) in (ex3_2_ind T T (\lambda (y1: 
T).(\lambda (_: T).(subst1 (minus d0 (S n)) u0 u (lift (S O) (minus d0 (S n)) 
y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 (minus d0 (S n)) u0 t (lift 
(S O) (minus d0 (S n)) y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g x3 y1 
y2))) (ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 d0 u0 (TLRef n) 
(lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d0 u0 (lift (S 
n) O t) (lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 
y2)))) (\lambda (x4: T).(\lambda (x5: T).(\lambda (H22: (subst1 (minus d0 (S 
n)) u0 u (lift (S O) (minus d0 (S n)) x4))).(\lambda (H23: (subst1 (minus d0 
(S n)) u0 t (lift (S O) (minus d0 (S n)) x5))).(\lambda (H24: (ty3 g x3 x4 
x5)).(let H25 \def (eq_ind T x4 (\lambda (t0: T).(ty3 g x3 t0 x5)) H24 x2 
(subst1_confluence_lift u x4 u0 (minus d0 (S n)) H22 x2 H20)) in (eq_ind_r 
nat (plus (minus d0 (S n)) (S n)) (\lambda (n0: nat).(ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(subst1 d0 u0 (TLRef n) (lift (S O) d0 y1)))) (\lambda (_: 
T).(\lambda (y2: T).(subst1 n0 u0 (lift (S n) O t) (lift (S O) d0 y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (eq_ind_r nat (plus (S 
n) (minus d0 (S n))) (\lambda (n0: nat).(ex3_2 T T (\lambda (y1: T).(\lambda 
(_: T).(subst1 d0 u0 (TLRef n) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda 
(y2: T).(subst1 (plus (minus d0 (S n)) (S n)) u0 (lift (S n) O t) (lift (S O) 
n0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (ex3_2_intro 
T T (\lambda (y1: T).(\lambda (_: T).(subst1 d0 u0 (TLRef n) (lift (S O) d0 
y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 (plus (minus d0 (S n)) (S n)) 
u0 (lift (S n) O t) (lift (S O) (plus (S n) (minus d0 (S n))) y2)))) (\lambda 
(y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) (TLRef n) (lift (S n) O x5) 
(eq_ind_r T (TLRef n) (\lambda (t0: T).(subst1 d0 u0 (TLRef n) t0)) 
(subst1_refl d0 u0 (TLRef n)) (lift (S O) d0 (TLRef n)) (lift_lref_lt n (S O) 
d0 H6)) (eq_ind_r T (lift (S n) O (lift (S O) (minus d0 (S n)) x5)) (\lambda 
(t0: T).(subst1 (plus (minus d0 (S n)) (S n)) u0 (lift (S n) O t) t0)) 
(subst1_lift_ge t (lift (S O) (minus d0 (S n)) x5) u0 (minus d0 (S n)) (S n) 
H23 O (le_O_n (minus d0 (S n)))) (lift (S O) (plus (S n) (minus d0 (S n))) 
(lift (S n) O x5)) (lift_d x5 (S O) (S n) (minus d0 (S n)) O (le_O_n (minus 
d0 (S n))))) (ty3_abbr g n a x3 x2 H18 x5 H25)) d0 (le_plus_minus (S n) d0 
H6)) d0 (le_plus_minus_sym (S n) d0 H6)))))))) H21)))))))) (getl_drop_conf_lt 
Abbr a0 x1 x0 n H15 a (S O) (minus d0 (S n)) H16))))))))) H11)))))) 
(csubst1_getl_lt d0 n H6 c0 a0 u0 H4 (CHead d (Bind Abbr) u) H0)))) (\lambda 
(H6: (eq nat n d0)).(let H7 \def (eq_ind_r nat d0 (\lambda (n0: nat).(drop (S 
O) n0 a0 a)) H5 n H6) in (let H8 \def (eq_ind_r nat d0 (\lambda (n0: 
nat).(csubst1 n0 u0 c0 a0)) H4 n H6) in (let H9 \def (eq_ind_r nat d0 
(\lambda (n0: nat).(getl n0 c0 (CHead e (Bind Abbr) u0))) H3 n H6) in (eq_ind 
nat n (\lambda (n0: nat).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 
n0 u0 (TLRef n) (lift (S O) n0 y1)))) (\lambda (_: T).(\lambda (y2: 
T).(subst1 n0 u0 (lift (S n) O t) (lift (S O) n0 y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2))))) (let H10 \def (eq_ind C (CHead d 
(Bind Abbr) u) (\lambda (c1: C).(getl n c0 c1)) H0 (CHead e (Bind Abbr) u0) 
(getl_mono c0 (CHead d (Bind Abbr) u) n H0 (CHead e (Bind Abbr) u0) H9)) in 
(let H11 \def (f_equal C C (\lambda (e0: C).(match e0 in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow d | (CHead c1 _ _) \Rightarrow c1])) 
(CHead d (Bind Abbr) u) (CHead e (Bind Abbr) u0) (getl_mono c0 (CHead d (Bind 
Abbr) u) n H0 (CHead e (Bind Abbr) u0) H9)) in ((let H12 \def (f_equal C T 
(\lambda (e0: C).(match e0 in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) (CHead d (Bind Abbr) u) 
(CHead e (Bind Abbr) u0) (getl_mono c0 (CHead d (Bind Abbr) u) n H0 (CHead e 
(Bind Abbr) u0) H9)) in (\lambda (H13: (eq C d e)).(let H14 \def (eq_ind_r T 
u0 (\lambda (t0: T).(getl n c0 (CHead e (Bind Abbr) t0))) H10 u H12) in (let 
H15 \def (eq_ind_r T u0 (\lambda (t0: T).(csubst1 n t0 c0 a0)) H8 u H12) in 
(eq_ind T u (\lambda (t0: T).(ex3_2 T T (\lambda (y1: T).(\lambda (_: 
T).(subst1 n t0 (TLRef n) (lift (S O) n y1)))) (\lambda (_: T).(\lambda (y2: 
T).(subst1 n t0 (lift (S n) O t) (lift (S O) n y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2))))) (let H16 \def (eq_ind_r C e (\lambda 
(c1: C).(getl n c0 (CHead c1 (Bind Abbr) u))) H14 d H13) in (ex3_2_intro T T 
(\lambda (y1: T).(\lambda (_: T).(subst1 n u (TLRef n) (lift (S O) n y1)))) 
(\lambda (_: T).(\lambda (y2: T).(subst1 n u (lift (S n) O t) (lift (S O) n 
y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) (lift n O u) (lift 
n O t) (subst1_single n u (TLRef n) (lift (S O) n (lift n O u)) (eq_ind_r T 
(lift (plus (S O) n) O u) (\lambda (t0: T).(subst0 n u (TLRef n) t0)) 
(subst0_lref u n) (lift (S O) n (lift n O u)) (lift_free u n (S O) O n (le_n 
(plus O n)) (le_O_n n)))) (eq_ind_r T (lift (plus (S O) n) O t) (\lambda (t0: 
T).(subst1 n u (lift (S n) O t) t0)) (subst1_refl n u (lift (S n) O t)) (lift 
(S O) n (lift n O t)) (lift_free t n (S O) O n (le_n (plus O n)) (le_O_n n))) 
(ty3_lift g d u t H1 a O n (getl_conf_ge_drop Abbr a0 d u n (csubst1_getl_ge 
n n (le_n n) c0 a0 u H15 (CHead d (Bind Abbr) u) H16) a H7)))) u0 H12))))) 
H11))) d0 H6))))) (\lambda (H6: (lt d0 n)).(eq_ind_r nat (S (plus O (minus n 
(S O)))) (\lambda (n0: nat).(ex3_2 T T (\lambda (y1: T).(\lambda (_: 
T).(subst1 d0 u0 (TLRef n0) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda 
(y2: T).(subst1 d0 u0 (lift (S n) O t) (lift (S O) d0 y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2))))) (eq_ind nat (plus (S O) (minus n (S 
O))) (\lambda (n0: nat).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 
d0 u0 (TLRef n0) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: 
T).(subst1 d0 u0 (lift (S n) O t) (lift (S O) d0 y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2))))) (eq_ind_r nat (plus (minus n (S O)) 
(S O)) (\lambda (n0: nat).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 
d0 u0 (TLRef n0) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: 
T).(subst1 d0 u0 (lift (S n) O t) (lift (S O) d0 y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2))))) (ex3_2_intro T T (\lambda (y1: 
T).(\lambda (_: T).(subst1 d0 u0 (TLRef (plus (minus n (S O)) (S O))) (lift 
(S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d0 u0 (lift (S n) O 
t) (lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) 
(TLRef (minus n (S O))) (lift n O t) (eq_ind_r T (TLRef (plus (minus n (S O)) 
(S O))) (\lambda (t0: T).(subst1 d0 u0 (TLRef (plus (minus n (S O)) (S O))) 
t0)) (subst1_refl d0 u0 (TLRef (plus (minus n (S O)) (S O)))) (lift (S O) d0 
(TLRef (minus n (S O)))) (lift_lref_ge (minus n (S O)) (S O) d0 (lt_le_minus 
d0 n H6))) (eq_ind_r T (lift (plus (S O) n) O t) (\lambda (t0: T).(subst1 d0 
u0 (lift (S n) O t) t0)) (subst1_refl d0 u0 (lift (S n) O t)) (lift (S O) d0 
(lift n O t)) (lift_free t n (S O) O d0 (le_S_n d0 (plus O n) (le_S (S d0) 
(plus O n) H6)) (le_O_n d0))) (eq_ind_r nat (S (minus n (S O))) (\lambda (n0: 
nat).(ty3 g a (TLRef (minus n (S O))) (lift n0 O t))) (ty3_abbr g (minus n (S 
O)) a d u (getl_drop_conf_ge n (CHead d (Bind Abbr) u) a0 (csubst1_getl_ge d0 
n (le_S_n d0 n (le_S (S d0) n H6)) c0 a0 u0 H4 (CHead d (Bind Abbr) u) H0) a 
(S O) d0 H5 (eq_ind_r nat (plus (S O) d0) (\lambda (n0: nat).(le n0 n)) H6 
(plus d0 (S O)) (plus_sym d0 (S O)))) t H1) n (minus_x_SO n (le_lt_trans O d0 
n (le_O_n d0) H6)))) (plus (S O) (minus n (S O))) (plus_sym (S O) (minus n (S 
O)))) (S (plus O (minus n (S O)))) (refl_equal nat (S (plus O (minus n (S 
O)))))) n (lt_plus_minus O n (le_lt_trans O d0 n (le_O_n d0) 
H6))))))))))))))))))))) (\lambda (n: nat).(\lambda (c0: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (H0: (getl n c0 (CHead d (Bind Abst) 
u))).(\lambda (t: T).(\lambda (H1: (ty3 g d u t)).(\lambda (H2: ((\forall (e: 
C).(\forall (u0: T).(\forall (d0: nat).((getl d0 d (CHead e (Bind Abbr) u0)) 
\to (\forall (a0: C).((csubst1 d0 u0 d a0) \to (\forall (a: C).((drop (S O) 
d0 a0 a) \to (ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 d0 u0 u 
(lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d0 u0 t (lift 
(S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 
y2)))))))))))))).(\lambda (e: C).(\lambda (u0: T).(\lambda (d0: nat).(\lambda 
(H3: (getl d0 c0 (CHead e (Bind Abbr) u0))).(\lambda (a0: C).(\lambda (H4: 
(csubst1 d0 u0 c0 a0)).(\lambda (a: C).(\lambda (H5: (drop (S O) d0 a0 
a)).(lt_eq_gt_e n d0 (ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 d0 
u0 (TLRef n) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 
d0 u0 (lift (S n) O u) (lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: 
T).(ty3 g a y1 y2)))) (\lambda (H6: (lt n d0)).(let H7 \def (eq_ind nat 
(minus d0 n) (\lambda (n0: nat).(getl n0 (CHead d (Bind Abst) u) (CHead e 
(Bind Abbr) u0))) (getl_conf_le d0 (CHead e (Bind Abbr) u0) c0 H3 (CHead d 
(Bind Abst) u) n H0 (le_S_n n d0 (le_S (S n) d0 H6))) (S (minus d0 (S n))) 
(minus_x_Sy d0 n H6)) in (ex2_ind C (\lambda (e2: C).(csubst1 (minus d0 n) u0 
(CHead d (Bind Abst) u) e2)) (\lambda (e2: C).(getl n a0 e2)) (ex3_2 T T 
(\lambda (y1: T).(\lambda (_: T).(subst1 d0 u0 (TLRef n) (lift (S O) d0 
y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d0 u0 (lift (S n) O u) (lift 
(S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda 
(x: C).(\lambda (H8: (csubst1 (minus d0 n) u0 (CHead d (Bind Abst) u) 
x)).(\lambda (H9: (getl n a0 x)).(let H10 \def (eq_ind nat (minus d0 n) 
(\lambda (n0: nat).(csubst1 n0 u0 (CHead d (Bind Abst) u) x)) H8 (S (minus d0 
(S n))) (minus_x_Sy d0 n H6)) in (let H11 \def (csubst1_gen_head (Bind Abst) 
d x u u0 (minus d0 (S n)) H10) in (ex3_2_ind T C (\lambda (u2: T).(\lambda 
(c2: C).(eq C x (CHead c2 (Bind Abst) u2)))) (\lambda (u2: T).(\lambda (_: 
C).(subst1 (minus d0 (S n)) u0 u u2))) (\lambda (_: T).(\lambda (c2: 
C).(csubst1 (minus d0 (S n)) u0 d c2))) (ex3_2 T T (\lambda (y1: T).(\lambda 
(_: T).(subst1 d0 u0 (TLRef n) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda 
(y2: T).(subst1 d0 u0 (lift (S n) O u) (lift (S O) d0 y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda (x0: T).(\lambda (x1: 
C).(\lambda (H12: (eq C x (CHead x1 (Bind Abst) x0))).(\lambda (H13: (subst1 
(minus d0 (S n)) u0 u x0)).(\lambda (H14: (csubst1 (minus d0 (S n)) u0 d 
x1)).(let H15 \def (eq_ind C x (\lambda (c1: C).(getl n a0 c1)) H9 (CHead x1 
(Bind Abst) x0) H12) in (let H16 \def (eq_ind nat d0 (\lambda (n0: nat).(drop 
(S O) n0 a0 a)) H5 (S (plus n (minus d0 (S n)))) (lt_plus_minus n d0 H6)) in 
(ex3_2_ind T C (\lambda (v: T).(\lambda (_: C).(eq T x0 (lift (S O) (minus d0 
(S n)) v)))) (\lambda (v: T).(\lambda (e0: C).(getl n a (CHead e0 (Bind Abst) 
v)))) (\lambda (_: T).(\lambda (e0: C).(drop (S O) (minus d0 (S n)) x1 e0))) 
(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 d0 u0 (TLRef n) (lift (S 
O) d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d0 u0 (lift (S n) O u) 
(lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) 
(\lambda (x2: T).(\lambda (x3: C).(\lambda (H17: (eq T x0 (lift (S O) (minus 
d0 (S n)) x2))).(\lambda (H18: (getl n a (CHead x3 (Bind Abst) x2))).(\lambda 
(H19: (drop (S O) (minus d0 (S n)) x1 x3)).(let H20 \def (eq_ind T x0 
(\lambda (t0: T).(subst1 (minus d0 (S n)) u0 u t0)) H13 (lift (S O) (minus d0 
(S n)) x2) H17) in (let H21 \def (H2 e u0 (minus d0 (S n)) (getl_gen_S (Bind 
Abst) d (CHead e (Bind Abbr) u0) u (minus d0 (S n)) H7) x1 H14 x3 H19) in 
(ex3_2_ind T T (\lambda (y1: T).(\lambda (_: T).(subst1 (minus d0 (S n)) u0 u 
(lift (S O) (minus d0 (S n)) y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 
(minus d0 (S n)) u0 t (lift (S O) (minus d0 (S n)) y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g x3 y1 y2))) (ex3_2 T T (\lambda (y1: T).(\lambda 
(_: T).(subst1 d0 u0 (TLRef n) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda 
(y2: T).(subst1 d0 u0 (lift (S n) O u) (lift (S O) d0 y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda (x4: T).(\lambda (x5: 
T).(\lambda (H22: (subst1 (minus d0 (S n)) u0 u (lift (S O) (minus d0 (S n)) 
x4))).(\lambda (_: (subst1 (minus d0 (S n)) u0 t (lift (S O) (minus d0 (S n)) 
x5))).(\lambda (H24: (ty3 g x3 x4 x5)).(let H25 \def (eq_ind T x4 (\lambda 
(t0: T).(ty3 g x3 t0 x5)) H24 x2 (subst1_confluence_lift u x4 u0 (minus d0 (S 
n)) H22 x2 H20)) in (eq_ind_r nat (plus (minus d0 (S n)) (S n)) (\lambda (n0: 
nat).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 d0 u0 (TLRef n) 
(lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 n0 u0 (lift (S 
n) O u) (lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 
y2))))) (eq_ind_r nat (plus (S n) (minus d0 (S n))) (\lambda (n0: nat).(ex3_2 
T T (\lambda (y1: T).(\lambda (_: T).(subst1 d0 u0 (TLRef n) (lift (S O) d0 
y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 (plus (minus d0 (S n)) (S n)) 
u0 (lift (S n) O u) (lift (S O) n0 y2)))) (\lambda (y1: T).(\lambda (y2: 
T).(ty3 g a y1 y2))))) (ex3_2_intro T T (\lambda (y1: T).(\lambda (_: 
T).(subst1 d0 u0 (TLRef n) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda 
(y2: T).(subst1 (plus (minus d0 (S n)) (S n)) u0 (lift (S n) O u) (lift (S O) 
(plus (S n) (minus d0 (S n))) y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g 
a y1 y2))) (TLRef n) (lift (S n) O x2) (eq_ind_r T (TLRef n) (\lambda (t0: 
T).(subst1 d0 u0 (TLRef n) t0)) (subst1_refl d0 u0 (TLRef n)) (lift (S O) d0 
(TLRef n)) (lift_lref_lt n (S O) d0 H6)) (eq_ind_r T (lift (S n) O (lift (S 
O) (minus d0 (S n)) x2)) (\lambda (t0: T).(subst1 (plus (minus d0 (S n)) (S 
n)) u0 (lift (S n) O u) t0)) (subst1_lift_ge u (lift (S O) (minus d0 (S n)) 
x2) u0 (minus d0 (S n)) (S n) H20 O (le_O_n (minus d0 (S n)))) (lift (S O) 
(plus (S n) (minus d0 (S n))) (lift (S n) O x2)) (lift_d x2 (S O) (S n) 
(minus d0 (S n)) O (le_O_n (minus d0 (S n))))) (ty3_abst g n a x3 x2 H18 x5 
H25)) d0 (le_plus_minus (S n) d0 H6)) d0 (le_plus_minus_sym (S n) d0 
H6)))))))) H21)))))))) (getl_drop_conf_lt Abst a0 x1 x0 n H15 a (S O) (minus 
d0 (S n)) H16))))))))) H11)))))) (csubst1_getl_lt d0 n H6 c0 a0 u0 H4 (CHead 
d (Bind Abst) u) H0)))) (\lambda (H6: (eq nat n d0)).(let H7 \def (eq_ind_r 
nat d0 (\lambda (n0: nat).(drop (S O) n0 a0 a)) H5 n H6) in (let H8 \def 
(eq_ind_r nat d0 (\lambda (n0: nat).(csubst1 n0 u0 c0 a0)) H4 n H6) in (let 
H9 \def (eq_ind_r nat d0 (\lambda (n0: nat).(getl n0 c0 (CHead e (Bind Abbr) 
u0))) H3 n H6) in (eq_ind nat n (\lambda (n0: nat).(ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(subst1 n0 u0 (TLRef n) (lift (S O) n0 y1)))) (\lambda (_: 
T).(\lambda (y2: T).(subst1 n0 u0 (lift (S n) O u) (lift (S O) n0 y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (let H10 \def (eq_ind C 
(CHead d (Bind Abst) u) (\lambda (c1: C).(getl n c0 c1)) H0 (CHead e (Bind 
Abbr) u0) (getl_mono c0 (CHead d (Bind Abst) u) n H0 (CHead e (Bind Abbr) u0) 
H9)) in (let H11 \def (eq_ind C (CHead d (Bind Abst) u) (\lambda (ee: 
C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow 
False | (CHead _ k _) \Rightarrow (match k in K return (\lambda (_: K).Prop) 
with [(Bind b) \Rightarrow (match b in B return (\lambda (_: B).Prop) with 
[Abbr \Rightarrow False | Abst \Rightarrow True | Void \Rightarrow False]) | 
(Flat _) \Rightarrow False])])) I (CHead e (Bind Abbr) u0) (getl_mono c0 
(CHead d (Bind Abst) u) n H0 (CHead e (Bind Abbr) u0) H9)) in (False_ind 
(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 n u0 (TLRef n) (lift (S 
O) n y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 n u0 (lift (S n) O u) 
(lift (S O) n y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) 
H11))) d0 H6))))) (\lambda (H6: (lt d0 n)).(eq_ind_r nat (S (plus O (minus n 
(S O)))) (\lambda (n0: nat).(ex3_2 T T (\lambda (y1: T).(\lambda (_: 
T).(subst1 d0 u0 (TLRef n0) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda 
(y2: T).(subst1 d0 u0 (lift (S n) O u) (lift (S O) d0 y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2))))) (eq_ind nat (plus (S O) (minus n (S 
O))) (\lambda (n0: nat).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 
d0 u0 (TLRef n0) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: 
T).(subst1 d0 u0 (lift (S n) O u) (lift (S O) d0 y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2))))) (eq_ind_r nat (plus (minus n (S O)) 
(S O)) (\lambda (n0: nat).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 
d0 u0 (TLRef n0) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: 
T).(subst1 d0 u0 (lift (S n) O u) (lift (S O) d0 y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2))))) (ex3_2_intro T T (\lambda (y1: 
T).(\lambda (_: T).(subst1 d0 u0 (TLRef (plus (minus n (S O)) (S O))) (lift 
(S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d0 u0 (lift (S n) O 
u) (lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) 
(TLRef (minus n (S O))) (lift n O u) (eq_ind_r T (TLRef (plus (minus n (S O)) 
(S O))) (\lambda (t0: T).(subst1 d0 u0 (TLRef (plus (minus n (S O)) (S O))) 
t0)) (subst1_refl d0 u0 (TLRef (plus (minus n (S O)) (S O)))) (lift (S O) d0 
(TLRef (minus n (S O)))) (lift_lref_ge (minus n (S O)) (S O) d0 (lt_le_minus 
d0 n H6))) (eq_ind_r T (lift (plus (S O) n) O u) (\lambda (t0: T).(subst1 d0 
u0 (lift (S n) O u) t0)) (subst1_refl d0 u0 (lift (S n) O u)) (lift (S O) d0 
(lift n O u)) (lift_free u n (S O) O d0 (le_S_n d0 (plus O n) (le_S (S d0) 
(plus O n) H6)) (le_O_n d0))) (eq_ind_r nat (S (minus n (S O))) (\lambda (n0: 
nat).(ty3 g a (TLRef (minus n (S O))) (lift n0 O u))) (ty3_abst g (minus n (S 
O)) a d u (getl_drop_conf_ge n (CHead d (Bind Abst) u) a0 (csubst1_getl_ge d0 
n (le_S_n d0 n (le_S (S d0) n H6)) c0 a0 u0 H4 (CHead d (Bind Abst) u) H0) a 
(S O) d0 H5 (eq_ind_r nat (plus (S O) d0) (\lambda (n0: nat).(le n0 n)) H6 
(plus d0 (S O)) (plus_sym d0 (S O)))) t H1) n (minus_x_SO n (le_lt_trans O d0 
n (le_O_n d0) H6)))) (plus (S O) (minus n (S O))) (plus_sym (S O) (minus n (S 
O)))) (S (plus O (minus n (S O)))) (refl_equal nat (S (plus O (minus n (S 
O)))))) n (lt_plus_minus O n (le_lt_trans O d0 n (le_O_n d0) 
H6))))))))))))))))))))) (\lambda (c0: C).(\lambda (u: T).(\lambda (t: 
T).(\lambda (_: (ty3 g c0 u t)).(\lambda (H1: ((\forall (e: C).(\forall (u0: 
T).(\forall (d: nat).((getl d c0 (CHead e (Bind Abbr) u0)) \to (\forall (a0: 
C).((csubst1 d u0 c0 a0) \to (\forall (a: C).((drop (S O) d a0 a) \to (ex3_2 
T T (\lambda (y1: T).(\lambda (_: T).(subst1 d u0 u (lift (S O) d y1)))) 
(\lambda (_: T).(\lambda (y2: T).(subst1 d u0 t (lift (S O) d y2)))) (\lambda 
(y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))))))))))))).(\lambda (b: 
B).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (ty3 g (CHead c0 (Bind b) 
u) t3 t4)).(\lambda (H3: ((\forall (e: C).(\forall (u0: T).(\forall (d: 
nat).((getl d (CHead c0 (Bind b) u) (CHead e (Bind Abbr) u0)) \to (\forall 
(a0: C).((csubst1 d u0 (CHead c0 (Bind b) u) a0) \to (\forall (a: C).((drop 
(S O) d a0 a) \to (ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 d u0 t3 
(lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d u0 t4 (lift 
(S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 
y2)))))))))))))).(\lambda (e: C).(\lambda (u0: T).(\lambda (d: nat).(\lambda 
(H4: (getl d c0 (CHead e (Bind Abbr) u0))).(\lambda (a0: C).(\lambda (H5: 
(csubst1 d u0 c0 a0)).(\lambda (a: C).(\lambda (H6: (drop (S O) d a0 a)).(let 
H7 \def (H1 e u0 d H4 a0 H5 a H6) in (ex3_2_ind T T (\lambda (y1: T).(\lambda 
(_: T).(subst1 d u0 u (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: 
T).(subst1 d u0 t (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 
g a y1 y2))) (ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 d u0 (THead 
(Bind b) u t3) (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 
d u0 (THead (Bind b) u t4) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda 
(y2: T).(ty3 g a y1 y2)))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H8: 
(subst1 d u0 u (lift (S O) d x0))).(\lambda (_: (subst1 d u0 t (lift (S O) d 
x1))).(\lambda (H10: (ty3 g a x0 x1)).(let H11 \def (H3 e u0 (S d) (getl_head 
(Bind b) d c0 (CHead e (Bind Abbr) u0) H4 u) (CHead a0 (Bind b) (lift (S O) d 
x0)) (csubst1_bind b d u0 u (lift (S O) d x0) H8 c0 a0 H5) (CHead a (Bind b) 
x0) (drop_skip_bind (S O) d a0 a H6 b x0)) in (ex3_2_ind T T (\lambda (y1: 
T).(\lambda (_: T).(subst1 (S d) u0 t3 (lift (S O) (S d) y1)))) (\lambda (_: 
T).(\lambda (y2: T).(subst1 (S d) u0 t4 (lift (S O) (S d) y2)))) (\lambda 
(y1: T).(\lambda (y2: T).(ty3 g (CHead a (Bind b) x0) y1 y2))) (ex3_2 T T 
(\lambda (y1: T).(\lambda (_: T).(subst1 d u0 (THead (Bind b) u t3) (lift (S 
O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d u0 (THead (Bind b) u 
t4) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) 
(\lambda (x2: T).(\lambda (x3: T).(\lambda (H12: (subst1 (S d) u0 t3 (lift (S 
O) (S d) x2))).(\lambda (H13: (subst1 (S d) u0 t4 (lift (S O) (S d) 
x3))).(\lambda (H14: (ty3 g (CHead a (Bind b) x0) x2 x3)).(ex3_2_intro T T 
(\lambda (y1: T).(\lambda (_: T).(subst1 d u0 (THead (Bind b) u t3) (lift (S 
O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d u0 (THead (Bind b) u 
t4) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) 
(THead (Bind b) x0 x2) (THead (Bind b) x0 x3) (eq_ind_r T (THead (Bind b) 
(lift (S O) d x0) (lift (S O) (S d) x2)) (\lambda (t0: T).(subst1 d u0 (THead 
(Bind b) u t3) t0)) (subst1_head u0 u (lift (S O) d x0) d H8 (Bind b) t3 
(lift (S O) (S d) x2) H12) (lift (S O) d (THead (Bind b) x0 x2)) (lift_bind b 
x0 x2 (S O) d)) (eq_ind_r T (THead (Bind b) (lift (S O) d x0) (lift (S O) (S 
d) x3)) (\lambda (t0: T).(subst1 d u0 (THead (Bind b) u t4) t0)) (subst1_head 
u0 u (lift (S O) d x0) d H8 (Bind b) t4 (lift (S O) (S d) x3) H13) (lift (S 
O) d (THead (Bind b) x0 x3)) (lift_bind b x0 x3 (S O) d)) (ty3_bind g a x0 x1 
H10 b x2 x3 H14))))))) H11))))))) H7)))))))))))))))))))) (\lambda (c0: 
C).(\lambda (w: T).(\lambda (u: T).(\lambda (_: (ty3 g c0 w u)).(\lambda (H1: 
((\forall (e: C).(\forall (u0: T).(\forall (d: nat).((getl d c0 (CHead e 
(Bind Abbr) u0)) \to (\forall (a0: C).((csubst1 d u0 c0 a0) \to (\forall (a: 
C).((drop (S O) d a0 a) \to (ex3_2 T T (\lambda (y1: T).(\lambda (_: 
T).(subst1 d u0 w (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: 
T).(subst1 d u0 u (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 
g a y1 y2)))))))))))))).(\lambda (v: T).(\lambda (t: T).(\lambda (_: (ty3 g 
c0 v (THead (Bind Abst) u t))).(\lambda (H3: ((\forall (e: C).(\forall (u0: 
T).(\forall (d: nat).((getl d c0 (CHead e (Bind Abbr) u0)) \to (\forall (a0: 
C).((csubst1 d u0 c0 a0) \to (\forall (a: C).((drop (S O) d a0 a) \to (ex3_2 
T T (\lambda (y1: T).(\lambda (_: T).(subst1 d u0 v (lift (S O) d y1)))) 
(\lambda (_: T).(\lambda (y2: T).(subst1 d u0 (THead (Bind Abst) u t) (lift 
(S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 
y2)))))))))))))).(\lambda (e: C).(\lambda (u0: T).(\lambda (d: nat).(\lambda 
(H4: (getl d c0 (CHead e (Bind Abbr) u0))).(\lambda (a0: C).(\lambda (H5: 
(csubst1 d u0 c0 a0)).(\lambda (a: C).(\lambda (H6: (drop (S O) d a0 a)).(let 
H7 \def (H3 e u0 d H4 a0 H5 a H6) in (ex3_2_ind T T (\lambda (y1: T).(\lambda 
(_: T).(subst1 d u0 v (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: 
T).(subst1 d u0 (THead (Bind Abst) u t) (lift (S O) d y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2))) (ex3_2 T T (\lambda (y1: T).(\lambda 
(_: T).(subst1 d u0 (THead (Flat Appl) w v) (lift (S O) d y1)))) (\lambda (_: 
T).(\lambda (y2: T).(subst1 d u0 (THead (Flat Appl) w (THead (Bind Abst) u 
t)) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (H8: (subst1 d u0 v (lift (S O) d 
x0))).(\lambda (H9: (subst1 d u0 (THead (Bind Abst) u t) (lift (S O) d 
x1))).(\lambda (H10: (ty3 g a x0 x1)).(let H11 \def (H1 e u0 d H4 a0 H5 a H6) 
in (ex3_2_ind T T (\lambda (y1: T).(\lambda (_: T).(subst1 d u0 w (lift (S O) 
d y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d u0 u (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) (ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(subst1 d u0 (THead (Flat Appl) w v) (lift (S O) d y1)))) 
(\lambda (_: T).(\lambda (y2: T).(subst1 d u0 (THead (Flat Appl) w (THead 
(Bind Abst) u t)) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 
g a y1 y2)))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H12: (subst1 d u0 w 
(lift (S O) d x2))).(\lambda (H13: (subst1 d u0 u (lift (S O) d 
x3))).(\lambda (H14: (ty3 g a x2 x3)).(let H_x \def (subst1_gen_head (Bind 
Abst) u0 u t (lift (S O) d x1) d H9) in (let H15 \def H_x in (ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t3: T).(eq T (lift (S O) d x1) (THead (Bind Abst) 
u2 t3)))) (\lambda (u2: T).(\lambda (_: T).(subst1 d u0 u u2))) (\lambda (_: 
T).(\lambda (t3: T).(subst1 (S d) u0 t t3))) (ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(subst1 d u0 (THead (Flat Appl) w v) (lift (S O) d y1)))) 
(\lambda (_: T).(\lambda (y2: T).(subst1 d u0 (THead (Flat Appl) w (THead 
(Bind Abst) u t)) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 
g a y1 y2)))) (\lambda (x4: T).(\lambda (x5: T).(\lambda (H16: (eq T (lift (S 
O) d x1) (THead (Bind Abst) x4 x5))).(\lambda (H17: (subst1 d u0 u 
x4)).(\lambda (H18: (subst1 (S d) u0 t x5)).(let H19 \def (sym_eq T (lift (S 
O) d x1) (THead (Bind Abst) x4 x5) H16) in (ex3_2_ind T T (\lambda (y: 
T).(\lambda (z: T).(eq T x1 (THead (Bind Abst) y z)))) (\lambda (y: 
T).(\lambda (_: T).(eq T x4 (lift (S O) d y)))) (\lambda (_: T).(\lambda (z: 
T).(eq T x5 (lift (S O) (S d) z)))) (ex3_2 T T (\lambda (y1: T).(\lambda (_: 
T).(subst1 d u0 (THead (Flat Appl) w v) (lift (S O) d y1)))) (\lambda (_: 
T).(\lambda (y2: T).(subst1 d u0 (THead (Flat Appl) w (THead (Bind Abst) u 
t)) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) 
(\lambda (x6: T).(\lambda (x7: T).(\lambda (H20: (eq T x1 (THead (Bind Abst) 
x6 x7))).(\lambda (H21: (eq T x4 (lift (S O) d x6))).(\lambda (H22: (eq T x5 
(lift (S O) (S d) x7))).(let H23 \def (eq_ind T x5 (\lambda (t0: T).(subst1 
(S d) u0 t t0)) H18 (lift (S O) (S d) x7) H22) in (let H24 \def (eq_ind T x4 
(\lambda (t0: T).(subst1 d u0 u t0)) H17 (lift (S O) d x6) H21) in (let H25 
\def (eq_ind T x1 (\lambda (t0: T).(ty3 g a x0 t0)) H10 (THead (Bind Abst) x6 
x7) H20) in (let H26 \def (eq_ind T x6 (\lambda (t0: T).(ty3 g a x0 (THead 
(Bind Abst) t0 x7))) H25 x3 (subst1_confluence_lift u x6 u0 d H24 x3 H13)) in 
(ex3_2_intro T T (\lambda (y1: T).(\lambda (_: T).(subst1 d u0 (THead (Flat 
Appl) w v) (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(subst1 d u0 
(THead (Flat Appl) w (THead (Bind Abst) u t)) (lift (S O) d y2)))) (\lambda 
(y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) (THead (Flat Appl) x2 x0) (THead 
(Flat Appl) x2 (THead (Bind Abst) x3 x7)) (eq_ind_r T (THead (Flat Appl) 
(lift (S O) d x2) (lift (S O) d x0)) (\lambda (t0: T).(subst1 d u0 (THead 
(Flat Appl) w v) t0)) (subst1_head u0 w (lift (S O) d x2) d H12 (Flat Appl) v 
(lift (S O) d x0) H8) (lift (S O) d (THead (Flat Appl) x2 x0)) (lift_flat 
Appl x2 x0 (S O) d)) (eq_ind_r T (THead (Flat Appl) (lift (S O) d x2) (lift 
(S O) d (THead (Bind Abst) x3 x7))) (\lambda (t0: T).(subst1 d u0 (THead 
(Flat Appl) w (THead (Bind Abst) u t)) t0)) (subst1_head u0 w (lift (S O) d 
x2) d H12 (Flat Appl) (THead (Bind Abst) u t) (lift (S O) d (THead (Bind 
Abst) x3 x7)) (eq_ind_r T (THead (Bind Abst) (lift (S O) d x3) (lift (S O) (S 
d) x7)) (\lambda (t0: T).(subst1 (s (Flat Appl) d) u0 (THead (Bind Abst) u t) 
t0)) (subst1_head u0 u (lift (S O) d x3) (s (Flat Appl) d) H13 (Bind Abst) t 
(lift (S O) (S d) x7) H23) (lift (S O) d (THead (Bind Abst) x3 x7)) 
(lift_bind Abst x3 x7 (S O) d))) (lift (S O) d (THead (Flat Appl) x2 (THead 
(Bind Abst) x3 x7))) (lift_flat Appl x2 (THead (Bind Abst) x3 x7) (S O) d)) 
(ty3_appl g a x2 x3 H14 x0 x7 H26))))))))))) (lift_gen_bind Abst x4 x5 x1 (S 
O) d H19)))))))) H15)))))))) H11))))))) H7))))))))))))))))))) (\lambda (c0: 
C).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (ty3 g c0 t3 t4)).(\lambda 
(H1: ((\forall (e: C).(\forall (u: T).(\forall (d: nat).((getl d c0 (CHead e 
(Bind Abbr) u)) \to (\forall (a0: C).((csubst1 d u c0 a0) \to (\forall (a: 
C).((drop (S O) d a0 a) \to (ex3_2 T T (\lambda (y1: T).(\lambda (_: 
T).(subst1 d u t3 (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: 
T).(subst1 d u t4 (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 
g a y1 y2)))))))))))))).(\lambda (t0: T).(\lambda (_: (ty3 g c0 t4 
t0)).(\lambda (H3: ((\forall (e: C).(\forall (u: T).(\forall (d: nat).((getl 
d c0 (CHead e (Bind Abbr) u)) \to (\forall (a0: C).((csubst1 d u c0 a0) \to 
(\forall (a: C).((drop (S O) d a0 a) \to (ex3_2 T T (\lambda (y1: T).(\lambda 
(_: T).(subst1 d u t4 (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: 
T).(subst1 d u t0 (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 
g a y1 y2)))))))))))))).(\lambda (e: C).(\lambda (u: T).(\lambda (d: 
nat).(\lambda (H4: (getl d c0 (CHead e (Bind Abbr) u))).(\lambda (a0: 
C).(\lambda (H5: (csubst1 d u c0 a0)).(\lambda (a: C).(\lambda (H6: (drop (S 
O) d a0 a)).(let H7 \def (H3 e u d H4 a0 H5 a H6) in (ex3_2_ind T T (\lambda 
(y1: T).(\lambda (_: T).(subst1 d u t4 (lift (S O) d y1)))) (\lambda (_: 
T).(\lambda (y2: T).(subst1 d u t0 (lift (S O) d y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2))) (ex3_2 T T (\lambda (y1: T).(\lambda 
(_: T).(subst1 d u (THead (Flat Cast) t4 t3) (lift (S O) d y1)))) (\lambda 
(_: T).(\lambda (y2: T).(subst1 d u (THead (Flat Cast) t0 t4) (lift (S O) d 
y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H8: (subst1 d u t4 (lift (S O) d x0))).(\lambda 
(H9: (subst1 d u t0 (lift (S O) d x1))).(\lambda (H10: (ty3 g a x0 x1)).(let 
H11 \def (H1 e u d H4 a0 H5 a H6) in (ex3_2_ind T T (\lambda (y1: T).(\lambda 
(_: T).(subst1 d u t3 (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: 
T).(subst1 d u t4 (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 
g a y1 y2))) (ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(subst1 d u (THead 
(Flat Cast) t4 t3) (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: 
T).(subst1 d u (THead (Flat Cast) t0 t4) (lift (S O) d y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda (x2: T).(\lambda (x3: 
T).(\lambda (H12: (subst1 d u t3 (lift (S O) d x2))).(\lambda (H13: (subst1 d 
u t4 (lift (S O) d x3))).(\lambda (H14: (ty3 g a x2 x3)).(let H15 \def 
(eq_ind T x3 (\lambda (t: T).(ty3 g a x2 t)) H14 x0 (subst1_confluence_lift 
t4 x3 u d H13 x0 H8)) in (ex3_2_intro T T (\lambda (y1: T).(\lambda (_: 
T).(subst1 d u (THead (Flat Cast) t4 t3) (lift (S O) d y1)))) (\lambda (_: 
T).(\lambda (y2: T).(subst1 d u (THead (Flat Cast) t0 t4) (lift (S O) d 
y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) (THead (Flat Cast) 
x0 x2) (THead (Flat Cast) x1 x0) (eq_ind_r T (THead (Flat Cast) (lift (S O) d 
x0) (lift (S O) d x2)) (\lambda (t: T).(subst1 d u (THead (Flat Cast) t4 t3) 
t)) (subst1_head u t4 (lift (S O) d x0) d H8 (Flat Cast) t3 (lift (S O) d x2) 
H12) (lift (S O) d (THead (Flat Cast) x0 x2)) (lift_flat Cast x0 x2 (S O) d)) 
(eq_ind_r T (THead (Flat Cast) (lift (S O) d x1) (lift (S O) d x0)) (\lambda 
(t: T).(subst1 d u (THead (Flat Cast) t0 t4) t)) (subst1_head u t0 (lift (S 
O) d x1) d H9 (Flat Cast) t4 (lift (S O) d x0) H8) (lift (S O) d (THead (Flat 
Cast) x1 x0)) (lift_flat Cast x1 x0 (S O) d)) (ty3_cast g a x2 x0 H15 x1 
H10)))))))) H11))))))) H7)))))))))))))))))) c t1 t2 H))))).
(* COMMENTS
Initial nodes: 12848
END *)

theorem ty3_gen_cvoid:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c 
t1 t2) \to (\forall (e: C).(\forall (u: T).(\forall (d: nat).((getl d c 
(CHead e (Bind Void) u)) \to (\forall (a: C).((drop (S O) d c a) \to (ex3_2 T 
T (\lambda (y1: T).(\lambda (_: T).(eq T t1 (lift (S O) d y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T t2 (lift (S O) d y2)))) (\lambda (y1: T).(\lambda 
(y2: T).(ty3 g a y1 y2))))))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (ty3 g c t1 t2)).(ty3_ind g (\lambda (c0: C).(\lambda (t: T).(\lambda 
(t0: T).(\forall (e: C).(\forall (u: T).(\forall (d: nat).((getl d c0 (CHead 
e (Bind Void) u)) \to (\forall (a: C).((drop (S O) d c0 a) \to (ex3_2 T T 
(\lambda (y1: T).(\lambda (_: T).(eq T t (lift (S O) d y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T t0 (lift (S O) d y2)))) (\lambda (y1: T).(\lambda 
(y2: T).(ty3 g a y1 y2))))))))))))) (\lambda (c0: C).(\lambda (t3: 
T).(\lambda (t: T).(\lambda (H0: (ty3 g c0 t3 t)).(\lambda (H1: ((\forall (e: 
C).(\forall (u: T).(\forall (d: nat).((getl d c0 (CHead e (Bind Void) u)) \to 
(\forall (a: C).((drop (S O) d c0 a) \to (ex3_2 T T (\lambda (y1: T).(\lambda 
(_: T).(eq T t3 (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T t 
(lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 
y2)))))))))))).(\lambda (u: T).(\lambda (t4: T).(\lambda (H2: (ty3 g c0 u 
t4)).(\lambda (H3: ((\forall (e: C).(\forall (u0: T).(\forall (d: nat).((getl 
d c0 (CHead e (Bind Void) u0)) \to (\forall (a: C).((drop (S O) d c0 a) \to 
(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T u (lift (S O) d y1)))) 
(\lambda (_: T).(\lambda (y2: T).(eq T t4 (lift (S O) d y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2)))))))))))).(\lambda (H4: (pc3 c0 t4 
t3)).(\lambda (e: C).(\lambda (u0: T).(\lambda (d: nat).(\lambda (H5: (getl d 
c0 (CHead e (Bind Void) u0))).(\lambda (a: C).(\lambda (H6: (drop (S O) d c0 
a)).(let H7 \def (H3 e u0 d H5 a H6) in (ex3_2_ind T T (\lambda (y1: 
T).(\lambda (_: T).(eq T u (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: 
T).(eq T t4 (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a 
y1 y2))) (ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T u (lift (S O) d 
y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T t3 (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H8: (eq T u (lift (S O) d x0))).(\lambda (H9: 
(eq T t4 (lift (S O) d x1))).(\lambda (H10: (ty3 g a x0 x1)).(let H11 \def 
(eq_ind T t4 (\lambda (t0: T).(pc3 c0 t0 t3)) H4 (lift (S O) d x1) H9) in 
(let H12 \def (eq_ind T t4 (\lambda (t0: T).(ty3 g c0 u t0)) H2 (lift (S O) d 
x1) H9) in (let H13 \def (eq_ind T u (\lambda (t0: T).(ty3 g c0 t0 (lift (S 
O) d x1))) H12 (lift (S O) d x0) H8) in (eq_ind_r T (lift (S O) d x0) 
(\lambda (t0: T).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T t0 (lift 
(S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T t3 (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (let H14 \def (H1 e u0 
d H5 a H6) in (ex3_2_ind T T (\lambda (y1: T).(\lambda (_: T).(eq T t3 (lift 
(S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T t (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) (ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(eq T (lift (S O) d x0) (lift (S O) d y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T t3 (lift (S O) d y2)))) (\lambda (y1: T).(\lambda 
(y2: T).(ty3 g a y1 y2)))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H15: 
(eq T t3 (lift (S O) d x2))).(\lambda (H16: (eq T t (lift (S O) d 
x3))).(\lambda (H17: (ty3 g a x2 x3)).(let H18 \def (eq_ind T t (\lambda (t0: 
T).(ty3 g c0 t3 t0)) H0 (lift (S O) d x3) H16) in (let H19 \def (eq_ind T t3 
(\lambda (t0: T).(ty3 g c0 t0 (lift (S O) d x3))) H18 (lift (S O) d x2) H15) 
in (let H20 \def (eq_ind T t3 (\lambda (t0: T).(pc3 c0 (lift (S O) d x1) t0)) 
H11 (lift (S O) d x2) H15) in (eq_ind_r T (lift (S O) d x2) (\lambda (t0: 
T).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T (lift (S O) d x0) (lift 
(S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T t0 (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (ex3_2_intro T T 
(\lambda (y1: T).(\lambda (_: T).(eq T (lift (S O) d x0) (lift (S O) d y1)))) 
(\lambda (_: T).(\lambda (y2: T).(eq T (lift (S O) d x2) (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) x0 x2 (refl_equal T (lift 
(S O) d x0)) (refl_equal T (lift (S O) d x2)) (ty3_conv g a x2 x3 H17 x0 x1 
H10 (pc3_gen_lift c0 x1 x2 (S O) d H20 a H6))) t3 H15))))))))) H14)) u 
H8))))))))) H7)))))))))))))))))) (\lambda (c0: C).(\lambda (m: nat).(\lambda 
(e: C).(\lambda (u: T).(\lambda (d: nat).(\lambda (_: (getl d c0 (CHead e 
(Bind Void) u))).(\lambda (a: C).(\lambda (_: (drop (S O) d c0 
a)).(ex3_2_intro T T (\lambda (y1: T).(\lambda (_: T).(eq T (TSort m) (lift 
(S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (TSort (next g m)) 
(lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) 
(TSort m) (TSort (next g m)) (eq_ind_r T (TSort m) (\lambda (t: T).(eq T 
(TSort m) t)) (refl_equal T (TSort m)) (lift (S O) d (TSort m)) (lift_sort m 
(S O) d)) (eq_ind_r T (TSort (next g m)) (\lambda (t: T).(eq T (TSort (next g 
m)) t)) (refl_equal T (TSort (next g m))) (lift (S O) d (TSort (next g m))) 
(lift_sort (next g m) (S O) d)) (ty3_sort g a m)))))))))) (\lambda (n: 
nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (H0: (getl n 
c0 (CHead d (Bind Abbr) u))).(\lambda (t: T).(\lambda (H1: (ty3 g d u 
t)).(\lambda (H2: ((\forall (e: C).(\forall (u0: T).(\forall (d0: nat).((getl 
d0 d (CHead e (Bind Void) u0)) \to (\forall (a: C).((drop (S O) d0 d a) \to 
(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T u (lift (S O) d0 y1)))) 
(\lambda (_: T).(\lambda (y2: T).(eq T t (lift (S O) d0 y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2)))))))))))).(\lambda (e: C).(\lambda (u0: 
T).(\lambda (d0: nat).(\lambda (H3: (getl d0 c0 (CHead e (Bind Void) 
u0))).(\lambda (a: C).(\lambda (H4: (drop (S O) d0 c0 a)).(lt_eq_gt_e n d0 
(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T (TLRef n) (lift (S O) d0 
y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (lift (S n) O t) (lift (S O) d0 
y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda (H5: (lt 
n d0)).(let H6 \def (eq_ind nat (minus d0 n) (\lambda (n0: nat).(getl n0 
(CHead d (Bind Abbr) u) (CHead e (Bind Void) u0))) (getl_conf_le d0 (CHead e 
(Bind Void) u0) c0 H3 (CHead d (Bind Abbr) u) n H0 (le_S_n n d0 (le_S (S n) 
d0 H5))) (S (minus d0 (S n))) (minus_x_Sy d0 n H5)) in (let H7 \def (eq_ind 
nat d0 (\lambda (n0: nat).(drop (S O) n0 c0 a)) H4 (S (plus n (minus d0 (S 
n)))) (lt_plus_minus n d0 H5)) in (ex3_2_ind T C (\lambda (v: T).(\lambda (_: 
C).(eq T u (lift (S O) (minus d0 (S n)) v)))) (\lambda (v: T).(\lambda (e0: 
C).(getl n a (CHead e0 (Bind Abbr) v)))) (\lambda (_: T).(\lambda (e0: 
C).(drop (S O) (minus d0 (S n)) d e0))) (ex3_2 T T (\lambda (y1: T).(\lambda 
(_: T).(eq T (TLRef n) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: 
T).(eq T (lift (S n) O t) (lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda 
(y2: T).(ty3 g a y1 y2)))) (\lambda (x0: T).(\lambda (x1: C).(\lambda (H8: 
(eq T u (lift (S O) (minus d0 (S n)) x0))).(\lambda (H9: (getl n a (CHead x1 
(Bind Abbr) x0))).(\lambda (H10: (drop (S O) (minus d0 (S n)) d x1)).(let H11 
\def (eq_ind T u (\lambda (t0: T).(\forall (e0: C).(\forall (u1: T).(\forall 
(d1: nat).((getl d1 d (CHead e0 (Bind Void) u1)) \to (\forall (a0: C).((drop 
(S O) d1 d a0) \to (ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T t0 (lift 
(S O) d1 y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T t (lift (S O) d1 
y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a0 y1 y2))))))))))) H2 (lift 
(S O) (minus d0 (S n)) x0) H8) in (let H12 \def (eq_ind T u (\lambda (t0: 
T).(ty3 g d t0 t)) H1 (lift (S O) (minus d0 (S n)) x0) H8) in (let H13 \def 
(H11 e u0 (minus d0 (S n)) (getl_gen_S (Bind Abbr) d (CHead e (Bind Void) u0) 
u (minus d0 (S n)) H6) x1 H10) in (ex3_2_ind T T (\lambda (y1: T).(\lambda 
(_: T).(eq T (lift (S O) (minus d0 (S n)) x0) (lift (S O) (minus d0 (S n)) 
y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T t (lift (S O) (minus d0 (S n)) 
y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g x1 y1 y2))) (ex3_2 T T 
(\lambda (y1: T).(\lambda (_: T).(eq T (TLRef n) (lift (S O) d0 y1)))) 
(\lambda (_: T).(\lambda (y2: T).(eq T (lift (S n) O t) (lift (S O) d0 y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda (x2: 
T).(\lambda (x3: T).(\lambda (H14: (eq T (lift (S O) (minus d0 (S n)) x0) 
(lift (S O) (minus d0 (S n)) x2))).(\lambda (H15: (eq T t (lift (S O) (minus 
d0 (S n)) x3))).(\lambda (H16: (ty3 g x1 x2 x3)).(let H17 \def (eq_ind T t 
(\lambda (t0: T).(ty3 g d (lift (S O) (minus d0 (S n)) x0) t0)) H12 (lift (S 
O) (minus d0 (S n)) x3) H15) in (eq_ind_r T (lift (S O) (minus d0 (S n)) x3) 
(\lambda (t0: T).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T (TLRef n) 
(lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (lift (S n) O 
t0) (lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 
y2))))) (let H18 \def (eq_ind_r T x2 (\lambda (t0: T).(ty3 g x1 t0 x3)) H16 
x0 (lift_inj x0 x2 (S O) (minus d0 (S n)) H14)) in (eq_ind T (lift (S O) 
(plus (S n) (minus d0 (S n))) (lift (S n) O x3)) (\lambda (t0: T).(ex3_2 T T 
(\lambda (y1: T).(\lambda (_: T).(eq T (TLRef n) (lift (S O) d0 y1)))) 
(\lambda (_: T).(\lambda (y2: T).(eq T t0 (lift (S O) d0 y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2))))) (eq_ind nat d0 (\lambda (n0: 
nat).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T (TLRef n) (lift (S O) 
d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (lift (S O) n0 (lift (S n) O 
x3)) (lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 
y2))))) (ex3_2_intro T T (\lambda (y1: T).(\lambda (_: T).(eq T (TLRef n) 
(lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (lift (S O) d0 
(lift (S n) O x3)) (lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: 
T).(ty3 g a y1 y2))) (TLRef n) (lift (S n) O x3) (eq_ind_r T (TLRef n) 
(\lambda (t0: T).(eq T (TLRef n) t0)) (refl_equal T (TLRef n)) (lift (S O) d0 
(TLRef n)) (lift_lref_lt n (S O) d0 H5)) (refl_equal T (lift (S O) d0 (lift 
(S n) O x3))) (ty3_abbr g n a x1 x0 H9 x3 H18)) (plus (S n) (minus d0 (S n))) 
(le_plus_minus (S n) d0 H5)) (lift (S n) O (lift (S O) (minus d0 (S n)) x3)) 
(lift_d x3 (S O) (S n) (minus d0 (S n)) O (le_O_n (minus d0 (S n)))))) t 
H15))))))) H13))))))))) (getl_drop_conf_lt Abbr c0 d u n H0 a (S O) (minus d0 
(S n)) H7))))) (\lambda (H5: (eq nat n d0)).(let H6 \def (eq_ind_r nat d0 
(\lambda (n0: nat).(drop (S O) n0 c0 a)) H4 n H5) in (let H7 \def (eq_ind_r 
nat d0 (\lambda (n0: nat).(getl n0 c0 (CHead e (Bind Void) u0))) H3 n H5) in 
(eq_ind nat n (\lambda (n0: nat).(ex3_2 T T (\lambda (y1: T).(\lambda (_: 
T).(eq T (TLRef n) (lift (S O) n0 y1)))) (\lambda (_: T).(\lambda (y2: T).(eq 
T (lift (S n) O t) (lift (S O) n0 y2)))) (\lambda (y1: T).(\lambda (y2: 
T).(ty3 g a y1 y2))))) (let H8 \def (eq_ind C (CHead d (Bind Abbr) u) 
(\lambda (c1: C).(getl n c0 c1)) H0 (CHead e (Bind Void) u0) (getl_mono c0 
(CHead d (Bind Abbr) u) n H0 (CHead e (Bind Void) u0) H7)) in (let H9 \def 
(eq_ind C (CHead d (Bind Abbr) u) (\lambda (ee: C).(match ee in C return 
(\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind b) 
\Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow 
True | Abst \Rightarrow False | Void \Rightarrow False]) | (Flat _) 
\Rightarrow False])])) I (CHead e (Bind Void) u0) (getl_mono c0 (CHead d 
(Bind Abbr) u) n H0 (CHead e (Bind Void) u0) H7)) in (False_ind (ex3_2 T T 
(\lambda (y1: T).(\lambda (_: T).(eq T (TLRef n) (lift (S O) n y1)))) 
(\lambda (_: T).(\lambda (y2: T).(eq T (lift (S n) O t) (lift (S O) n y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) H9))) d0 H5)))) (\lambda 
(H5: (lt d0 n)).(eq_ind_r nat (S (plus O (minus n (S O)))) (\lambda (n0: 
nat).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T (TLRef n0) (lift (S O) 
d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (lift (S n) O t) (lift (S O) 
d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (eq_ind nat 
(plus (S O) (minus n (S O))) (\lambda (n0: nat).(ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(eq T (TLRef n0) (lift (S O) d0 y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T (lift (S n) O t) (lift (S O) d0 y2)))) (\lambda 
(y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (eq_ind_r nat (plus (minus n (S 
O)) (S O)) (\lambda (n0: nat).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq 
T (TLRef n0) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T 
(lift (S n) O t) (lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 
g a y1 y2))))) (ex3_2_intro T T (\lambda (y1: T).(\lambda (_: T).(eq T (TLRef 
(plus (minus n (S O)) (S O))) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda 
(y2: T).(eq T (lift (S n) O t) (lift (S O) d0 y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2))) (TLRef (minus n (S O))) (lift n O t) 
(eq_ind_r T (TLRef (plus (minus n (S O)) (S O))) (\lambda (t0: T).(eq T 
(TLRef (plus (minus n (S O)) (S O))) t0)) (refl_equal T (TLRef (plus (minus n 
(S O)) (S O)))) (lift (S O) d0 (TLRef (minus n (S O)))) (lift_lref_ge (minus 
n (S O)) (S O) d0 (lt_le_minus d0 n H5))) (eq_ind_r T (lift (plus (S O) n) O 
t) (\lambda (t0: T).(eq T (lift (S n) O t) t0)) (refl_equal T (lift (S n) O 
t)) (lift (S O) d0 (lift n O t)) (lift_free t n (S O) O d0 (le_S_n d0 (plus O 
n) (le_S (S d0) (plus O n) H5)) (le_O_n d0))) (eq_ind_r nat (S (minus n (S 
O))) (\lambda (n0: nat).(ty3 g a (TLRef (minus n (S O))) (lift n0 O t))) 
(ty3_abbr g (minus n (S O)) a d u (getl_drop_conf_ge n (CHead d (Bind Abbr) 
u) c0 H0 a (S O) d0 H4 (eq_ind_r nat (plus (S O) d0) (\lambda (n0: nat).(le 
n0 n)) H5 (plus d0 (S O)) (plus_sym d0 (S O)))) t H1) n (minus_x_SO n 
(le_lt_trans O d0 n (le_O_n d0) H5)))) (plus (S O) (minus n (S O))) (plus_sym 
(S O) (minus n (S O)))) (S (plus O (minus n (S O)))) (refl_equal nat (S (plus 
O (minus n (S O)))))) n (lt_plus_minus O n (le_lt_trans O d0 n (le_O_n d0) 
H5))))))))))))))))))) (\lambda (n: nat).(\lambda (c0: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (H0: (getl n c0 (CHead d (Bind Abst) 
u))).(\lambda (t: T).(\lambda (H1: (ty3 g d u t)).(\lambda (H2: ((\forall (e: 
C).(\forall (u0: T).(\forall (d0: nat).((getl d0 d (CHead e (Bind Void) u0)) 
\to (\forall (a: C).((drop (S O) d0 d a) \to (ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(eq T u (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda 
(y2: T).(eq T t (lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 
g a y1 y2)))))))))))).(\lambda (e: C).(\lambda (u0: T).(\lambda (d0: 
nat).(\lambda (H3: (getl d0 c0 (CHead e (Bind Void) u0))).(\lambda (a: 
C).(\lambda (H4: (drop (S O) d0 c0 a)).(lt_eq_gt_e n d0 (ex3_2 T T (\lambda 
(y1: T).(\lambda (_: T).(eq T (TLRef n) (lift (S O) d0 y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T (lift (S n) O u) (lift (S O) d0 y2)))) (\lambda 
(y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda (H5: (lt n d0)).(let H6 
\def (eq_ind nat (minus d0 n) (\lambda (n0: nat).(getl n0 (CHead d (Bind 
Abst) u) (CHead e (Bind Void) u0))) (getl_conf_le d0 (CHead e (Bind Void) u0) 
c0 H3 (CHead d (Bind Abst) u) n H0 (le_S_n n d0 (le_S (S n) d0 H5))) (S 
(minus d0 (S n))) (minus_x_Sy d0 n H5)) in (let H7 \def (eq_ind nat d0 
(\lambda (n0: nat).(drop (S O) n0 c0 a)) H4 (S (plus n (minus d0 (S n)))) 
(lt_plus_minus n d0 H5)) in (ex3_2_ind T C (\lambda (v: T).(\lambda (_: 
C).(eq T u (lift (S O) (minus d0 (S n)) v)))) (\lambda (v: T).(\lambda (e0: 
C).(getl n a (CHead e0 (Bind Abst) v)))) (\lambda (_: T).(\lambda (e0: 
C).(drop (S O) (minus d0 (S n)) d e0))) (ex3_2 T T (\lambda (y1: T).(\lambda 
(_: T).(eq T (TLRef n) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: 
T).(eq T (lift (S n) O u) (lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda 
(y2: T).(ty3 g a y1 y2)))) (\lambda (x0: T).(\lambda (x1: C).(\lambda (H8: 
(eq T u (lift (S O) (minus d0 (S n)) x0))).(\lambda (H9: (getl n a (CHead x1 
(Bind Abst) x0))).(\lambda (H10: (drop (S O) (minus d0 (S n)) d x1)).(let H11 
\def (eq_ind T u (\lambda (t0: T).(\forall (e0: C).(\forall (u1: T).(\forall 
(d1: nat).((getl d1 d (CHead e0 (Bind Void) u1)) \to (\forall (a0: C).((drop 
(S O) d1 d a0) \to (ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T t0 (lift 
(S O) d1 y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T t (lift (S O) d1 
y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a0 y1 y2))))))))))) H2 (lift 
(S O) (minus d0 (S n)) x0) H8) in (let H12 \def (eq_ind T u (\lambda (t0: 
T).(ty3 g d t0 t)) H1 (lift (S O) (minus d0 (S n)) x0) H8) in (eq_ind_r T 
(lift (S O) (minus d0 (S n)) x0) (\lambda (t0: T).(ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(eq T (TLRef n) (lift (S O) d0 y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T (lift (S n) O t0) (lift (S O) d0 y2)))) (\lambda 
(y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (let H13 \def (H11 e u0 (minus 
d0 (S n)) (getl_gen_S (Bind Abst) d (CHead e (Bind Void) u0) u (minus d0 (S 
n)) H6) x1 H10) in (ex3_2_ind T T (\lambda (y1: T).(\lambda (_: T).(eq T 
(lift (S O) (minus d0 (S n)) x0) (lift (S O) (minus d0 (S n)) y1)))) (\lambda 
(_: T).(\lambda (y2: T).(eq T t (lift (S O) (minus d0 (S n)) y2)))) (\lambda 
(y1: T).(\lambda (y2: T).(ty3 g x1 y1 y2))) (ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(eq T (TLRef n) (lift (S O) d0 y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T (lift (S n) O (lift (S O) (minus d0 (S n)) x0)) 
(lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) 
(\lambda (x2: T).(\lambda (x3: T).(\lambda (H14: (eq T (lift (S O) (minus d0 
(S n)) x0) (lift (S O) (minus d0 (S n)) x2))).(\lambda (H15: (eq T t (lift (S 
O) (minus d0 (S n)) x3))).(\lambda (H16: (ty3 g x1 x2 x3)).(let H17 \def 
(eq_ind T t (\lambda (t0: T).(ty3 g d (lift (S O) (minus d0 (S n)) x0) t0)) 
H12 (lift (S O) (minus d0 (S n)) x3) H15) in (let H18 \def (eq_ind_r T x2 
(\lambda (t0: T).(ty3 g x1 t0 x3)) H16 x0 (lift_inj x0 x2 (S O) (minus d0 (S 
n)) H14)) in (eq_ind T (lift (S O) (plus (S n) (minus d0 (S n))) (lift (S n) 
O x0)) (\lambda (t0: T).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T 
(TLRef n) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T t0 
(lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) 
(eq_ind nat d0 (\lambda (n0: nat).(ex3_2 T T (\lambda (y1: T).(\lambda (_: 
T).(eq T (TLRef n) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(eq 
T (lift (S O) n0 (lift (S n) O x0)) (lift (S O) d0 y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2))))) (ex3_2_intro T T (\lambda (y1: 
T).(\lambda (_: T).(eq T (TLRef n) (lift (S O) d0 y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T (lift (S O) d0 (lift (S n) O x0)) (lift (S O) d0 
y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) (TLRef n) (lift (S 
n) O x0) (eq_ind_r T (TLRef n) (\lambda (t0: T).(eq T (TLRef n) t0)) 
(refl_equal T (TLRef n)) (lift (S O) d0 (TLRef n)) (lift_lref_lt n (S O) d0 
H5)) (refl_equal T (lift (S O) d0 (lift (S n) O x0))) (ty3_abst g n a x1 x0 
H9 x3 H18)) (plus (S n) (minus d0 (S n))) (le_plus_minus (S n) d0 H5)) (lift 
(S n) O (lift (S O) (minus d0 (S n)) x0)) (lift_d x0 (S O) (S n) (minus d0 (S 
n)) O (le_O_n (minus d0 (S n)))))))))))) H13)) u H8)))))))) 
(getl_drop_conf_lt Abst c0 d u n H0 a (S O) (minus d0 (S n)) H7))))) (\lambda 
(H5: (eq nat n d0)).(let H6 \def (eq_ind_r nat d0 (\lambda (n0: nat).(drop (S 
O) n0 c0 a)) H4 n H5) in (let H7 \def (eq_ind_r nat d0 (\lambda (n0: 
nat).(getl n0 c0 (CHead e (Bind Void) u0))) H3 n H5) in (eq_ind nat n 
(\lambda (n0: nat).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T (TLRef 
n) (lift (S O) n0 y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (lift (S n) O 
u) (lift (S O) n0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 
y2))))) (let H8 \def (eq_ind C (CHead d (Bind Abst) u) (\lambda (c1: C).(getl 
n c0 c1)) H0 (CHead e (Bind Void) u0) (getl_mono c0 (CHead d (Bind Abst) u) n 
H0 (CHead e (Bind Void) u0) H7)) in (let H9 \def (eq_ind C (CHead d (Bind 
Abst) u) (\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with 
[(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind b) \Rightarrow (match b in B return 
(\lambda (_: B).Prop) with [Abbr \Rightarrow False | Abst \Rightarrow True | 
Void \Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead e (Bind 
Void) u0) (getl_mono c0 (CHead d (Bind Abst) u) n H0 (CHead e (Bind Void) u0) 
H7)) in (False_ind (ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T (TLRef 
n) (lift (S O) n y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (lift (S n) O 
u) (lift (S O) n y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) 
H9))) d0 H5)))) (\lambda (H5: (lt d0 n)).(eq_ind_r nat (S (plus O (minus n (S 
O)))) (\lambda (n0: nat).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T 
(TLRef n0) (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (lift 
(S n) O u) (lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a 
y1 y2))))) (eq_ind nat (plus (S O) (minus n (S O))) (\lambda (n0: nat).(ex3_2 
T T (\lambda (y1: T).(\lambda (_: T).(eq T (TLRef n0) (lift (S O) d0 y1)))) 
(\lambda (_: T).(\lambda (y2: T).(eq T (lift (S n) O u) (lift (S O) d0 y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (eq_ind_r nat (plus 
(minus n (S O)) (S O)) (\lambda (n0: nat).(ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(eq T (TLRef n0) (lift (S O) d0 y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T (lift (S n) O u) (lift (S O) d0 y2)))) (\lambda 
(y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (ex3_2_intro T T (\lambda (y1: 
T).(\lambda (_: T).(eq T (TLRef (plus (minus n (S O)) (S O))) (lift (S O) d0 
y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (lift (S n) O u) (lift (S O) d0 
y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) (TLRef (minus n (S 
O))) (lift n O u) (eq_ind_r T (TLRef (plus (minus n (S O)) (S O))) (\lambda 
(t0: T).(eq T (TLRef (plus (minus n (S O)) (S O))) t0)) (refl_equal T (TLRef 
(plus (minus n (S O)) (S O)))) (lift (S O) d0 (TLRef (minus n (S O)))) 
(lift_lref_ge (minus n (S O)) (S O) d0 (lt_le_minus d0 n H5))) (eq_ind_r T 
(lift (plus (S O) n) O u) (\lambda (t0: T).(eq T (lift (S n) O u) t0)) 
(refl_equal T (lift (S n) O u)) (lift (S O) d0 (lift n O u)) (lift_free u n 
(S O) O d0 (le_S_n d0 (plus O n) (le_S (S d0) (plus O n) H5)) (le_O_n d0))) 
(eq_ind_r nat (S (minus n (S O))) (\lambda (n0: nat).(ty3 g a (TLRef (minus n 
(S O))) (lift n0 O u))) (ty3_abst g (minus n (S O)) a d u (getl_drop_conf_ge 
n (CHead d (Bind Abst) u) c0 H0 a (S O) d0 H4 (eq_ind_r nat (plus (S O) d0) 
(\lambda (n0: nat).(le n0 n)) H5 (plus d0 (S O)) (plus_sym d0 (S O)))) t H1) 
n (minus_x_SO n (le_lt_trans O d0 n (le_O_n d0) H5)))) (plus (S O) (minus n 
(S O))) (plus_sym (S O) (minus n (S O)))) (S (plus O (minus n (S O)))) 
(refl_equal nat (S (plus O (minus n (S O)))))) n (lt_plus_minus O n 
(le_lt_trans O d0 n (le_O_n d0) H5))))))))))))))))))) (\lambda (c0: 
C).(\lambda (u: T).(\lambda (t: T).(\lambda (H0: (ty3 g c0 u t)).(\lambda 
(H1: ((\forall (e: C).(\forall (u0: T).(\forall (d: nat).((getl d c0 (CHead e 
(Bind Void) u0)) \to (\forall (a: C).((drop (S O) d c0 a) \to (ex3_2 T T 
(\lambda (y1: T).(\lambda (_: T).(eq T u (lift (S O) d y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T t (lift (S O) d y2)))) (\lambda (y1: T).(\lambda 
(y2: T).(ty3 g a y1 y2)))))))))))).(\lambda (b: B).(\lambda (t3: T).(\lambda 
(t4: T).(\lambda (H2: (ty3 g (CHead c0 (Bind b) u) t3 t4)).(\lambda (H3: 
((\forall (e: C).(\forall (u0: T).(\forall (d: nat).((getl d (CHead c0 (Bind 
b) u) (CHead e (Bind Void) u0)) \to (\forall (a: C).((drop (S O) d (CHead c0 
(Bind b) u) a) \to (ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T t3 (lift 
(S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T t4 (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))))))))))).(\lambda (e: 
C).(\lambda (u0: T).(\lambda (d: nat).(\lambda (H4: (getl d c0 (CHead e (Bind 
Void) u0))).(\lambda (a: C).(\lambda (H5: (drop (S O) d c0 a)).(let H6 \def 
(H1 e u0 d H4 a H5) in (ex3_2_ind T T (\lambda (y1: T).(\lambda (_: T).(eq T 
u (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T t (lift (S O) d 
y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) (ex3_2 T T 
(\lambda (y1: T).(\lambda (_: T).(eq T (THead (Bind b) u t3) (lift (S O) d 
y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (THead (Bind b) u t4) (lift (S 
O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda 
(x0: T).(\lambda (x1: T).(\lambda (H7: (eq T u (lift (S O) d x0))).(\lambda 
(H8: (eq T t (lift (S O) d x1))).(\lambda (H9: (ty3 g a x0 x1)).(let H10 \def 
(eq_ind T t (\lambda (t0: T).(ty3 g c0 u t0)) H0 (lift (S O) d x1) H8) in 
(let H11 \def (eq_ind T u (\lambda (t0: T).(ty3 g c0 t0 (lift (S O) d x1))) 
H10 (lift (S O) d x0) H7) in (let H12 \def (eq_ind T u (\lambda (t0: 
T).(\forall (e0: C).(\forall (u1: T).(\forall (d0: nat).((getl d0 (CHead c0 
(Bind b) t0) (CHead e0 (Bind Void) u1)) \to (\forall (a0: C).((drop (S O) d0 
(CHead c0 (Bind b) t0) a0) \to (ex3_2 T T (\lambda (y1: T).(\lambda (_: 
T).(eq T t3 (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T t4 
(lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a0 y1 
y2))))))))))) H3 (lift (S O) d x0) H7) in (let H13 \def (eq_ind T u (\lambda 
(t0: T).(ty3 g (CHead c0 (Bind b) t0) t3 t4)) H2 (lift (S O) d x0) H7) in 
(eq_ind_r T (lift (S O) d x0) (\lambda (t0: T).(ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(eq T (THead (Bind b) t0 t3) (lift (S O) d y1)))) (\lambda 
(_: T).(\lambda (y2: T).(eq T (THead (Bind b) t0 t4) (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (let H14 \def (H12 e u0 
(S d) (getl_head (Bind b) d c0 (CHead e (Bind Void) u0) H4 (lift (S O) d x0)) 
(CHead a (Bind b) x0) (drop_skip_bind (S O) d c0 a H5 b x0)) in (ex3_2_ind T 
T (\lambda (y1: T).(\lambda (_: T).(eq T t3 (lift (S O) (S d) y1)))) (\lambda 
(_: T).(\lambda (y2: T).(eq T t4 (lift (S O) (S d) y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g (CHead a (Bind b) x0) y1 y2))) (ex3_2 T T (\lambda 
(y1: T).(\lambda (_: T).(eq T (THead (Bind b) (lift (S O) d x0) t3) (lift (S 
O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (THead (Bind b) (lift (S 
O) d x0) t4) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a 
y1 y2)))) (\lambda (x2: T).(\lambda (x3: T).(\lambda (H15: (eq T t3 (lift (S 
O) (S d) x2))).(\lambda (H16: (eq T t4 (lift (S O) (S d) x3))).(\lambda (H17: 
(ty3 g (CHead a (Bind b) x0) x2 x3)).(eq_ind_r T (lift (S O) (S d) x3) 
(\lambda (t0: T).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T (THead 
(Bind b) (lift (S O) d x0) t3) (lift (S O) d y1)))) (\lambda (_: T).(\lambda 
(y2: T).(eq T (THead (Bind b) (lift (S O) d x0) t0) (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (eq_ind_r T (lift (S O) 
(S d) x2) (\lambda (t0: T).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T 
(THead (Bind b) (lift (S O) d x0) t0) (lift (S O) d y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T (THead (Bind b) (lift (S O) d x0) (lift (S O) (S d) 
x3)) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 
y2))))) (ex3_2_intro T T (\lambda (y1: T).(\lambda (_: T).(eq T (THead (Bind 
b) (lift (S O) d x0) (lift (S O) (S d) x2)) (lift (S O) d y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T (THead (Bind b) (lift (S O) d x0) (lift (S O) (S d) 
x3)) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) 
(THead (Bind b) x0 x2) (THead (Bind b) x0 x3) (sym_eq T (lift (S O) d (THead 
(Bind b) x0 x2)) (THead (Bind b) (lift (S O) d x0) (lift (S O) (S d) x2)) 
(lift_bind b x0 x2 (S O) d)) (sym_eq T (lift (S O) d (THead (Bind b) x0 x3)) 
(THead (Bind b) (lift (S O) d x0) (lift (S O) (S d) x3)) (lift_bind b x0 x3 
(S O) d)) (ty3_bind g a x0 x1 H9 b x2 x3 H17)) t3 H15) t4 H16)))))) H14)) u 
H7)))))))))) H6)))))))))))))))))) (\lambda (c0: C).(\lambda (w: T).(\lambda 
(u: T).(\lambda (_: (ty3 g c0 w u)).(\lambda (H1: ((\forall (e: C).(\forall 
(u0: T).(\forall (d: nat).((getl d c0 (CHead e (Bind Void) u0)) \to (\forall 
(a: C).((drop (S O) d c0 a) \to (ex3_2 T T (\lambda (y1: T).(\lambda (_: 
T).(eq T w (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T u 
(lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 
y2)))))))))))).(\lambda (v: T).(\lambda (t: T).(\lambda (H2: (ty3 g c0 v 
(THead (Bind Abst) u t))).(\lambda (H3: ((\forall (e: C).(\forall (u0: 
T).(\forall (d: nat).((getl d c0 (CHead e (Bind Void) u0)) \to (\forall (a: 
C).((drop (S O) d c0 a) \to (ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T 
v (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (THead (Bind 
Abst) u t) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 
y2)))))))))))).(\lambda (e: C).(\lambda (u0: T).(\lambda (d: nat).(\lambda 
(H4: (getl d c0 (CHead e (Bind Void) u0))).(\lambda (a: C).(\lambda (H5: 
(drop (S O) d c0 a)).(let H6 \def (H3 e u0 d H4 a H5) in (ex3_2_ind T T 
(\lambda (y1: T).(\lambda (_: T).(eq T v (lift (S O) d y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T (THead (Bind Abst) u t) (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) (ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(eq T (THead (Flat Appl) w v) (lift (S O) d y1)))) 
(\lambda (_: T).(\lambda (y2: T).(eq T (THead (Flat Appl) w (THead (Bind 
Abst) u t)) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a 
y1 y2)))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H7: (eq T v (lift (S O) 
d x0))).(\lambda (H8: (eq T (THead (Bind Abst) u t) (lift (S O) d 
x1))).(\lambda (H9: (ty3 g a x0 x1)).(let H10 \def (eq_ind T v (\lambda (t0: 
T).(ty3 g c0 t0 (THead (Bind Abst) u t))) H2 (lift (S O) d x0) H7) in 
(eq_ind_r T (lift (S O) d x0) (\lambda (t0: T).(ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(eq T (THead (Flat Appl) w t0) (lift (S O) d y1)))) 
(\lambda (_: T).(\lambda (y2: T).(eq T (THead (Flat Appl) w (THead (Bind 
Abst) u t)) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a 
y1 y2))))) (ex3_2_ind T T (\lambda (y: T).(\lambda (z: T).(eq T x1 (THead 
(Bind Abst) y z)))) (\lambda (y: T).(\lambda (_: T).(eq T u (lift (S O) d 
y)))) (\lambda (_: T).(\lambda (z: T).(eq T t (lift (S O) (S d) z)))) (ex3_2 
T T (\lambda (y1: T).(\lambda (_: T).(eq T (THead (Flat Appl) w (lift (S O) d 
x0)) (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (THead (Flat 
Appl) w (THead (Bind Abst) u t)) (lift (S O) d y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda (x2: T).(\lambda (x3: 
T).(\lambda (H11: (eq T x1 (THead (Bind Abst) x2 x3))).(\lambda (H12: (eq T u 
(lift (S O) d x2))).(\lambda (H13: (eq T t (lift (S O) (S d) x3))).(let H14 
\def (eq_ind T x1 (\lambda (t0: T).(ty3 g a x0 t0)) H9 (THead (Bind Abst) x2 
x3) H11) in (eq_ind_r T (lift (S O) (S d) x3) (\lambda (t0: T).(ex3_2 T T 
(\lambda (y1: T).(\lambda (_: T).(eq T (THead (Flat Appl) w (lift (S O) d 
x0)) (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (THead (Flat 
Appl) w (THead (Bind Abst) u t0)) (lift (S O) d y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2))))) (let H15 \def (eq_ind T u (\lambda 
(t0: T).(\forall (e0: C).(\forall (u1: T).(\forall (d0: nat).((getl d0 c0 
(CHead e0 (Bind Void) u1)) \to (\forall (a0: C).((drop (S O) d0 c0 a0) \to 
(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T w (lift (S O) d0 y1)))) 
(\lambda (_: T).(\lambda (y2: T).(eq T t0 (lift (S O) d0 y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a0 y1 y2))))))))))) H1 (lift (S O) d x2) H12) in 
(eq_ind_r T (lift (S O) d x2) (\lambda (t0: T).(ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(eq T (THead (Flat Appl) w (lift (S O) d x0)) (lift (S O) 
d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (THead (Flat Appl) w (THead 
(Bind Abst) t0 (lift (S O) (S d) x3))) (lift (S O) d y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2))))) (let H16 \def (H15 e u0 d H4 a H5) in 
(ex3_2_ind T T (\lambda (y1: T).(\lambda (_: T).(eq T w (lift (S O) d y1)))) 
(\lambda (_: T).(\lambda (y2: T).(eq T (lift (S O) d x2) (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) (ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(eq T (THead (Flat Appl) w (lift (S O) d x0)) (lift (S O) 
d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (THead (Flat Appl) w (THead 
(Bind Abst) (lift (S O) d x2) (lift (S O) (S d) x3))) (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda (x4: 
T).(\lambda (x5: T).(\lambda (H17: (eq T w (lift (S O) d x4))).(\lambda (H18: 
(eq T (lift (S O) d x2) (lift (S O) d x5))).(\lambda (H19: (ty3 g a x4 
x5)).(eq_ind_r T (lift (S O) d x4) (\lambda (t0: T).(ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(eq T (THead (Flat Appl) t0 (lift (S O) d x0)) (lift (S O) 
d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (THead (Flat Appl) t0 (THead 
(Bind Abst) (lift (S O) d x2) (lift (S O) (S d) x3))) (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (let H20 \def (eq_ind_r 
T x5 (\lambda (t0: T).(ty3 g a x4 t0)) H19 x2 (lift_inj x2 x5 (S O) d H18)) 
in (eq_ind T (lift (S O) d (THead (Bind Abst) x2 x3)) (\lambda (t0: T).(ex3_2 
T T (\lambda (y1: T).(\lambda (_: T).(eq T (THead (Flat Appl) (lift (S O) d 
x4) (lift (S O) d x0)) (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: 
T).(eq T (THead (Flat Appl) (lift (S O) d x4) t0) (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (eq_ind T (lift (S O) d 
(THead (Flat Appl) x4 x0)) (\lambda (t0: T).(ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(eq T t0 (lift (S O) d y1)))) (\lambda (_: T).(\lambda 
(y2: T).(eq T (THead (Flat Appl) (lift (S O) d x4) (lift (S O) d (THead (Bind 
Abst) x2 x3))) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g 
a y1 y2))))) (eq_ind T (lift (S O) d (THead (Flat Appl) x4 (THead (Bind Abst) 
x2 x3))) (\lambda (t0: T).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T 
(lift (S O) d (THead (Flat Appl) x4 x0)) (lift (S O) d y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T t0 (lift (S O) d y2)))) (\lambda (y1: T).(\lambda 
(y2: T).(ty3 g a y1 y2))))) (ex3_2_intro T T (\lambda (y1: T).(\lambda (_: 
T).(eq T (lift (S O) d (THead (Flat Appl) x4 x0)) (lift (S O) d y1)))) 
(\lambda (_: T).(\lambda (y2: T).(eq T (lift (S O) d (THead (Flat Appl) x4 
(THead (Bind Abst) x2 x3))) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda 
(y2: T).(ty3 g a y1 y2))) (THead (Flat Appl) x4 x0) (THead (Flat Appl) x4 
(THead (Bind Abst) x2 x3)) (refl_equal T (lift (S O) d (THead (Flat Appl) x4 
x0))) (refl_equal T (lift (S O) d (THead (Flat Appl) x4 (THead (Bind Abst) x2 
x3)))) (ty3_appl g a x4 x2 H20 x0 x3 H14)) (THead (Flat Appl) (lift (S O) d 
x4) (lift (S O) d (THead (Bind Abst) x2 x3))) (lift_flat Appl x4 (THead (Bind 
Abst) x2 x3) (S O) d)) (THead (Flat Appl) (lift (S O) d x4) (lift (S O) d 
x0)) (lift_flat Appl x4 x0 (S O) d)) (THead (Bind Abst) (lift (S O) d x2) 
(lift (S O) (S d) x3)) (lift_bind Abst x2 x3 (S O) d))) w H17)))))) H16)) u 
H12)) t H13))))))) (lift_gen_bind Abst u t x1 (S O) d H8)) v H7))))))) 
H6))))))))))))))))) (\lambda (c0: C).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (H0: (ty3 g c0 t3 t4)).(\lambda (H1: ((\forall (e: C).(\forall 
(u: T).(\forall (d: nat).((getl d c0 (CHead e (Bind Void) u)) \to (\forall 
(a: C).((drop (S O) d c0 a) \to (ex3_2 T T (\lambda (y1: T).(\lambda (_: 
T).(eq T t3 (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T t4 
(lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 
y2)))))))))))).(\lambda (t0: T).(\lambda (H2: (ty3 g c0 t4 t0)).(\lambda (H3: 
((\forall (e: C).(\forall (u: T).(\forall (d: nat).((getl d c0 (CHead e (Bind 
Void) u)) \to (\forall (a: C).((drop (S O) d c0 a) \to (ex3_2 T T (\lambda 
(y1: T).(\lambda (_: T).(eq T t4 (lift (S O) d y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T t0 (lift (S O) d y2)))) (\lambda (y1: T).(\lambda 
(y2: T).(ty3 g a y1 y2)))))))))))).(\lambda (e: C).(\lambda (u: T).(\lambda 
(d: nat).(\lambda (H4: (getl d c0 (CHead e (Bind Void) u))).(\lambda (a: 
C).(\lambda (H5: (drop (S O) d c0 a)).(let H6 \def (H3 e u d H4 a H5) in 
(ex3_2_ind T T (\lambda (y1: T).(\lambda (_: T).(eq T t4 (lift (S O) d y1)))) 
(\lambda (_: T).(\lambda (y2: T).(eq T t0 (lift (S O) d y2)))) (\lambda (y1: 
T).(\lambda (y2: T).(ty3 g a y1 y2))) (ex3_2 T T (\lambda (y1: T).(\lambda 
(_: T).(eq T (THead (Flat Cast) t4 t3) (lift (S O) d y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T (THead (Flat Cast) t0 t4) (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H7: (eq T t4 (lift (S O) d x0))).(\lambda (H8: 
(eq T t0 (lift (S O) d x1))).(\lambda (H9: (ty3 g a x0 x1)).(let H10 \def 
(eq_ind T t0 (\lambda (t: T).(ty3 g c0 t4 t)) H2 (lift (S O) d x1) H8) in 
(eq_ind_r T (lift (S O) d x1) (\lambda (t: T).(ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(eq T (THead (Flat Cast) t4 t3) (lift (S O) d y1)))) 
(\lambda (_: T).(\lambda (y2: T).(eq T (THead (Flat Cast) t t4) (lift (S O) d 
y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (let H11 \def 
(eq_ind T t4 (\lambda (t: T).(ty3 g c0 t (lift (S O) d x1))) H10 (lift (S O) 
d x0) H7) in (let H12 \def (eq_ind T t4 (\lambda (t: T).(\forall (e0: 
C).(\forall (u0: T).(\forall (d0: nat).((getl d0 c0 (CHead e0 (Bind Void) 
u0)) \to (\forall (a0: C).((drop (S O) d0 c0 a0) \to (ex3_2 T T (\lambda (y1: 
T).(\lambda (_: T).(eq T t3 (lift (S O) d0 y1)))) (\lambda (_: T).(\lambda 
(y2: T).(eq T t (lift (S O) d0 y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 
g a0 y1 y2))))))))))) H1 (lift (S O) d x0) H7) in (let H13 \def (eq_ind T t4 
(\lambda (t: T).(ty3 g c0 t3 t)) H0 (lift (S O) d x0) H7) in (eq_ind_r T 
(lift (S O) d x0) (\lambda (t: T).(ex3_2 T T (\lambda (y1: T).(\lambda (_: 
T).(eq T (THead (Flat Cast) t t3) (lift (S O) d y1)))) (\lambda (_: 
T).(\lambda (y2: T).(eq T (THead (Flat Cast) (lift (S O) d x1) t) (lift (S O) 
d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (let H14 \def 
(H12 e u d H4 a H5) in (ex3_2_ind T T (\lambda (y1: T).(\lambda (_: T).(eq T 
t3 (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T (lift (S O) d 
x0) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) 
(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T (THead (Flat Cast) (lift (S 
O) d x0) t3) (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: T).(eq T 
(THead (Flat Cast) (lift (S O) d x1) (lift (S O) d x0)) (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2)))) (\lambda (x2: 
T).(\lambda (x3: T).(\lambda (H15: (eq T t3 (lift (S O) d x2))).(\lambda 
(H16: (eq T (lift (S O) d x0) (lift (S O) d x3))).(\lambda (H17: (ty3 g a x2 
x3)).(let H18 \def (eq_ind T t3 (\lambda (t: T).(ty3 g c0 t (lift (S O) d 
x0))) H13 (lift (S O) d x2) H15) in (eq_ind_r T (lift (S O) d x2) (\lambda 
(t: T).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T (THead (Flat Cast) 
(lift (S O) d x0) t) (lift (S O) d y1)))) (\lambda (_: T).(\lambda (y2: 
T).(eq T (THead (Flat Cast) (lift (S O) d x1) (lift (S O) d x0)) (lift (S O) 
d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))))) (let H19 \def 
(eq_ind_r T x3 (\lambda (t: T).(ty3 g a x2 t)) H17 x0 (lift_inj x0 x3 (S O) d 
H16)) in (eq_ind T (lift (S O) d (THead (Flat Cast) x0 x2)) (\lambda (t: 
T).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T t (lift (S O) d y1)))) 
(\lambda (_: T).(\lambda (y2: T).(eq T (THead (Flat Cast) (lift (S O) d x1) 
(lift (S O) d x0)) (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: 
T).(ty3 g a y1 y2))))) (eq_ind T (lift (S O) d (THead (Flat Cast) x1 x0)) 
(\lambda (t: T).(ex3_2 T T (\lambda (y1: T).(\lambda (_: T).(eq T (lift (S O) 
d (THead (Flat Cast) x0 x2)) (lift (S O) d y1)))) (\lambda (_: T).(\lambda 
(y2: T).(eq T t (lift (S O) d y2)))) (\lambda (y1: T).(\lambda (y2: T).(ty3 g 
a y1 y2))))) (ex3_2_intro T T (\lambda (y1: T).(\lambda (_: T).(eq T (lift (S 
O) d (THead (Flat Cast) x0 x2)) (lift (S O) d y1)))) (\lambda (_: T).(\lambda 
(y2: T).(eq T (lift (S O) d (THead (Flat Cast) x1 x0)) (lift (S O) d y2)))) 
(\lambda (y1: T).(\lambda (y2: T).(ty3 g a y1 y2))) (THead (Flat Cast) x0 x2) 
(THead (Flat Cast) x1 x0) (refl_equal T (lift (S O) d (THead (Flat Cast) x0 
x2))) (refl_equal T (lift (S O) d (THead (Flat Cast) x1 x0))) (ty3_cast g a 
x2 x0 H19 x1 H9)) (THead (Flat Cast) (lift (S O) d x1) (lift (S O) d x0)) 
(lift_flat Cast x1 x0 (S O) d)) (THead (Flat Cast) (lift (S O) d x0) (lift (S 
O) d x2)) (lift_flat Cast x0 x2 (S O) d))) t3 H15))))))) H14)) t4 H7)))) t0 
H8))))))) H6)))))))))))))))) c t1 t2 H))))).
(* COMMENTS
Initial nodes: 13105
END *)

