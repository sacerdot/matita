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

include "Basic-1/pr0/subst1.ma".

include "Basic-1/pr0/fwd.ma".

include "Basic-1/csubst1/getl.ma".

include "Basic-1/csubst1/fwd.ma".

include "Basic-1/subst1/subst1.ma".

include "Basic-1/getl/drop.ma".

theorem pr2_delta1:
 \forall (c: C).(\forall (d: C).(\forall (u: T).(\forall (i: nat).((getl i c 
(CHead d (Bind Abbr) u)) \to (\forall (t1: T).(\forall (t2: T).((pr0 t1 t2) 
\to (\forall (t: T).((subst1 i u t2 t) \to (pr2 c t1 t))))))))))
\def
 \lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead d (Bind Abbr) u))).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (H0: (pr0 t1 t2)).(\lambda (t: T).(\lambda (H1: (subst1 i u t2 
t)).(subst1_ind i u t2 (\lambda (t0: T).(pr2 c t1 t0)) (pr2_free c t1 t2 H0) 
(\lambda (t0: T).(\lambda (H2: (subst0 i u t2 t0)).(pr2_delta c d u i H t1 t2 
H0 t0 H2))) t H1)))))))))).
(* COMMENTS
Initial nodes: 111
END *)

theorem pr2_subst1:
 \forall (c: C).(\forall (e: C).(\forall (v: T).(\forall (i: nat).((getl i c 
(CHead e (Bind Abbr) v)) \to (\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) 
\to (\forall (w1: T).((subst1 i v t1 w1) \to (ex2 T (\lambda (w2: T).(pr2 c 
w1 w2)) (\lambda (w2: T).(subst1 i v t2 w2))))))))))))
\def
 \lambda (c: C).(\lambda (e: C).(\lambda (v: T).(\lambda (i: nat).(\lambda 
(H: (getl i c (CHead e (Bind Abbr) v))).(\lambda (t1: T).(\lambda (t2: 
T).(\lambda (H0: (pr2 c t1 t2)).(insert_eq C c (\lambda (c0: C).(pr2 c0 t1 
t2)) (\lambda (c0: C).(\forall (w1: T).((subst1 i v t1 w1) \to (ex2 T 
(\lambda (w2: T).(pr2 c0 w1 w2)) (\lambda (w2: T).(subst1 i v t2 w2)))))) 
(\lambda (y: C).(\lambda (H1: (pr2 y t1 t2)).(pr2_ind (\lambda (c0: 
C).(\lambda (t: T).(\lambda (t0: T).((eq C c0 c) \to (\forall (w1: 
T).((subst1 i v t w1) \to (ex2 T (\lambda (w2: T).(pr2 c0 w1 w2)) (\lambda 
(w2: T).(subst1 i v t0 w2))))))))) (\lambda (c0: C).(\lambda (t3: T).(\lambda 
(t4: T).(\lambda (H2: (pr0 t3 t4)).(\lambda (H3: (eq C c0 c)).(\lambda (w1: 
T).(\lambda (H4: (subst1 i v t3 w1)).(eq_ind_r C c (\lambda (c1: C).(ex2 T 
(\lambda (w2: T).(pr2 c1 w1 w2)) (\lambda (w2: T).(subst1 i v t4 w2)))) 
(ex2_ind T (\lambda (w2: T).(pr0 w1 w2)) (\lambda (w2: T).(subst1 i v t4 w2)) 
(ex2 T (\lambda (w2: T).(pr2 c w1 w2)) (\lambda (w2: T).(subst1 i v t4 w2))) 
(\lambda (x: T).(\lambda (H5: (pr0 w1 x)).(\lambda (H6: (subst1 i v t4 
x)).(ex_intro2 T (\lambda (w2: T).(pr2 c w1 w2)) (\lambda (w2: T).(subst1 i v 
t4 w2)) x (pr2_free c w1 x H5) H6)))) (pr0_subst1 t3 t4 H2 v w1 i H4 v 
(pr0_refl v))) c0 H3)))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (u: 
T).(\lambda (i0: nat).(\lambda (H2: (getl i0 c0 (CHead d (Bind Abbr) 
u))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H3: (pr0 t3 t4)).(\lambda 
(t: T).(\lambda (H4: (subst0 i0 u t4 t)).(\lambda (H5: (eq C c0 c)).(\lambda 
(w1: T).(\lambda (H6: (subst1 i v t3 w1)).(let H7 \def (eq_ind C c0 (\lambda 
(c1: C).(getl i0 c1 (CHead d (Bind Abbr) u))) H2 c H5) in (eq_ind_r C c 
(\lambda (c1: C).(ex2 T (\lambda (w2: T).(pr2 c1 w1 w2)) (\lambda (w2: 
T).(subst1 i v t w2)))) (ex2_ind T (\lambda (w2: T).(pr0 w1 w2)) (\lambda 
(w2: T).(subst1 i v t4 w2)) (ex2 T (\lambda (w2: T).(pr2 c w1 w2)) (\lambda 
(w2: T).(subst1 i v t w2))) (\lambda (x: T).(\lambda (H8: (pr0 w1 
x)).(\lambda (H9: (subst1 i v t4 x)).(neq_eq_e i i0 (ex2 T (\lambda (w2: 
T).(pr2 c w1 w2)) (\lambda (w2: T).(subst1 i v t w2))) (\lambda (H10: (not 
(eq nat i i0))).(ex2_ind T (\lambda (t0: T).(subst1 i v t t0)) (\lambda (t0: 
T).(subst1 i0 u x t0)) (ex2 T (\lambda (w2: T).(pr2 c w1 w2)) (\lambda (w2: 
T).(subst1 i v t w2))) (\lambda (x0: T).(\lambda (H11: (subst1 i v t 
x0)).(\lambda (H12: (subst1 i0 u x x0)).(ex_intro2 T (\lambda (w2: T).(pr2 c 
w1 w2)) (\lambda (w2: T).(subst1 i v t w2)) x0 (pr2_delta1 c d u i0 H7 w1 x 
H8 x0 H12) H11)))) (subst1_confluence_neq t4 t u i0 (subst1_single i0 u t4 t 
H4) x v i H9 (sym_not_eq nat i i0 H10)))) (\lambda (H10: (eq nat i i0)).(let 
H11 \def (eq_ind_r nat i0 (\lambda (n: nat).(subst0 n u t4 t)) H4 i H10) in 
(let H12 \def (eq_ind_r nat i0 (\lambda (n: nat).(getl n c (CHead d (Bind 
Abbr) u))) H7 i H10) in (let H13 \def (eq_ind C (CHead e (Bind Abbr) v) 
(\lambda (c1: C).(getl i c c1)) H (CHead d (Bind Abbr) u) (getl_mono c (CHead 
e (Bind Abbr) v) i H (CHead d (Bind Abbr) u) H12)) in (let H14 \def (f_equal 
C C (\lambda (e0: C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow e | (CHead c1 _ _) \Rightarrow c1])) (CHead e (Bind Abbr) v) 
(CHead d (Bind Abbr) u) (getl_mono c (CHead e (Bind Abbr) v) i H (CHead d 
(Bind Abbr) u) H12)) in ((let H15 \def (f_equal C T (\lambda (e0: C).(match 
e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow v | (CHead _ _ 
t0) \Rightarrow t0])) (CHead e (Bind Abbr) v) (CHead d (Bind Abbr) u) 
(getl_mono c (CHead e (Bind Abbr) v) i H (CHead d (Bind Abbr) u) H12)) in 
(\lambda (H16: (eq C e d)).(let H17 \def (eq_ind_r T u (\lambda (t0: T).(getl 
i c (CHead d (Bind Abbr) t0))) H13 v H15) in (let H18 \def (eq_ind_r T u 
(\lambda (t0: T).(subst0 i t0 t4 t)) H11 v H15) in (let H19 \def (eq_ind_r C 
d (\lambda (c1: C).(getl i c (CHead c1 (Bind Abbr) v))) H17 e H16) in 
(ex2_ind T (\lambda (t0: T).(subst1 i v t t0)) (\lambda (t0: T).(subst1 i v x 
t0)) (ex2 T (\lambda (w2: T).(pr2 c w1 w2)) (\lambda (w2: T).(subst1 i v t 
w2))) (\lambda (x0: T).(\lambda (H20: (subst1 i v t x0)).(\lambda (H21: 
(subst1 i v x x0)).(ex_intro2 T (\lambda (w2: T).(pr2 c w1 w2)) (\lambda (w2: 
T).(subst1 i v t w2)) x0 (pr2_delta1 c e v i H19 w1 x H8 x0 H21) H20)))) 
(subst1_confluence_eq t4 t v i (subst1_single i v t4 t H18) x H9))))))) 
H14)))))))))) (pr0_subst1 t3 t4 H3 v w1 i H6 v (pr0_refl v))) c0 
H5))))))))))))))) y t1 t2 H1))) H0)))))))).
(* COMMENTS
Initial nodes: 1311
END *)

theorem pr2_gen_cabbr:
 \forall (c: C).(\forall (t1: T).(\forall (t2: T).((pr2 c t1 t2) \to (\forall 
(e: C).(\forall (u: T).(\forall (d: nat).((getl d c (CHead e (Bind Abbr) u)) 
\to (\forall (a0: C).((csubst1 d u c a0) \to (\forall (a: C).((drop (S O) d 
a0 a) \to (\forall (x1: T).((subst1 d u t1 (lift (S O) d x1)) \to (ex2 T 
(\lambda (x2: T).(subst1 d u t2 (lift (S O) d x2))) (\lambda (x2: T).(pr2 a 
x1 x2))))))))))))))))
\def
 \lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (H: (pr2 c t1 
t2)).(pr2_ind (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: T).(\forall (e: 
C).(\forall (u: T).(\forall (d: nat).((getl d c0 (CHead e (Bind Abbr) u)) \to 
(\forall (a0: C).((csubst1 d u c0 a0) \to (\forall (a: C).((drop (S O) d a0 
a) \to (\forall (x1: T).((subst1 d u t (lift (S O) d x1)) \to (ex2 T (\lambda 
(x2: T).(subst1 d u t0 (lift (S O) d x2))) (\lambda (x2: T).(pr2 a x1 
x2)))))))))))))))) (\lambda (c0: C).(\lambda (t3: T).(\lambda (t4: 
T).(\lambda (H0: (pr0 t3 t4)).(\lambda (e: C).(\lambda (u: T).(\lambda (d: 
nat).(\lambda (_: (getl d c0 (CHead e (Bind Abbr) u))).(\lambda (a0: 
C).(\lambda (_: (csubst1 d u c0 a0)).(\lambda (a: C).(\lambda (_: (drop (S O) 
d a0 a)).(\lambda (x1: T).(\lambda (H4: (subst1 d u t3 (lift (S O) d 
x1))).(ex2_ind T (\lambda (w2: T).(pr0 (lift (S O) d x1) w2)) (\lambda (w2: 
T).(subst1 d u t4 w2)) (ex2 T (\lambda (x2: T).(subst1 d u t4 (lift (S O) d 
x2))) (\lambda (x2: T).(pr2 a x1 x2))) (\lambda (x: T).(\lambda (H5: (pr0 
(lift (S O) d x1) x)).(\lambda (H6: (subst1 d u t4 x)).(ex2_ind T (\lambda 
(t5: T).(eq T x (lift (S O) d t5))) (\lambda (t5: T).(pr0 x1 t5)) (ex2 T 
(\lambda (x2: T).(subst1 d u t4 (lift (S O) d x2))) (\lambda (x2: T).(pr2 a 
x1 x2))) (\lambda (x0: T).(\lambda (H7: (eq T x (lift (S O) d x0))).(\lambda 
(H8: (pr0 x1 x0)).(let H9 \def (eq_ind T x (\lambda (t: T).(subst1 d u t4 t)) 
H6 (lift (S O) d x0) H7) in (ex_intro2 T (\lambda (x2: T).(subst1 d u t4 
(lift (S O) d x2))) (\lambda (x2: T).(pr2 a x1 x2)) x0 H9 (pr2_free a x1 x0 
H8)))))) (pr0_gen_lift x1 x (S O) d H5))))) (pr0_subst1 t3 t4 H0 u (lift (S 
O) d x1) d H4 u (pr0_refl u))))))))))))))))) (\lambda (c0: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c0 (CHead d (Bind 
Abbr) u))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (H1: (pr0 t3 
t4)).(\lambda (t: T).(\lambda (H2: (subst0 i u t4 t)).(\lambda (e: 
C).(\lambda (u0: T).(\lambda (d0: nat).(\lambda (H3: (getl d0 c0 (CHead e 
(Bind Abbr) u0))).(\lambda (a0: C).(\lambda (H4: (csubst1 d0 u0 c0 
a0)).(\lambda (a: C).(\lambda (H5: (drop (S O) d0 a0 a)).(\lambda (x1: 
T).(\lambda (H6: (subst1 d0 u0 t3 (lift (S O) d0 x1))).(ex2_ind T (\lambda 
(w2: T).(pr0 (lift (S O) d0 x1) w2)) (\lambda (w2: T).(subst1 d0 u0 t4 w2)) 
(ex2 T (\lambda (x2: T).(subst1 d0 u0 t (lift (S O) d0 x2))) (\lambda (x2: 
T).(pr2 a x1 x2))) (\lambda (x: T).(\lambda (H7: (pr0 (lift (S O) d0 x1) 
x)).(\lambda (H8: (subst1 d0 u0 t4 x)).(ex2_ind T (\lambda (t5: T).(eq T x 
(lift (S O) d0 t5))) (\lambda (t5: T).(pr0 x1 t5)) (ex2 T (\lambda (x2: 
T).(subst1 d0 u0 t (lift (S O) d0 x2))) (\lambda (x2: T).(pr2 a x1 x2))) 
(\lambda (x0: T).(\lambda (H9: (eq T x (lift (S O) d0 x0))).(\lambda (H10: 
(pr0 x1 x0)).(let H11 \def (eq_ind T x (\lambda (t0: T).(subst1 d0 u0 t4 t0)) 
H8 (lift (S O) d0 x0) H9) in (lt_eq_gt_e i d0 (ex2 T (\lambda (x2: T).(subst1 
d0 u0 t (lift (S O) d0 x2))) (\lambda (x2: T).(pr2 a x1 x2))) (\lambda (H12: 
(lt i d0)).(ex2_ind T (\lambda (t0: T).(subst1 d0 u0 t t0)) (\lambda (t0: 
T).(subst1 i u (lift (S O) d0 x0) t0)) (ex2 T (\lambda (x2: T).(subst1 d0 u0 
t (lift (S O) d0 x2))) (\lambda (x2: T).(pr2 a x1 x2))) (\lambda (x2: 
T).(\lambda (H13: (subst1 d0 u0 t x2)).(\lambda (H14: (subst1 i u (lift (S O) 
d0 x0) x2)).(ex2_ind C (\lambda (e2: C).(csubst1 (minus d0 i) u0 (CHead d 
(Bind Abbr) u) e2)) (\lambda (e2: C).(getl i a0 e2)) (ex2 T (\lambda (x3: 
T).(subst1 d0 u0 t (lift (S O) d0 x3))) (\lambda (x3: T).(pr2 a x1 x3))) 
(\lambda (x3: C).(\lambda (H15: (csubst1 (minus d0 i) u0 (CHead d (Bind Abbr) 
u) x3)).(\lambda (H16: (getl i a0 x3)).(let H17 \def (eq_ind nat (minus d0 i) 
(\lambda (n: nat).(csubst1 n u0 (CHead d (Bind Abbr) u) x3)) H15 (S (minus d0 
(S i))) (minus_x_Sy d0 i H12)) in (let H18 \def (csubst1_gen_head (Bind Abbr) 
d x3 u u0 (minus d0 (S i)) H17) in (ex3_2_ind T C (\lambda (u2: T).(\lambda 
(c2: C).(eq C x3 (CHead c2 (Bind Abbr) u2)))) (\lambda (u2: T).(\lambda (_: 
C).(subst1 (minus d0 (S i)) u0 u u2))) (\lambda (_: T).(\lambda (c2: 
C).(csubst1 (minus d0 (S i)) u0 d c2))) (ex2 T (\lambda (x4: T).(subst1 d0 u0 
t (lift (S O) d0 x4))) (\lambda (x4: T).(pr2 a x1 x4))) (\lambda (x4: 
T).(\lambda (x5: C).(\lambda (H19: (eq C x3 (CHead x5 (Bind Abbr) 
x4))).(\lambda (H20: (subst1 (minus d0 (S i)) u0 u x4)).(\lambda (_: (csubst1 
(minus d0 (S i)) u0 d x5)).(let H22 \def (eq_ind C x3 (\lambda (c1: C).(getl 
i a0 c1)) H16 (CHead x5 (Bind Abbr) x4) H19) in (let H23 \def (eq_ind nat d0 
(\lambda (n: nat).(drop (S O) n a0 a)) H5 (S (plus i (minus d0 (S i)))) 
(lt_plus_minus i d0 H12)) in (ex3_2_ind T C (\lambda (v: T).(\lambda (_: 
C).(eq T x4 (lift (S O) (minus d0 (S i)) v)))) (\lambda (v: T).(\lambda (e0: 
C).(getl i a (CHead e0 (Bind Abbr) v)))) (\lambda (_: T).(\lambda (e0: 
C).(drop (S O) (minus d0 (S i)) x5 e0))) (ex2 T (\lambda (x6: T).(subst1 d0 
u0 t (lift (S O) d0 x6))) (\lambda (x6: T).(pr2 a x1 x6))) (\lambda (x6: 
T).(\lambda (x7: C).(\lambda (H24: (eq T x4 (lift (S O) (minus d0 (S i)) 
x6))).(\lambda (H25: (getl i a (CHead x7 (Bind Abbr) x6))).(\lambda (_: (drop 
(S O) (minus d0 (S i)) x5 x7)).(let H27 \def (eq_ind T x4 (\lambda (t0: 
T).(subst1 (minus d0 (S i)) u0 u t0)) H20 (lift (S O) (minus d0 (S i)) x6) 
H24) in (ex2_ind T (\lambda (t0: T).(subst1 i (lift (S O) (minus d0 (S i)) 
x6) (lift (S O) d0 x0) t0)) (\lambda (t0: T).(subst1 (S (plus (minus d0 (S 
i)) i)) u0 x2 t0)) (ex2 T (\lambda (x8: T).(subst1 d0 u0 t (lift (S O) d0 
x8))) (\lambda (x8: T).(pr2 a x1 x8))) (\lambda (x8: T).(\lambda (H28: 
(subst1 i (lift (S O) (minus d0 (S i)) x6) (lift (S O) d0 x0) x8)).(\lambda 
(H29: (subst1 (S (plus (minus d0 (S i)) i)) u0 x2 x8)).(let H30 \def (eq_ind 
nat d0 (\lambda (n: nat).(subst1 i (lift (S O) (minus d0 (S i)) x6) (lift (S 
O) n x0) x8)) H28 (S (plus i (minus d0 (S i)))) (lt_plus_minus i d0 H12)) in 
(ex2_ind T (\lambda (t5: T).(eq T x8 (lift (S O) (S (plus i (minus d0 (S 
i)))) t5))) (\lambda (t5: T).(subst1 i x6 x0 t5)) (ex2 T (\lambda (x9: 
T).(subst1 d0 u0 t (lift (S O) d0 x9))) (\lambda (x9: T).(pr2 a x1 x9))) 
(\lambda (x9: T).(\lambda (H31: (eq T x8 (lift (S O) (S (plus i (minus d0 (S 
i)))) x9))).(\lambda (H32: (subst1 i x6 x0 x9)).(let H33 \def (eq_ind T x8 
(\lambda (t0: T).(subst1 (S (plus (minus d0 (S i)) i)) u0 x2 t0)) H29 (lift 
(S O) (S (plus i (minus d0 (S i)))) x9) H31) in (let H34 \def (eq_ind_r nat 
(S (plus i (minus d0 (S i)))) (\lambda (n: nat).(subst1 (S (plus (minus d0 (S 
i)) i)) u0 x2 (lift (S O) n x9))) H33 d0 (lt_plus_minus i d0 H12)) in (let 
H35 \def (eq_ind_r nat (S (plus (minus d0 (S i)) i)) (\lambda (n: 
nat).(subst1 n u0 x2 (lift (S O) d0 x9))) H34 d0 (lt_plus_minus_r i d0 H12)) 
in (ex_intro2 T (\lambda (x10: T).(subst1 d0 u0 t (lift (S O) d0 x10))) 
(\lambda (x10: T).(pr2 a x1 x10)) x9 (subst1_trans x2 t u0 d0 H13 (lift (S O) 
d0 x9) H35) (pr2_delta1 a x7 x6 i H25 x1 x0 H10 x9 H32)))))))) 
(subst1_gen_lift_lt x6 x0 x8 i (S O) (minus d0 (S i)) H30)))))) 
(subst1_subst1_back (lift (S O) d0 x0) x2 u i H14 (lift (S O) (minus d0 (S 
i)) x6) u0 (minus d0 (S i)) H27)))))))) (getl_drop_conf_lt Abbr a0 x5 x4 i 
H22 a (S O) (minus d0 (S i)) H23))))))))) H18)))))) (csubst1_getl_lt d0 i H12 
c0 a0 u0 H4 (CHead d (Bind Abbr) u) H0))))) (subst1_confluence_neq t4 t u i 
(subst1_single i u t4 t H2) (lift (S O) d0 x0) u0 d0 H11 (lt_neq i d0 H12)))) 
(\lambda (H12: (eq nat i d0)).(let H13 \def (eq_ind_r nat d0 (\lambda (n: 
nat).(subst1 n u0 t4 (lift (S O) n x0))) H11 i H12) in (let H14 \def 
(eq_ind_r nat d0 (\lambda (n: nat).(drop (S O) n a0 a)) H5 i H12) in (let H15 
\def (eq_ind_r nat d0 (\lambda (n: nat).(csubst1 n u0 c0 a0)) H4 i H12) in 
(let H16 \def (eq_ind_r nat d0 (\lambda (n: nat).(getl n c0 (CHead e (Bind 
Abbr) u0))) H3 i H12) in (eq_ind nat i (\lambda (n: nat).(ex2 T (\lambda (x2: 
T).(subst1 n u0 t (lift (S O) n x2))) (\lambda (x2: T).(pr2 a x1 x2)))) (let 
H17 \def (eq_ind C (CHead d (Bind Abbr) u) (\lambda (c1: C).(getl i c0 c1)) 
H0 (CHead e (Bind Abbr) u0) (getl_mono c0 (CHead d (Bind Abbr) u) i H0 (CHead 
e (Bind Abbr) u0) H16)) in (let H18 \def (f_equal C C (\lambda (e0: C).(match 
e0 in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c1 _ 
_) \Rightarrow c1])) (CHead d (Bind Abbr) u) (CHead e (Bind Abbr) u0) 
(getl_mono c0 (CHead d (Bind Abbr) u) i H0 (CHead e (Bind Abbr) u0) H16)) in 
((let H19 \def (f_equal C T (\lambda (e0: C).(match e0 in C return (\lambda 
(_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) 
(CHead d (Bind Abbr) u) (CHead e (Bind Abbr) u0) (getl_mono c0 (CHead d (Bind 
Abbr) u) i H0 (CHead e (Bind Abbr) u0) H16)) in (\lambda (H20: (eq C d 
e)).(let H21 \def (eq_ind_r T u0 (\lambda (t0: T).(getl i c0 (CHead e (Bind 
Abbr) t0))) H17 u H19) in (let H22 \def (eq_ind_r T u0 (\lambda (t0: 
T).(subst1 i t0 t4 (lift (S O) i x0))) H13 u H19) in (let H23 \def (eq_ind_r 
T u0 (\lambda (t0: T).(csubst1 i t0 c0 a0)) H15 u H19) in (eq_ind T u 
(\lambda (t0: T).(ex2 T (\lambda (x2: T).(subst1 i t0 t (lift (S O) i x2))) 
(\lambda (x2: T).(pr2 a x1 x2)))) (let H24 \def (eq_ind_r C e (\lambda (c1: 
C).(getl i c0 (CHead c1 (Bind Abbr) u))) H21 d H20) in (ex2_ind T (\lambda 
(t0: T).(subst1 i u t t0)) (\lambda (t0: T).(subst1 i u (lift (S O) i x0) 
t0)) (ex2 T (\lambda (x2: T).(subst1 i u t (lift (S O) i x2))) (\lambda (x2: 
T).(pr2 a x1 x2))) (\lambda (x2: T).(\lambda (H25: (subst1 i u t 
x2)).(\lambda (H26: (subst1 i u (lift (S O) i x0) x2)).(let H27 \def (eq_ind 
T x2 (\lambda (t0: T).(subst1 i u t t0)) H25 (lift (S O) i x0) 
(subst1_gen_lift_eq x0 u x2 (S O) i i (le_n i) (eq_ind_r nat (plus (S O) i) 
(\lambda (n: nat).(lt i n)) (le_n (plus (S O) i)) (plus i (S O)) (plus_sym i 
(S O))) H26)) in (ex_intro2 T (\lambda (x3: T).(subst1 i u t (lift (S O) i 
x3))) (\lambda (x3: T).(pr2 a x1 x3)) x0 H27 (pr2_free a x1 x0 H10)))))) 
(subst1_confluence_eq t4 t u i (subst1_single i u t4 t H2) (lift (S O) i x0) 
H22))) u0 H19)))))) H18))) d0 H12)))))) (\lambda (H12: (lt d0 i)).(ex2_ind T 
(\lambda (t0: T).(subst1 d0 u0 t t0)) (\lambda (t0: T).(subst1 i u (lift (S 
O) d0 x0) t0)) (ex2 T (\lambda (x2: T).(subst1 d0 u0 t (lift (S O) d0 x2))) 
(\lambda (x2: T).(pr2 a x1 x2))) (\lambda (x2: T).(\lambda (H13: (subst1 d0 
u0 t x2)).(\lambda (H14: (subst1 i u (lift (S O) d0 x0) x2)).(ex2_ind T 
(\lambda (t5: T).(eq T x2 (lift (S O) d0 t5))) (\lambda (t5: T).(subst1 
(minus i (S O)) u x0 t5)) (ex2 T (\lambda (x3: T).(subst1 d0 u0 t (lift (S O) 
d0 x3))) (\lambda (x3: T).(pr2 a x1 x3))) (\lambda (x3: T).(\lambda (H15: (eq 
T x2 (lift (S O) d0 x3))).(\lambda (H16: (subst1 (minus i (S O)) u x0 
x3)).(let H17 \def (eq_ind T x2 (\lambda (t0: T).(subst1 d0 u0 t t0)) H13 
(lift (S O) d0 x3) H15) in (ex_intro2 T (\lambda (x4: T).(subst1 d0 u0 t 
(lift (S O) d0 x4))) (\lambda (x4: T).(pr2 a x1 x4)) x3 H17 (pr2_delta1 a d u 
(minus i (S O)) (getl_drop_conf_ge i (CHead d (Bind Abbr) u) a0 
(csubst1_getl_ge d0 i (le_S_n d0 i (le_S (S d0) i H12)) c0 a0 u0 H4 (CHead d 
(Bind Abbr) u) H0) a (S O) d0 H5 (eq_ind_r nat (plus (S O) d0) (\lambda (n: 
nat).(le n i)) H12 (plus d0 (S O)) (plus_sym d0 (S O)))) x1 x0 H10 x3 
H16)))))) (subst1_gen_lift_ge u x0 x2 i (S O) d0 H14 (eq_ind_r nat (plus (S 
O) d0) (\lambda (n: nat).(le n i)) H12 (plus d0 (S O)) (plus_sym d0 (S 
O)))))))) (subst1_confluence_neq t4 t u i (subst1_single i u t4 t H2) (lift 
(S O) d0 x0) u0 d0 H11 (sym_not_eq nat d0 i (lt_neq d0 i H12)))))))))) 
(pr0_gen_lift x1 x (S O) d0 H7))))) (pr0_subst1 t3 t4 H1 u0 (lift (S O) d0 
x1) d0 H6 u0 (pr0_refl u0))))))))))))))))))))))) c t1 t2 H)))).
(* COMMENTS
Initial nodes: 3757
END *)

