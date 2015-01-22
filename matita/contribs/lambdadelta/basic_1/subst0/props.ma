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

include "Basic-1/subst0/fwd.ma".

theorem subst0_refl:
 \forall (u: T).(\forall (t: T).(\forall (d: nat).((subst0 d u t t) \to 
(\forall (P: Prop).P))))
\def
 \lambda (u: T).(\lambda (t: T).(T_ind (\lambda (t0: T).(\forall (d: 
nat).((subst0 d u t0 t0) \to (\forall (P: Prop).P)))) (\lambda (n: 
nat).(\lambda (d: nat).(\lambda (H: (subst0 d u (TSort n) (TSort 
n))).(\lambda (P: Prop).(subst0_gen_sort u (TSort n) d n H P))))) (\lambda 
(n: nat).(\lambda (d: nat).(\lambda (H: (subst0 d u (TLRef n) (TLRef 
n))).(\lambda (P: Prop).(land_ind (eq nat n d) (eq T (TLRef n) (lift (S n) O 
u)) P (\lambda (_: (eq nat n d)).(\lambda (H1: (eq T (TLRef n) (lift (S n) O 
u))).(lift_gen_lref_false (S n) O n (le_O_n n) (le_n (plus O (S n))) u H1 
P))) (subst0_gen_lref u (TLRef n) d n H)))))) (\lambda (k: K).(\lambda (t0: 
T).(\lambda (H: ((\forall (d: nat).((subst0 d u t0 t0) \to (\forall (P: 
Prop).P))))).(\lambda (t1: T).(\lambda (H0: ((\forall (d: nat).((subst0 d u 
t1 t1) \to (\forall (P: Prop).P))))).(\lambda (d: nat).(\lambda (H1: (subst0 
d u (THead k t0 t1) (THead k t0 t1))).(\lambda (P: Prop).(or3_ind (ex2 T 
(\lambda (u2: T).(eq T (THead k t0 t1) (THead k u2 t1))) (\lambda (u2: 
T).(subst0 d u t0 u2))) (ex2 T (\lambda (t2: T).(eq T (THead k t0 t1) (THead 
k t0 t2))) (\lambda (t2: T).(subst0 (s k d) u t1 t2))) (ex3_2 T T (\lambda 
(u2: T).(\lambda (t2: T).(eq T (THead k t0 t1) (THead k u2 t2)))) (\lambda 
(u2: T).(\lambda (_: T).(subst0 d u t0 u2))) (\lambda (_: T).(\lambda (t2: 
T).(subst0 (s k d) u t1 t2)))) P (\lambda (H2: (ex2 T (\lambda (u2: T).(eq T 
(THead k t0 t1) (THead k u2 t1))) (\lambda (u2: T).(subst0 d u t0 
u2)))).(ex2_ind T (\lambda (u2: T).(eq T (THead k t0 t1) (THead k u2 t1))) 
(\lambda (u2: T).(subst0 d u t0 u2)) P (\lambda (x: T).(\lambda (H3: (eq T 
(THead k t0 t1) (THead k x t1))).(\lambda (H4: (subst0 d u t0 x)).(let H5 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead _ t2 _) 
\Rightarrow t2])) (THead k t0 t1) (THead k x t1) H3) in (let H6 \def 
(eq_ind_r T x (\lambda (t2: T).(subst0 d u t0 t2)) H4 t0 H5) in (H d H6 
P)))))) H2)) (\lambda (H2: (ex2 T (\lambda (t2: T).(eq T (THead k t0 t1) 
(THead k t0 t2))) (\lambda (t2: T).(subst0 (s k d) u t1 t2)))).(ex2_ind T 
(\lambda (t2: T).(eq T (THead k t0 t1) (THead k t0 t2))) (\lambda (t2: 
T).(subst0 (s k d) u t1 t2)) P (\lambda (x: T).(\lambda (H3: (eq T (THead k 
t0 t1) (THead k t0 x))).(\lambda (H4: (subst0 (s k d) u t1 x)).(let H5 \def 
(f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) with 
[(TSort _) \Rightarrow t1 | (TLRef _) \Rightarrow t1 | (THead _ _ t2) 
\Rightarrow t2])) (THead k t0 t1) (THead k t0 x) H3) in (let H6 \def 
(eq_ind_r T x (\lambda (t2: T).(subst0 (s k d) u t1 t2)) H4 t1 H5) in (H0 (s 
k d) H6 P)))))) H2)) (\lambda (H2: (ex3_2 T T (\lambda (u2: T).(\lambda (t2: 
T).(eq T (THead k t0 t1) (THead k u2 t2)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 d u t0 u2))) (\lambda (_: T).(\lambda (t2: T).(subst0 (s k d) u t1 
t2))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t2: T).(eq T (THead k t0 
t1) (THead k u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(subst0 d u t0 u2))) 
(\lambda (_: T).(\lambda (t2: T).(subst0 (s k d) u t1 t2))) P (\lambda (x0: 
T).(\lambda (x1: T).(\lambda (H3: (eq T (THead k t0 t1) (THead k x0 
x1))).(\lambda (H4: (subst0 d u t0 x0)).(\lambda (H5: (subst0 (s k d) u t1 
x1)).(let H6 \def (f_equal T T (\lambda (e: T).(match e in T return (\lambda 
(_: T).T) with [(TSort _) \Rightarrow t0 | (TLRef _) \Rightarrow t0 | (THead 
_ t2 _) \Rightarrow t2])) (THead k t0 t1) (THead k x0 x1) H3) in ((let H7 
\def (f_equal T T (\lambda (e: T).(match e in T return (\lambda (_: T).T) 
with [(TSort _) \Rightarrow t1 | (TLRef _) \Rightarrow t1 | (THead _ _ t2) 
\Rightarrow t2])) (THead k t0 t1) (THead k x0 x1) H3) in (\lambda (H8: (eq T 
t0 x0)).(let H9 \def (eq_ind_r T x1 (\lambda (t2: T).(subst0 (s k d) u t1 
t2)) H5 t1 H7) in (let H10 \def (eq_ind_r T x0 (\lambda (t2: T).(subst0 d u 
t0 t2)) H4 t0 H8) in (H d H10 P))))) H6))))))) H2)) (subst0_gen_head k u t0 
t1 (THead k t0 t1) d H1)))))))))) t)).
(* COMMENTS
Initial nodes: 1119
END *)

theorem subst0_lift_lt:
 \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).((subst0 
i u t1 t2) \to (\forall (d: nat).((lt i d) \to (\forall (h: nat).(subst0 i 
(lift h (minus d (S i)) u) (lift h d t1) (lift h d t2)))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (subst0 i u t1 t2)).(subst0_ind (\lambda (n: nat).(\lambda (t: 
T).(\lambda (t0: T).(\lambda (t3: T).(\forall (d: nat).((lt n d) \to (\forall 
(h: nat).(subst0 n (lift h (minus d (S n)) t) (lift h d t0) (lift h d 
t3))))))))) (\lambda (v: T).(\lambda (i0: nat).(\lambda (d: nat).(\lambda 
(H0: (lt i0 d)).(\lambda (h: nat).(eq_ind_r T (TLRef i0) (\lambda (t: 
T).(subst0 i0 (lift h (minus d (S i0)) v) t (lift h d (lift (S i0) O v)))) 
(let w \def (minus d (S i0)) in (eq_ind nat (plus (S i0) (minus d (S i0))) 
(\lambda (n: nat).(subst0 i0 (lift h w v) (TLRef i0) (lift h n (lift (S i0) O 
v)))) (eq_ind_r T (lift (S i0) O (lift h (minus d (S i0)) v)) (\lambda (t: 
T).(subst0 i0 (lift h w v) (TLRef i0) t)) (subst0_lref (lift h (minus d (S 
i0)) v) i0) (lift h (plus (S i0) (minus d (S i0))) (lift (S i0) O v)) (lift_d 
v h (S i0) (minus d (S i0)) O (le_O_n (minus d (S i0))))) d (le_plus_minus_r 
(S i0) d H0))) (lift h d (TLRef i0)) (lift_lref_lt i0 h d H0))))))) (\lambda 
(v: T).(\lambda (u2: T).(\lambda (u1: T).(\lambda (i0: nat).(\lambda (_: 
(subst0 i0 v u1 u2)).(\lambda (H1: ((\forall (d: nat).((lt i0 d) \to (\forall 
(h: nat).(subst0 i0 (lift h (minus d (S i0)) v) (lift h d u1) (lift h d 
u2))))))).(\lambda (t: T).(\lambda (k: K).(\lambda (d: nat).(\lambda (H2: (lt 
i0 d)).(\lambda (h: nat).(eq_ind_r T (THead k (lift h d u1) (lift h (s k d) 
t)) (\lambda (t0: T).(subst0 i0 (lift h (minus d (S i0)) v) t0 (lift h d 
(THead k u2 t)))) (eq_ind_r T (THead k (lift h d u2) (lift h (s k d) t)) 
(\lambda (t0: T).(subst0 i0 (lift h (minus d (S i0)) v) (THead k (lift h d 
u1) (lift h (s k d) t)) t0)) (subst0_fst (lift h (minus d (S i0)) v) (lift h 
d u2) (lift h d u1) i0 (H1 d H2 h) (lift h (s k d) t) k) (lift h d (THead k 
u2 t)) (lift_head k u2 t h d)) (lift h d (THead k u1 t)) (lift_head k u1 t h 
d))))))))))))) (\lambda (k: K).(\lambda (v: T).(\lambda (t0: T).(\lambda (t3: 
T).(\lambda (i0: nat).(\lambda (_: (subst0 (s k i0) v t3 t0)).(\lambda (H1: 
((\forall (d: nat).((lt (s k i0) d) \to (\forall (h: nat).(subst0 (s k i0) 
(lift h (minus d (S (s k i0))) v) (lift h d t3) (lift h d t0))))))).(\lambda 
(u0: T).(\lambda (d: nat).(\lambda (H2: (lt i0 d)).(\lambda (h: nat).(let H3 
\def (eq_ind_r nat (S (s k i0)) (\lambda (n: nat).(\forall (d0: nat).((lt (s 
k i0) d0) \to (\forall (h0: nat).(subst0 (s k i0) (lift h0 (minus d0 n) v) 
(lift h0 d0 t3) (lift h0 d0 t0)))))) H1 (s k (S i0)) (s_S k i0)) in (eq_ind_r 
T (THead k (lift h d u0) (lift h (s k d) t3)) (\lambda (t: T).(subst0 i0 
(lift h (minus d (S i0)) v) t (lift h d (THead k u0 t0)))) (eq_ind_r T (THead 
k (lift h d u0) (lift h (s k d) t0)) (\lambda (t: T).(subst0 i0 (lift h 
(minus d (S i0)) v) (THead k (lift h d u0) (lift h (s k d) t3)) t)) (eq_ind 
nat (minus (s k d) (s k (S i0))) (\lambda (n: nat).(subst0 i0 (lift h n v) 
(THead k (lift h d u0) (lift h (s k d) t3)) (THead k (lift h d u0) (lift h (s 
k d) t0)))) (subst0_snd k (lift h (minus (s k d) (s k (S i0))) v) (lift h (s 
k d) t0) (lift h (s k d) t3) i0 (H3 (s k d) (s_lt k i0 d H2) h) (lift h d 
u0)) (minus d (S i0)) (minus_s_s k d (S i0))) (lift h d (THead k u0 t0)) 
(lift_head k u0 t0 h d)) (lift h d (THead k u0 t3)) (lift_head k u0 t3 h 
d)))))))))))))) (\lambda (v: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda 
(i0: nat).(\lambda (_: (subst0 i0 v u1 u2)).(\lambda (H1: ((\forall (d: 
nat).((lt i0 d) \to (\forall (h: nat).(subst0 i0 (lift h (minus d (S i0)) v) 
(lift h d u1) (lift h d u2))))))).(\lambda (k: K).(\lambda (t0: T).(\lambda 
(t3: T).(\lambda (_: (subst0 (s k i0) v t0 t3)).(\lambda (H3: ((\forall (d: 
nat).((lt (s k i0) d) \to (\forall (h: nat).(subst0 (s k i0) (lift h (minus d 
(S (s k i0))) v) (lift h d t0) (lift h d t3))))))).(\lambda (d: nat).(\lambda 
(H4: (lt i0 d)).(\lambda (h: nat).(let H5 \def (eq_ind_r nat (S (s k i0)) 
(\lambda (n: nat).(\forall (d0: nat).((lt (s k i0) d0) \to (\forall (h0: 
nat).(subst0 (s k i0) (lift h0 (minus d0 n) v) (lift h0 d0 t0) (lift h0 d0 
t3)))))) H3 (s k (S i0)) (s_S k i0)) in (eq_ind_r T (THead k (lift h d u1) 
(lift h (s k d) t0)) (\lambda (t: T).(subst0 i0 (lift h (minus d (S i0)) v) t 
(lift h d (THead k u2 t3)))) (eq_ind_r T (THead k (lift h d u2) (lift h (s k 
d) t3)) (\lambda (t: T).(subst0 i0 (lift h (minus d (S i0)) v) (THead k (lift 
h d u1) (lift h (s k d) t0)) t)) (subst0_both (lift h (minus d (S i0)) v) 
(lift h d u1) (lift h d u2) i0 (H1 d H4 h) k (lift h (s k d) t0) (lift h (s k 
d) t3) (eq_ind nat (minus (s k d) (s k (S i0))) (\lambda (n: nat).(subst0 (s 
k i0) (lift h n v) (lift h (s k d) t0) (lift h (s k d) t3))) (H5 (s k d) 
(s_lt k i0 d H4) h) (minus d (S i0)) (minus_s_s k d (S i0)))) (lift h d 
(THead k u2 t3)) (lift_head k u2 t3 h d)) (lift h d (THead k u1 t0)) 
(lift_head k u1 t0 h d))))))))))))))))) i u t1 t2 H))))).
(* COMMENTS
Initial nodes: 1805
END *)

theorem subst0_lift_ge:
 \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).(\forall 
(h: nat).((subst0 i u t1 t2) \to (\forall (d: nat).((le d i) \to (subst0 
(plus i h) u (lift h d t1) (lift h d t2)))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(h: nat).(\lambda (H: (subst0 i u t1 t2)).(subst0_ind (\lambda (n: 
nat).(\lambda (t: T).(\lambda (t0: T).(\lambda (t3: T).(\forall (d: nat).((le 
d n) \to (subst0 (plus n h) t (lift h d t0) (lift h d t3)))))))) (\lambda (v: 
T).(\lambda (i0: nat).(\lambda (d: nat).(\lambda (H0: (le d i0)).(eq_ind_r T 
(TLRef (plus i0 h)) (\lambda (t: T).(subst0 (plus i0 h) v t (lift h d (lift 
(S i0) O v)))) (eq_ind_r T (lift (plus h (S i0)) O v) (\lambda (t: T).(subst0 
(plus i0 h) v (TLRef (plus i0 h)) t)) (eq_ind nat (S (plus h i0)) (\lambda 
(n: nat).(subst0 (plus i0 h) v (TLRef (plus i0 h)) (lift n O v))) (eq_ind_r 
nat (plus h i0) (\lambda (n: nat).(subst0 n v (TLRef n) (lift (S (plus h i0)) 
O v))) (subst0_lref v (plus h i0)) (plus i0 h) (plus_sym i0 h)) (plus h (S 
i0)) (plus_n_Sm h i0)) (lift h d (lift (S i0) O v)) (lift_free v (S i0) h O d 
(le_S d i0 H0) (le_O_n d))) (lift h d (TLRef i0)) (lift_lref_ge i0 h d 
H0)))))) (\lambda (v: T).(\lambda (u2: T).(\lambda (u1: T).(\lambda (i0: 
nat).(\lambda (_: (subst0 i0 v u1 u2)).(\lambda (H1: ((\forall (d: nat).((le 
d i0) \to (subst0 (plus i0 h) v (lift h d u1) (lift h d u2)))))).(\lambda (t: 
T).(\lambda (k: K).(\lambda (d: nat).(\lambda (H2: (le d i0)).(eq_ind_r T 
(THead k (lift h d u1) (lift h (s k d) t)) (\lambda (t0: T).(subst0 (plus i0 
h) v t0 (lift h d (THead k u2 t)))) (eq_ind_r T (THead k (lift h d u2) (lift 
h (s k d) t)) (\lambda (t0: T).(subst0 (plus i0 h) v (THead k (lift h d u1) 
(lift h (s k d) t)) t0)) (subst0_fst v (lift h d u2) (lift h d u1) (plus i0 
h) (H1 d H2) (lift h (s k d) t) k) (lift h d (THead k u2 t)) (lift_head k u2 
t h d)) (lift h d (THead k u1 t)) (lift_head k u1 t h d)))))))))))) (\lambda 
(k: K).(\lambda (v: T).(\lambda (t0: T).(\lambda (t3: T).(\lambda (i0: 
nat).(\lambda (_: (subst0 (s k i0) v t3 t0)).(\lambda (H1: ((\forall (d: 
nat).((le d (s k i0)) \to (subst0 (plus (s k i0) h) v (lift h d t3) (lift h d 
t0)))))).(\lambda (u0: T).(\lambda (d: nat).(\lambda (H2: (le d i0)).(let H3 
\def (eq_ind_r nat (plus (s k i0) h) (\lambda (n: nat).(\forall (d0: 
nat).((le d0 (s k i0)) \to (subst0 n v (lift h d0 t3) (lift h d0 t0))))) H1 
(s k (plus i0 h)) (s_plus k i0 h)) in (eq_ind_r T (THead k (lift h d u0) 
(lift h (s k d) t3)) (\lambda (t: T).(subst0 (plus i0 h) v t (lift h d (THead 
k u0 t0)))) (eq_ind_r T (THead k (lift h d u0) (lift h (s k d) t0)) (\lambda 
(t: T).(subst0 (plus i0 h) v (THead k (lift h d u0) (lift h (s k d) t3)) t)) 
(subst0_snd k v (lift h (s k d) t0) (lift h (s k d) t3) (plus i0 h) (H3 (s k 
d) (s_le k d i0 H2)) (lift h d u0)) (lift h d (THead k u0 t0)) (lift_head k 
u0 t0 h d)) (lift h d (THead k u0 t3)) (lift_head k u0 t3 h d))))))))))))) 
(\lambda (v: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (i0: nat).(\lambda 
(_: (subst0 i0 v u1 u2)).(\lambda (H1: ((\forall (d: nat).((le d i0) \to 
(subst0 (plus i0 h) v (lift h d u1) (lift h d u2)))))).(\lambda (k: 
K).(\lambda (t0: T).(\lambda (t3: T).(\lambda (_: (subst0 (s k i0) v t0 
t3)).(\lambda (H3: ((\forall (d: nat).((le d (s k i0)) \to (subst0 (plus (s k 
i0) h) v (lift h d t0) (lift h d t3)))))).(\lambda (d: nat).(\lambda (H4: (le 
d i0)).(let H5 \def (eq_ind_r nat (plus (s k i0) h) (\lambda (n: 
nat).(\forall (d0: nat).((le d0 (s k i0)) \to (subst0 n v (lift h d0 t0) 
(lift h d0 t3))))) H3 (s k (plus i0 h)) (s_plus k i0 h)) in (eq_ind_r T 
(THead k (lift h d u1) (lift h (s k d) t0)) (\lambda (t: T).(subst0 (plus i0 
h) v t (lift h d (THead k u2 t3)))) (eq_ind_r T (THead k (lift h d u2) (lift 
h (s k d) t3)) (\lambda (t: T).(subst0 (plus i0 h) v (THead k (lift h d u1) 
(lift h (s k d) t0)) t)) (subst0_both v (lift h d u1) (lift h d u2) (plus i0 
h) (H1 d H4) k (lift h (s k d) t0) (lift h (s k d) t3) (H5 (s k d) (s_le k d 
i0 H4))) (lift h d (THead k u2 t3)) (lift_head k u2 t3 h d)) (lift h d (THead 
k u1 t0)) (lift_head k u1 t0 h d)))))))))))))))) i u t1 t2 H)))))).
(* COMMENTS
Initial nodes: 1449
END *)

theorem subst0_lift_ge_S:
 \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).((subst0 
i u t1 t2) \to (\forall (d: nat).((le d i) \to (subst0 (S i) u (lift (S O) d 
t1) (lift (S O) d t2))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (subst0 i u t1 t2)).(\lambda (d: nat).(\lambda (H0: (le d i)).(eq_ind nat 
(plus i (S O)) (\lambda (n: nat).(subst0 n u (lift (S O) d t1) (lift (S O) d 
t2))) (subst0_lift_ge t1 t2 u i (S O) H d H0) (S i) (eq_ind_r nat (plus (S O) 
i) (\lambda (n: nat).(eq nat n (S i))) (refl_equal nat (S i)) (plus i (S O)) 
(plus_sym i (S O)))))))))).
(* COMMENTS
Initial nodes: 137
END *)

theorem subst0_lift_ge_s:
 \forall (t1: T).(\forall (t2: T).(\forall (u: T).(\forall (i: nat).((subst0 
i u t1 t2) \to (\forall (d: nat).((le d i) \to (\forall (b: B).(subst0 (s 
(Bind b) i) u (lift (S O) d t1) (lift (S O) d t2)))))))))
\def
 \lambda (t1: T).(\lambda (t2: T).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H: (subst0 i u t1 t2)).(\lambda (d: nat).(\lambda (H0: (le d i)).(\lambda 
(_: B).(subst0_lift_ge_S t1 t2 u i H d H0)))))))).
(* COMMENTS
Initial nodes: 43
END *)

