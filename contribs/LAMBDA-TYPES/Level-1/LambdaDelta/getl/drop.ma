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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/getl/drop".

include "getl/props.ma".

include "clear/drop.ma".

include "r/props.ma".

theorem getl_drop:
 \forall (b: B).(\forall (c: C).(\forall (e: C).(\forall (u: T).(\forall (h: 
nat).((getl h c (CHead e (Bind b) u)) \to (drop (S h) O c e))))))
\def
 \lambda (b: B).(\lambda (c: C).(C_ind (\lambda (c0: C).(\forall (e: 
C).(\forall (u: T).(\forall (h: nat).((getl h c0 (CHead e (Bind b) u)) \to 
(drop (S h) O c0 e)))))) (\lambda (n: nat).(\lambda (e: C).(\lambda (u: 
T).(\lambda (h: nat).(\lambda (H: (getl h (CSort n) (CHead e (Bind b) 
u))).(getl_gen_sort n h (CHead e (Bind b) u) H (drop (S h) O (CSort n) 
e))))))) (\lambda (c0: C).(\lambda (H: ((\forall (e: C).(\forall (u: 
T).(\forall (h: nat).((getl h c0 (CHead e (Bind b) u)) \to (drop (S h) O c0 
e))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (e: C).(\lambda (u: 
T).(\lambda (h: nat).(nat_ind (\lambda (n: nat).((getl n (CHead c0 k t) 
(CHead e (Bind b) u)) \to (drop (S n) O (CHead c0 k t) e))) (\lambda (H0: 
(getl O (CHead c0 k t) (CHead e (Bind b) u))).(K_ind (\lambda (k0: K).((clear 
(CHead c0 k0 t) (CHead e (Bind b) u)) \to (drop (S O) O (CHead c0 k0 t) e))) 
(\lambda (b0: B).(\lambda (H1: (clear (CHead c0 (Bind b0) t) (CHead e (Bind 
b) u))).(let H2 \def (f_equal C C (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow e | (CHead c _ _) \Rightarrow 
c])) (CHead e (Bind b) u) (CHead c0 (Bind b0) t) (clear_gen_bind b0 c0 (CHead 
e (Bind b) u) t H1)) in ((let H3 \def (f_equal C B (\lambda (e0: C).(match e0 
in C return (\lambda (_: C).B) with [(CSort _) \Rightarrow b | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b) 
\Rightarrow b | (Flat _) \Rightarrow b])])) (CHead e (Bind b) u) (CHead c0 
(Bind b0) t) (clear_gen_bind b0 c0 (CHead e (Bind b) u) t H1)) in ((let H4 
\def (f_equal C T (\lambda (e0: C).(match e0 in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead e (Bind 
b) u) (CHead c0 (Bind b0) t) (clear_gen_bind b0 c0 (CHead e (Bind b) u) t 
H1)) in (\lambda (H5: (eq B b b0)).(\lambda (H6: (eq C e c0)).(eq_ind_r C c0 
(\lambda (c1: C).(drop (S O) O (CHead c0 (Bind b0) t) c1)) (eq_ind B b 
(\lambda (b1: B).(drop (S O) O (CHead c0 (Bind b1) t) c0)) (drop_drop (Bind 
b) O c0 c0 (drop_refl c0) t) b0 H5) e H6)))) H3)) H2)))) (\lambda (f: 
F).(\lambda (H1: (clear (CHead c0 (Flat f) t) (CHead e (Bind b) 
u))).(drop_clear_O b (CHead c0 (Flat f) t) e u (clear_flat c0 (CHead e (Bind 
b) u) (clear_gen_flat f c0 (CHead e (Bind b) u) t H1) f t) e O (drop_refl 
e)))) k (getl_gen_O (CHead c0 k t) (CHead e (Bind b) u) H0))) (\lambda (n: 
nat).(\lambda (_: (((getl n (CHead c0 k t) (CHead e (Bind b) u)) \to (drop (S 
n) O (CHead c0 k t) e)))).(\lambda (H1: (getl (S n) (CHead c0 k t) (CHead e 
(Bind b) u))).(drop_drop k (S n) c0 e (eq_ind_r nat (S (r k n)) (\lambda (n0: 
nat).(drop n0 O c0 e)) (H e u (r k n) (getl_gen_S k c0 (CHead e (Bind b) u) t 
n H1)) (r k (S n)) (r_S k n)) t)))) h)))))))) c)).

theorem getl_drop_conf_lt:
 \forall (b: B).(\forall (c: C).(\forall (c0: C).(\forall (u: T).(\forall (i: 
nat).((getl i c (CHead c0 (Bind b) u)) \to (\forall (e: C).(\forall (h: 
nat).(\forall (d: nat).((drop h (S (plus i d)) c e) \to (ex3_2 T C (\lambda 
(v: T).(\lambda (_: C).(eq T u (lift h d v)))) (\lambda (v: T).(\lambda (e0: 
C).(getl i e (CHead e0 (Bind b) v)))) (\lambda (_: T).(\lambda (e0: C).(drop 
h d c0 e0)))))))))))))
\def
 \lambda (b: B).(\lambda (c: C).(C_ind (\lambda (c0: C).(\forall (c1: 
C).(\forall (u: T).(\forall (i: nat).((getl i c0 (CHead c1 (Bind b) u)) \to 
(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h (S (plus i d)) 
c0 e) \to (ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h d v)))) 
(\lambda (v: T).(\lambda (e0: C).(getl i e (CHead e0 (Bind b) v)))) (\lambda 
(_: T).(\lambda (e0: C).(drop h d c1 e0))))))))))))) (\lambda (n: 
nat).(\lambda (c0: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H: (getl i 
(CSort n) (CHead c0 (Bind b) u))).(\lambda (e: C).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (_: (drop h (S (plus i d)) (CSort n) e)).(getl_gen_sort n i 
(CHead c0 (Bind b) u) H (ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u 
(lift h d v)))) (\lambda (v: T).(\lambda (e0: C).(getl i e (CHead e0 (Bind b) 
v)))) (\lambda (_: T).(\lambda (e0: C).(drop h d c0 e0)))))))))))))) (\lambda 
(c0: C).(\lambda (H: ((\forall (c1: C).(\forall (u: T).(\forall (i: 
nat).((getl i c0 (CHead c1 (Bind b) u)) \to (\forall (e: C).(\forall (h: 
nat).(\forall (d: nat).((drop h (S (plus i d)) c0 e) \to (ex3_2 T C (\lambda 
(v: T).(\lambda (_: C).(eq T u (lift h d v)))) (\lambda (v: T).(\lambda (e0: 
C).(getl i e (CHead e0 (Bind b) v)))) (\lambda (_: T).(\lambda (e0: C).(drop 
h d c1 e0)))))))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c1: 
C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i (CHead c0 k t) 
(CHead c1 (Bind b) u))).(\lambda (e: C).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H1: (drop h (S (plus i d)) (CHead c0 k t) e)).(let H2 \def 
(getl_gen_all (CHead c0 k t) (CHead c1 (Bind b) u) i H0) in (ex2_ind C 
(\lambda (e0: C).(drop i O (CHead c0 k t) e0)) (\lambda (e0: C).(clear e0 
(CHead c1 (Bind b) u))) (ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u 
(lift h d v)))) (\lambda (v: T).(\lambda (e0: C).(getl i e (CHead e0 (Bind b) 
v)))) (\lambda (_: T).(\lambda (e0: C).(drop h d c1 e0)))) (\lambda (x: 
C).(\lambda (H3: (drop i O (CHead c0 k t) x)).(\lambda (H4: (clear x (CHead 
c1 (Bind b) u))).((match x in C return (\lambda (c2: C).((drop i O (CHead c0 
k t) c2) \to ((clear c2 (CHead c1 (Bind b) u)) \to (ex3_2 T C (\lambda (v: 
T).(\lambda (_: C).(eq T u (lift h d v)))) (\lambda (v: T).(\lambda (e0: 
C).(getl i e (CHead e0 (Bind b) v)))) (\lambda (_: T).(\lambda (e0: C).(drop 
h d c1 e0))))))) with [(CSort n) \Rightarrow (\lambda (_: (drop i O (CHead c0 
k t) (CSort n))).(\lambda (H6: (clear (CSort n) (CHead c1 (Bind b) 
u))).(clear_gen_sort (CHead c1 (Bind b) u) n H6 (ex3_2 T C (\lambda (v: 
T).(\lambda (_: C).(eq T u (lift h d v)))) (\lambda (v: T).(\lambda (e0: 
C).(getl i e (CHead e0 (Bind b) v)))) (\lambda (_: T).(\lambda (e0: C).(drop 
h d c1 e0))))))) | (CHead c2 k0 t0) \Rightarrow (\lambda (H5: (drop i O 
(CHead c0 k t) (CHead c2 k0 t0))).(\lambda (H6: (clear (CHead c2 k0 t0) 
(CHead c1 (Bind b) u))).((match k0 in K return (\lambda (k1: K).((drop i O 
(CHead c0 k t) (CHead c2 k1 t0)) \to ((clear (CHead c2 k1 t0) (CHead c1 (Bind 
b) u)) \to (ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h d v)))) 
(\lambda (v: T).(\lambda (e0: C).(getl i e (CHead e0 (Bind b) v)))) (\lambda 
(_: T).(\lambda (e0: C).(drop h d c1 e0))))))) with [(Bind b0) \Rightarrow 
(\lambda (H7: (drop i O (CHead c0 k t) (CHead c2 (Bind b0) t0))).(\lambda 
(H8: (clear (CHead c2 (Bind b0) t0) (CHead c1 (Bind b) u))).(let H9 \def 
(f_equal C C (\lambda (e0: C).(match e0 in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) (CHead c1 (Bind b) 
u) (CHead c2 (Bind b0) t0) (clear_gen_bind b0 c2 (CHead c1 (Bind b) u) t0 
H8)) in ((let H10 \def (f_equal C B (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).B) with [(CSort _) \Rightarrow b | (CHead _ k _) \Rightarrow 
(match k in K return (\lambda (_: K).B) with [(Bind b) \Rightarrow b | (Flat 
_) \Rightarrow b])])) (CHead c1 (Bind b) u) (CHead c2 (Bind b0) t0) 
(clear_gen_bind b0 c2 (CHead c1 (Bind b) u) t0 H8)) in ((let H11 \def 
(f_equal C T (\lambda (e0: C).(match e0 in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead c1 (Bind b) 
u) (CHead c2 (Bind b0) t0) (clear_gen_bind b0 c2 (CHead c1 (Bind b) u) t0 
H8)) in (\lambda (H12: (eq B b b0)).(\lambda (H13: (eq C c1 c2)).(let H14 
\def (eq_ind_r T t0 (\lambda (t0: T).(drop i O (CHead c0 k t) (CHead c2 (Bind 
b0) t0))) H7 u H11) in (let H15 \def (eq_ind_r B b0 (\lambda (b: B).(drop i O 
(CHead c0 k t) (CHead c2 (Bind b) u))) H14 b H12) in (let H16 \def (eq_ind_r 
C c2 (\lambda (c: C).(drop i O (CHead c0 k t) (CHead c (Bind b) u))) H15 c1 
H13) in (ex3_2_ind T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h (r 
(Bind b) d) v)))) (\lambda (v: T).(\lambda (e0: C).(drop i O e (CHead e0 
(Bind b) v)))) (\lambda (_: T).(\lambda (e0: C).(drop h (r (Bind b) d) c1 
e0))) (ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h d v)))) 
(\lambda (v: T).(\lambda (e0: C).(getl i e (CHead e0 (Bind b) v)))) (\lambda 
(_: T).(\lambda (e0: C).(drop h d c1 e0)))) (\lambda (x0: T).(\lambda (x1: 
C).(\lambda (H17: (eq T u (lift h (r (Bind b) d) x0))).(\lambda (H18: (drop i 
O e (CHead x1 (Bind b) x0))).(\lambda (H19: (drop h (r (Bind b) d) c1 
x1)).(eq_ind_r T (lift h (r (Bind b) d) x0) (\lambda (t1: T).(ex3_2 T C 
(\lambda (v: T).(\lambda (_: C).(eq T t1 (lift h d v)))) (\lambda (v: 
T).(\lambda (e0: C).(getl i e (CHead e0 (Bind b) v)))) (\lambda (_: 
T).(\lambda (e0: C).(drop h d c1 e0))))) (ex3_2_intro T C (\lambda (v: 
T).(\lambda (_: C).(eq T (lift h (r (Bind b) d) x0) (lift h d v)))) (\lambda 
(v: T).(\lambda (e0: C).(getl i e (CHead e0 (Bind b) v)))) (\lambda (_: 
T).(\lambda (e0: C).(drop h d c1 e0))) x0 x1 (refl_equal T (lift h d x0)) 
(getl_intro i e (CHead x1 (Bind b) x0) (CHead x1 (Bind b) x0) H18 (clear_bind 
b x1 x0)) H19) u H17)))))) (drop_conf_lt (Bind b) i u c1 (CHead c0 k t) H16 e 
h d H1)))))))) H10)) H9)))) | (Flat f) \Rightarrow (\lambda (H7: (drop i O 
(CHead c0 k t) (CHead c2 (Flat f) t0))).(\lambda (H8: (clear (CHead c2 (Flat 
f) t0) (CHead c1 (Bind b) u))).((match i in nat return (\lambda (n: 
nat).((drop h (S (plus n d)) (CHead c0 k t) e) \to ((drop n O (CHead c0 k t) 
(CHead c2 (Flat f) t0)) \to (ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T 
u (lift h d v)))) (\lambda (v: T).(\lambda (e0: C).(getl n e (CHead e0 (Bind 
b) v)))) (\lambda (_: T).(\lambda (e0: C).(drop h d c1 e0))))))) with [O 
\Rightarrow (\lambda (H9: (drop h (S (plus O d)) (CHead c0 k t) e)).(\lambda 
(H10: (drop O O (CHead c0 k t) (CHead c2 (Flat f) t0))).(let H11 \def 
(f_equal C C (\lambda (e0: C).(match e0 in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead c0 k t) 
(CHead c2 (Flat f) t0) (drop_gen_refl (CHead c0 k t) (CHead c2 (Flat f) t0) 
H10)) in ((let H12 \def (f_equal C K (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).K) with [(CSort _) \Rightarrow k | (CHead _ k _) \Rightarrow 
k])) (CHead c0 k t) (CHead c2 (Flat f) t0) (drop_gen_refl (CHead c0 k t) 
(CHead c2 (Flat f) t0) H10)) in ((let H13 \def (f_equal C T (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow t | 
(CHead _ _ t) \Rightarrow t])) (CHead c0 k t) (CHead c2 (Flat f) t0) 
(drop_gen_refl (CHead c0 k t) (CHead c2 (Flat f) t0) H10)) in (\lambda (H14: 
(eq K k (Flat f))).(\lambda (H15: (eq C c0 c2)).(let H16 \def (eq_ind_r C c2 
(\lambda (c: C).(clear c (CHead c1 (Bind b) u))) (clear_gen_flat f c2 (CHead 
c1 (Bind b) u) t0 H8) c0 H15) in (let H17 \def (eq_ind K k (\lambda (k: 
K).(drop h (S (plus O d)) (CHead c0 k t) e)) H9 (Flat f) H14) in (ex3_2_ind C 
T (\lambda (e0: C).(\lambda (v: T).(eq C e (CHead e0 (Flat f) v)))) (\lambda 
(_: C).(\lambda (v: T).(eq T t (lift h (r (Flat f) (plus O d)) v)))) (\lambda 
(e0: C).(\lambda (_: T).(drop h (r (Flat f) (plus O d)) c0 e0))) (ex3_2 T C 
(\lambda (v: T).(\lambda (_: C).(eq T u (lift h d v)))) (\lambda (v: 
T).(\lambda (e0: C).(getl O e (CHead e0 (Bind b) v)))) (\lambda (_: 
T).(\lambda (e0: C).(drop h d c1 e0)))) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H18: (eq C e (CHead x0 (Flat f) x1))).(\lambda (H19: (eq T t 
(lift h (r (Flat f) (plus O d)) x1))).(\lambda (H20: (drop h (r (Flat f) 
(plus O d)) c0 x0)).(let H21 \def (f_equal T T (\lambda (e0: T).e0) t (lift h 
(r (Flat f) (plus O d)) x1) H19) in (eq_ind_r C (CHead x0 (Flat f) x1) 
(\lambda (c3: C).(ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h d 
v)))) (\lambda (v: T).(\lambda (e0: C).(getl O c3 (CHead e0 (Bind b) v)))) 
(\lambda (_: T).(\lambda (e0: C).(drop h d c1 e0))))) (let H22 \def (H c1 u O 
(getl_intro O c0 (CHead c1 (Bind b) u) c0 (drop_refl c0) H16) x0 h d H20) in 
(ex3_2_ind T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h d v)))) 
(\lambda (v: T).(\lambda (e0: C).(getl O x0 (CHead e0 (Bind b) v)))) (\lambda 
(_: T).(\lambda (e0: C).(drop h d c1 e0))) (ex3_2 T C (\lambda (v: 
T).(\lambda (_: C).(eq T u (lift h d v)))) (\lambda (v: T).(\lambda (e0: 
C).(getl O (CHead x0 (Flat f) x1) (CHead e0 (Bind b) v)))) (\lambda (_: 
T).(\lambda (e0: C).(drop h d c1 e0)))) (\lambda (x2: T).(\lambda (x3: 
C).(\lambda (H23: (eq T u (lift h d x2))).(\lambda (H24: (getl O x0 (CHead x3 
(Bind b) x2))).(\lambda (H25: (drop h d c1 x3)).(let H26 \def (eq_ind T u 
(\lambda (t: T).(clear c0 (CHead c1 (Bind b) t))) H16 (lift h d x2) H23) in 
(eq_ind_r T (lift h d x2) (\lambda (t1: T).(ex3_2 T C (\lambda (v: 
T).(\lambda (_: C).(eq T t1 (lift h d v)))) (\lambda (v: T).(\lambda (e0: 
C).(getl O (CHead x0 (Flat f) x1) (CHead e0 (Bind b) v)))) (\lambda (_: 
T).(\lambda (e0: C).(drop h d c1 e0))))) (ex3_2_intro T C (\lambda (v: 
T).(\lambda (_: C).(eq T (lift h d x2) (lift h d v)))) (\lambda (v: 
T).(\lambda (e0: C).(getl O (CHead x0 (Flat f) x1) (CHead e0 (Bind b) v)))) 
(\lambda (_: T).(\lambda (e0: C).(drop h d c1 e0))) x2 x3 (refl_equal T (lift 
h d x2)) (getl_flat x0 (CHead x3 (Bind b) x2) O H24 f x1) H25) u H23))))))) 
H22)) e H18))))))) (drop_gen_skip_l c0 e t h (plus O d) (Flat f) H17))))))) 
H12)) H11)))) | (S n) \Rightarrow (\lambda (H9: (drop h (S (plus (S n) d)) 
(CHead c0 k t) e)).(\lambda (H10: (drop (S n) O (CHead c0 k t) (CHead c2 
(Flat f) t0))).(ex3_2_ind C T (\lambda (e0: C).(\lambda (v: T).(eq C e (CHead 
e0 k v)))) (\lambda (_: C).(\lambda (v: T).(eq T t (lift h (r k (plus (S n) 
d)) v)))) (\lambda (e0: C).(\lambda (_: T).(drop h (r k (plus (S n) d)) c0 
e0))) (ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h d v)))) 
(\lambda (v: T).(\lambda (e0: C).(getl (S n) e (CHead e0 (Bind b) v)))) 
(\lambda (_: T).(\lambda (e0: C).(drop h d c1 e0)))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H11: (eq C e (CHead x0 k x1))).(\lambda (H12: 
(eq T t (lift h (r k (plus (S n) d)) x1))).(\lambda (H13: (drop h (r k (plus 
(S n) d)) c0 x0)).(let H14 \def (f_equal T T (\lambda (e0: T).e0) t (lift h 
(r k (plus (S n) d)) x1) H12) in (eq_ind_r C (CHead x0 k x1) (\lambda (c3: 
C).(ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h d v)))) 
(\lambda (v: T).(\lambda (e0: C).(getl (S n) c3 (CHead e0 (Bind b) v)))) 
(\lambda (_: T).(\lambda (e0: C).(drop h d c1 e0))))) (let H15 \def (eq_ind 
nat (r k (plus (S n) d)) (\lambda (n: nat).(drop h n c0 x0)) H13 (plus (r k 
(S n)) d) (r_plus k (S n) d)) in (let H16 \def (eq_ind nat (r k (S n)) 
(\lambda (n: nat).(drop h (plus n d) c0 x0)) H15 (S (r k n)) (r_S k n)) in 
(let H17 \def (H c1 u (r k n) (getl_intro (r k n) c0 (CHead c1 (Bind b) u) 
(CHead c2 (Flat f) t0) (drop_gen_drop k c0 (CHead c2 (Flat f) t0) t n H10) 
(clear_flat c2 (CHead c1 (Bind b) u) (clear_gen_flat f c2 (CHead c1 (Bind b) 
u) t0 H8) f t0)) x0 h d H16) in (ex3_2_ind T C (\lambda (v: T).(\lambda (_: 
C).(eq T u (lift h d v)))) (\lambda (v: T).(\lambda (e0: C).(getl (r k n) x0 
(CHead e0 (Bind b) v)))) (\lambda (_: T).(\lambda (e0: C).(drop h d c1 e0))) 
(ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h d v)))) (\lambda 
(v: T).(\lambda (e0: C).(getl (S n) (CHead x0 k x1) (CHead e0 (Bind b) v)))) 
(\lambda (_: T).(\lambda (e0: C).(drop h d c1 e0)))) (\lambda (x2: 
T).(\lambda (x3: C).(\lambda (H18: (eq T u (lift h d x2))).(\lambda (H19: 
(getl (r k n) x0 (CHead x3 (Bind b) x2))).(\lambda (H20: (drop h d c1 
x3)).(let H21 \def (eq_ind T u (\lambda (t: T).(clear c2 (CHead c1 (Bind b) 
t))) (clear_gen_flat f c2 (CHead c1 (Bind b) u) t0 H8) (lift h d x2) H18) in 
(eq_ind_r T (lift h d x2) (\lambda (t1: T).(ex3_2 T C (\lambda (v: 
T).(\lambda (_: C).(eq T t1 (lift h d v)))) (\lambda (v: T).(\lambda (e0: 
C).(getl (S n) (CHead x0 k x1) (CHead e0 (Bind b) v)))) (\lambda (_: 
T).(\lambda (e0: C).(drop h d c1 e0))))) (ex3_2_intro T C (\lambda (v: 
T).(\lambda (_: C).(eq T (lift h d x2) (lift h d v)))) (\lambda (v: 
T).(\lambda (e0: C).(getl (S n) (CHead x0 k x1) (CHead e0 (Bind b) v)))) 
(\lambda (_: T).(\lambda (e0: C).(drop h d c1 e0))) x2 x3 (refl_equal T (lift 
h d x2)) (getl_head k n x0 (CHead x3 (Bind b) x2) H19 x1) H20) u H18))))))) 
H17)))) e H11))))))) (drop_gen_skip_l c0 e t h (plus (S n) d) k H9))))]) H1 
H7)))]) H5 H6)))]) H3 H4)))) H2)))))))))))))) c)).

theorem getl_drop_conf_ge:
 \forall (i: nat).(\forall (a: C).(\forall (c: C).((getl i c a) \to (\forall 
(e: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) \to ((le (plus d 
h) i) \to (getl (minus i h) e a)))))))))
\def
 \lambda (i: nat).(\lambda (a: C).(\lambda (c: C).(\lambda (H: (getl i c 
a)).(\lambda (e: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H0: (drop h 
d c e)).(\lambda (H1: (le (plus d h) i)).(let H2 \def (getl_gen_all c a i H) 
in (ex2_ind C (\lambda (e0: C).(drop i O c e0)) (\lambda (e0: C).(clear e0 
a)) (getl (minus i h) e a) (\lambda (x: C).(\lambda (H3: (drop i O c 
x)).(\lambda (H4: (clear x a)).(getl_intro (minus i h) e a x (drop_conf_ge i 
x c H3 e h d H0 H1) H4)))) H2)))))))))).

theorem getl_conf_ge_drop:
 \forall (b: B).(\forall (c1: C).(\forall (e: C).(\forall (u: T).(\forall (i: 
nat).((getl i c1 (CHead e (Bind b) u)) \to (\forall (c2: C).((drop (S O) i c1 
c2) \to (drop i O c2 e))))))))
\def
 \lambda (b: B).(\lambda (c1: C).(\lambda (e: C).(\lambda (u: T).(\lambda (i: 
nat).(\lambda (H: (getl i c1 (CHead e (Bind b) u))).(\lambda (c2: C).(\lambda 
(H0: (drop (S O) i c1 c2)).(let H3 \def (eq_ind nat (minus (S i) (S O)) 
(\lambda (n: nat).(drop n O c2 e)) (drop_conf_ge (S i) e c1 (getl_drop b c1 e 
u i H) c2 (S O) i H0 (eq_ind_r nat (plus (S O) i) (\lambda (n: nat).(le n (S 
i))) (le_n (S i)) (plus i (S O)) (plus_comm i (S O)))) i (minus_Sx_SO i)) in 
H3)))))))).

theorem getl_drop_conf_rev:
 \forall (j: nat).(\forall (e1: C).(\forall (e2: C).((drop j O e1 e2) \to 
(\forall (b: B).(\forall (c2: C).(\forall (v2: T).(\forall (i: nat).((getl i 
c2 (CHead e2 (Bind b) v2)) \to (ex2 C (\lambda (c1: C).(drop j O c1 c2)) 
(\lambda (c1: C).(drop (S i) j c1 e1)))))))))))
\def
 \lambda (j: nat).(\lambda (e1: C).(\lambda (e2: C).(\lambda (H: (drop j O e1 
e2)).(\lambda (b: B).(\lambda (c2: C).(\lambda (v2: T).(\lambda (i: 
nat).(\lambda (H0: (getl i c2 (CHead e2 (Bind b) v2))).(drop_conf_rev j e1 e2 
H c2 (S i) (getl_drop b c2 e2 v2 i H0)))))))))).

theorem drop_getl_trans_lt:
 \forall (i: nat).(\forall (d: nat).((lt i d) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (h: nat).((drop h d c1 c2) \to (\forall (b: B).(\forall (e2: 
C).(\forall (v: T).((getl i c2 (CHead e2 (Bind b) v)) \to (ex2 C (\lambda 
(e1: C).(getl i c1 (CHead e1 (Bind b) (lift h (minus d (S i)) v)))) (\lambda 
(e1: C).(drop h (minus d (S i)) e1 e2)))))))))))))
\def
 \lambda (i: nat).(\lambda (d: nat).(\lambda (H: (lt i d)).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (h: nat).(\lambda (H0: (drop h d c1 
c2)).(\lambda (b: B).(\lambda (e2: C).(\lambda (v: T).(\lambda (H1: (getl i 
c2 (CHead e2 (Bind b) v))).(let H2 \def (getl_gen_all c2 (CHead e2 (Bind b) 
v) i H1) in (ex2_ind C (\lambda (e: C).(drop i O c2 e)) (\lambda (e: 
C).(clear e (CHead e2 (Bind b) v))) (ex2 C (\lambda (e1: C).(getl i c1 (CHead 
e1 (Bind b) (lift h (minus d (S i)) v)))) (\lambda (e1: C).(drop h (minus d 
(S i)) e1 e2))) (\lambda (x: C).(\lambda (H3: (drop i O c2 x)).(\lambda (H4: 
(clear x (CHead e2 (Bind b) v))).(ex2_ind C (\lambda (e1: C).(drop i O c1 
e1)) (\lambda (e1: C).(drop h (minus d i) e1 x)) (ex2 C (\lambda (e1: 
C).(getl i c1 (CHead e1 (Bind b) (lift h (minus d (S i)) v)))) (\lambda (e1: 
C).(drop h (minus d (S i)) e1 e2))) (\lambda (x0: C).(\lambda (H5: (drop i O 
c1 x0)).(\lambda (H6: (drop h (minus d i) x0 x)).(let H7 \def (eq_ind nat 
(minus d i) (\lambda (n: nat).(drop h n x0 x)) H6 (S (minus d (S i))) 
(minus_x_Sy d i H)) in (let H8 \def (drop_clear_S x x0 h (minus d (S i)) H7 b 
e2 v H4) in (ex2_ind C (\lambda (c3: C).(clear x0 (CHead c3 (Bind b) (lift h 
(minus d (S i)) v)))) (\lambda (c3: C).(drop h (minus d (S i)) c3 e2)) (ex2 C 
(\lambda (e1: C).(getl i c1 (CHead e1 (Bind b) (lift h (minus d (S i)) v)))) 
(\lambda (e1: C).(drop h (minus d (S i)) e1 e2))) (\lambda (x1: C).(\lambda 
(H9: (clear x0 (CHead x1 (Bind b) (lift h (minus d (S i)) v)))).(\lambda 
(H10: (drop h (minus d (S i)) x1 e2)).(ex_intro2 C (\lambda (e1: C).(getl i 
c1 (CHead e1 (Bind b) (lift h (minus d (S i)) v)))) (\lambda (e1: C).(drop h 
(minus d (S i)) e1 e2)) x1 (getl_intro i c1 (CHead x1 (Bind b) (lift h (minus 
d (S i)) v)) x0 H5 H9) H10)))) H8)))))) (drop_trans_le i d (le_S_n i d (le_S 
(S i) d H)) c1 c2 h H0 x H3))))) H2)))))))))))).

theorem drop_getl_trans_le:
 \forall (i: nat).(\forall (d: nat).((le i d) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (h: nat).((drop h d c1 c2) \to (\forall (e2: C).((getl i c2 
e2) \to (ex3_2 C C (\lambda (e0: C).(\lambda (_: C).(drop i O c1 e0))) 
(\lambda (e0: C).(\lambda (e1: C).(drop h (minus d i) e0 e1))) (\lambda (_: 
C).(\lambda (e1: C).(clear e1 e2))))))))))))
\def
 \lambda (i: nat).(\lambda (d: nat).(\lambda (H: (le i d)).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (h: nat).(\lambda (H0: (drop h d c1 
c2)).(\lambda (e2: C).(\lambda (H1: (getl i c2 e2)).(let H2 \def 
(getl_gen_all c2 e2 i H1) in (ex2_ind C (\lambda (e: C).(drop i O c2 e)) 
(\lambda (e: C).(clear e e2)) (ex3_2 C C (\lambda (e0: C).(\lambda (_: 
C).(drop i O c1 e0))) (\lambda (e0: C).(\lambda (e1: C).(drop h (minus d i) 
e0 e1))) (\lambda (_: C).(\lambda (e1: C).(clear e1 e2)))) (\lambda (x: 
C).(\lambda (H3: (drop i O c2 x)).(\lambda (H4: (clear x e2)).(let H5 \def 
(drop_trans_le i d H c1 c2 h H0 x H3) in (ex2_ind C (\lambda (e1: C).(drop i 
O c1 e1)) (\lambda (e1: C).(drop h (minus d i) e1 x)) (ex3_2 C C (\lambda 
(e0: C).(\lambda (_: C).(drop i O c1 e0))) (\lambda (e0: C).(\lambda (e1: 
C).(drop h (minus d i) e0 e1))) (\lambda (_: C).(\lambda (e1: C).(clear e1 
e2)))) (\lambda (x0: C).(\lambda (H6: (drop i O c1 x0)).(\lambda (H7: (drop h 
(minus d i) x0 x)).(ex3_2_intro C C (\lambda (e0: C).(\lambda (_: C).(drop i 
O c1 e0))) (\lambda (e0: C).(\lambda (e1: C).(drop h (minus d i) e0 e1))) 
(\lambda (_: C).(\lambda (e1: C).(clear e1 e2))) x0 x H6 H7 H4)))) H5))))) 
H2)))))))))).

theorem drop_getl_trans_ge:
 \forall (i: nat).(\forall (c1: C).(\forall (c2: C).(\forall (d: 
nat).(\forall (h: nat).((drop h d c1 c2) \to (\forall (e2: C).((getl i c2 e2) 
\to ((le d i) \to (getl (plus i h) c1 e2)))))))))
\def
 \lambda (i: nat).(\lambda (c1: C).(\lambda (c2: C).(\lambda (d: 
nat).(\lambda (h: nat).(\lambda (H: (drop h d c1 c2)).(\lambda (e2: 
C).(\lambda (H0: (getl i c2 e2)).(\lambda (H1: (le d i)).(let H2 \def 
(getl_gen_all c2 e2 i H0) in (ex2_ind C (\lambda (e: C).(drop i O c2 e)) 
(\lambda (e: C).(clear e e2)) (getl (plus i h) c1 e2) (\lambda (x: 
C).(\lambda (H3: (drop i O c2 x)).(\lambda (H4: (clear x e2)).(getl_intro 
(plus i h) c1 e2 x (drop_trans_ge i c1 c2 d h H x H3 H1) H4)))) H2)))))))))).

theorem getl_drop_trans:
 \forall (c1: C).(\forall (c2: C).(\forall (h: nat).((getl h c1 c2) \to 
(\forall (e2: C).(\forall (i: nat).((drop (S i) O c2 e2) \to (drop (S (plus i 
h)) O c1 e2)))))))
\def
 \lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: C).(\forall (h: 
nat).((getl h c c2) \to (\forall (e2: C).(\forall (i: nat).((drop (S i) O c2 
e2) \to (drop (S (plus i h)) O c e2)))))))) (\lambda (n: nat).(\lambda (c2: 
C).(\lambda (h: nat).(\lambda (H: (getl h (CSort n) c2)).(\lambda (e2: 
C).(\lambda (i: nat).(\lambda (_: (drop (S i) O c2 e2)).(getl_gen_sort n h c2 
H (drop (S (plus i h)) O (CSort n) e2))))))))) (\lambda (c2: C).(\lambda 
(IHc: ((\forall (c3: C).(\forall (h: nat).((getl h c2 c3) \to (\forall (e2: 
C).(\forall (i: nat).((drop (S i) O c3 e2) \to (drop (S (plus i h)) O c2 
e2))))))))).(\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (t: T).(\forall 
(c3: C).(\forall (h: nat).((getl h (CHead c2 k0 t) c3) \to (\forall (e2: 
C).(\forall (i: nat).((drop (S i) O c3 e2) \to (drop (S (plus i h)) O (CHead 
c2 k0 t) e2))))))))) (\lambda (b: B).(\lambda (t: T).(\lambda (c3: 
C).(\lambda (h: nat).(nat_ind (\lambda (n: nat).((getl n (CHead c2 (Bind b) 
t) c3) \to (\forall (e2: C).(\forall (i: nat).((drop (S i) O c3 e2) \to (drop 
(S (plus i n)) O (CHead c2 (Bind b) t) e2)))))) (\lambda (H: (getl O (CHead 
c2 (Bind b) t) c3)).(\lambda (e2: C).(\lambda (i: nat).(\lambda (H0: (drop (S 
i) O c3 e2)).(let H1 \def (eq_ind C c3 (\lambda (c: C).(drop (S i) O c e2)) 
H0 (CHead c2 (Bind b) t) (clear_gen_bind b c2 c3 t (getl_gen_O (CHead c2 
(Bind b) t) c3 H))) in (eq_ind nat i (\lambda (n: nat).(drop (S n) O (CHead 
c2 (Bind b) t) e2)) (drop_drop (Bind b) i c2 e2 (drop_gen_drop (Bind b) c2 e2 
t i H1) t) (plus i O) (plus_n_O i))))))) (\lambda (n: nat).(\lambda (_: 
(((getl n (CHead c2 (Bind b) t) c3) \to (\forall (e2: C).(\forall (i: 
nat).((drop (S i) O c3 e2) \to (drop (S (plus i n)) O (CHead c2 (Bind b) t) 
e2))))))).(\lambda (H0: (getl (S n) (CHead c2 (Bind b) t) c3)).(\lambda (e2: 
C).(\lambda (i: nat).(\lambda (H1: (drop (S i) O c3 e2)).(eq_ind nat (plus (S 
i) n) (\lambda (n0: nat).(drop (S n0) O (CHead c2 (Bind b) t) e2)) (drop_drop 
(Bind b) (plus (S i) n) c2 e2 (IHc c3 n (getl_gen_S (Bind b) c2 c3 t n H0) e2 
i H1) t) (plus i (S n)) (plus_Snm_nSm i n)))))))) h))))) (\lambda (f: 
F).(\lambda (t: T).(\lambda (c3: C).(\lambda (h: nat).(nat_ind (\lambda (n: 
nat).((getl n (CHead c2 (Flat f) t) c3) \to (\forall (e2: C).(\forall (i: 
nat).((drop (S i) O c3 e2) \to (drop (S (plus i n)) O (CHead c2 (Flat f) t) 
e2)))))) (\lambda (H: (getl O (CHead c2 (Flat f) t) c3)).(\lambda (e2: 
C).(\lambda (i: nat).(\lambda (H0: (drop (S i) O c3 e2)).(drop_drop (Flat f) 
(plus i O) c2 e2 (IHc c3 O (getl_intro O c2 c3 c2 (drop_refl c2) 
(clear_gen_flat f c2 c3 t (getl_gen_O (CHead c2 (Flat f) t) c3 H))) e2 i H0) 
t))))) (\lambda (n: nat).(\lambda (_: (((getl n (CHead c2 (Flat f) t) c3) \to 
(\forall (e2: C).(\forall (i: nat).((drop (S i) O c3 e2) \to (drop (S (plus i 
n)) O (CHead c2 (Flat f) t) e2))))))).(\lambda (H0: (getl (S n) (CHead c2 
(Flat f) t) c3)).(\lambda (e2: C).(\lambda (i: nat).(\lambda (H1: (drop (S i) 
O c3 e2)).(drop_drop (Flat f) (plus i (S n)) c2 e2 (IHc c3 (S n) (getl_gen_S 
(Flat f) c2 c3 t n H0) e2 i H1) t))))))) h))))) k)))) c1).

