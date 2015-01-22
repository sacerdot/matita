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

include "Basic-1/drop/fwd.ma".

include "Basic-1/lift/props.ma".

include "Basic-1/r/props.ma".

theorem drop_skip_bind:
 \forall (h: nat).(\forall (d: nat).(\forall (c: C).(\forall (e: C).((drop h 
d c e) \to (\forall (b: B).(\forall (u: T).(drop h (S d) (CHead c (Bind b) 
(lift h d u)) (CHead e (Bind b) u))))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (c: C).(\lambda (e: C).(\lambda 
(H: (drop h d c e)).(\lambda (b: B).(\lambda (u: T).(eq_ind nat (r (Bind b) 
d) (\lambda (n: nat).(drop h (S d) (CHead c (Bind b) (lift h n u)) (CHead e 
(Bind b) u))) (drop_skip (Bind b) h d c e H u) d (refl_equal nat d)))))))).
(* COMMENTS
Initial nodes: 95
END *)

theorem drop_skip_flat:
 \forall (h: nat).(\forall (d: nat).(\forall (c: C).(\forall (e: C).((drop h 
(S d) c e) \to (\forall (f: F).(\forall (u: T).(drop h (S d) (CHead c (Flat 
f) (lift h (S d) u)) (CHead e (Flat f) u))))))))
\def
 \lambda (h: nat).(\lambda (d: nat).(\lambda (c: C).(\lambda (e: C).(\lambda 
(H: (drop h (S d) c e)).(\lambda (f: F).(\lambda (u: T).(eq_ind nat (r (Flat 
f) d) (\lambda (n: nat).(drop h (S d) (CHead c (Flat f) (lift h n u)) (CHead 
e (Flat f) u))) (drop_skip (Flat f) h d c e H u) (S d) (refl_equal nat (S 
d))))))))).
(* COMMENTS
Initial nodes: 101
END *)

theorem drop_S:
 \forall (b: B).(\forall (c: C).(\forall (e: C).(\forall (u: T).(\forall (h: 
nat).((drop h O c (CHead e (Bind b) u)) \to (drop (S h) O c e))))))
\def
 \lambda (b: B).(\lambda (c: C).(C_ind (\lambda (c0: C).(\forall (e: 
C).(\forall (u: T).(\forall (h: nat).((drop h O c0 (CHead e (Bind b) u)) \to 
(drop (S h) O c0 e)))))) (\lambda (n: nat).(\lambda (e: C).(\lambda (u: 
T).(\lambda (h: nat).(\lambda (H: (drop h O (CSort n) (CHead e (Bind b) 
u))).(and3_ind (eq C (CHead e (Bind b) u) (CSort n)) (eq nat h O) (eq nat O 
O) (drop (S h) O (CSort n) e) (\lambda (H0: (eq C (CHead e (Bind b) u) (CSort 
n))).(\lambda (H1: (eq nat h O)).(\lambda (_: (eq nat O O)).(eq_ind_r nat O 
(\lambda (n0: nat).(drop (S n0) O (CSort n) e)) (let H3 \def (eq_ind C (CHead 
e (Bind b) u) (\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) 
with [(CSort _) \Rightarrow False | (CHead _ _ _) \Rightarrow True])) I 
(CSort n) H0) in (False_ind (drop (S O) O (CSort n) e) H3)) h H1)))) 
(drop_gen_sort n h O (CHead e (Bind b) u) H))))))) (\lambda (c0: C).(\lambda 
(H: ((\forall (e: C).(\forall (u: T).(\forall (h: nat).((drop h O c0 (CHead e 
(Bind b) u)) \to (drop (S h) O c0 e))))))).(\lambda (k: K).(\lambda (t: 
T).(\lambda (e: C).(\lambda (u: T).(\lambda (h: nat).(nat_ind (\lambda (n: 
nat).((drop n O (CHead c0 k t) (CHead e (Bind b) u)) \to (drop (S n) O (CHead 
c0 k t) e))) (\lambda (H0: (drop O O (CHead c0 k t) (CHead e (Bind b) 
u))).(let H1 \def (f_equal C C (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | (CHead c1 _ _) 
\Rightarrow c1])) (CHead c0 k t) (CHead e (Bind b) u) (drop_gen_refl (CHead 
c0 k t) (CHead e (Bind b) u) H0)) in ((let H2 \def (f_equal C K (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k | 
(CHead _ k0 _) \Rightarrow k0])) (CHead c0 k t) (CHead e (Bind b) u) 
(drop_gen_refl (CHead c0 k t) (CHead e (Bind b) u) H0)) in ((let H3 \def 
(f_equal C T (\lambda (e0: C).(match e0 in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow t | (CHead _ _ t0) \Rightarrow t0])) (CHead c0 k t) 
(CHead e (Bind b) u) (drop_gen_refl (CHead c0 k t) (CHead e (Bind b) u) H0)) 
in (\lambda (H4: (eq K k (Bind b))).(\lambda (H5: (eq C c0 e)).(eq_ind C c0 
(\lambda (c1: C).(drop (S O) O (CHead c0 k t) c1)) (eq_ind_r K (Bind b) 
(\lambda (k0: K).(drop (S O) O (CHead c0 k0 t) c0)) (drop_drop (Bind b) O c0 
c0 (drop_refl c0) t) k H4) e H5)))) H2)) H1))) (\lambda (n: nat).(\lambda (_: 
(((drop n O (CHead c0 k t) (CHead e (Bind b) u)) \to (drop (S n) O (CHead c0 
k t) e)))).(\lambda (H1: (drop (S n) O (CHead c0 k t) (CHead e (Bind b) 
u))).(drop_drop k (S n) c0 e (eq_ind_r nat (S (r k n)) (\lambda (n0: 
nat).(drop n0 O c0 e)) (H e u (r k n) (drop_gen_drop k c0 (CHead e (Bind b) 
u) t n H1)) (r k (S n)) (r_S k n)) t)))) h)))))))) c)).
(* COMMENTS
Initial nodes: 807
END *)

theorem drop_ctail:
 \forall (c1: C).(\forall (c2: C).(\forall (d: nat).(\forall (h: nat).((drop 
h d c1 c2) \to (\forall (k: K).(\forall (u: T).(drop h d (CTail k u c1) 
(CTail k u c2))))))))
\def
 \lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: C).(\forall (d: 
nat).(\forall (h: nat).((drop h d c c2) \to (\forall (k: K).(\forall (u: 
T).(drop h d (CTail k u c) (CTail k u c2))))))))) (\lambda (n: nat).(\lambda 
(c2: C).(\lambda (d: nat).(\lambda (h: nat).(\lambda (H: (drop h d (CSort n) 
c2)).(\lambda (k: K).(\lambda (u: T).(and3_ind (eq C c2 (CSort n)) (eq nat h 
O) (eq nat d O) (drop h d (CTail k u (CSort n)) (CTail k u c2)) (\lambda (H0: 
(eq C c2 (CSort n))).(\lambda (H1: (eq nat h O)).(\lambda (H2: (eq nat d 
O)).(eq_ind_r nat O (\lambda (n0: nat).(drop n0 d (CTail k u (CSort n)) 
(CTail k u c2))) (eq_ind_r nat O (\lambda (n0: nat).(drop O n0 (CTail k u 
(CSort n)) (CTail k u c2))) (eq_ind_r C (CSort n) (\lambda (c: C).(drop O O 
(CTail k u (CSort n)) (CTail k u c))) (drop_refl (CTail k u (CSort n))) c2 
H0) d H2) h H1)))) (drop_gen_sort n h d c2 H))))))))) (\lambda (c2: 
C).(\lambda (IHc: ((\forall (c3: C).(\forall (d: nat).(\forall (h: 
nat).((drop h d c2 c3) \to (\forall (k: K).(\forall (u: T).(drop h d (CTail k 
u c2) (CTail k u c3)))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c3: 
C).(\lambda (d: nat).(nat_ind (\lambda (n: nat).(\forall (h: nat).((drop h n 
(CHead c2 k t) c3) \to (\forall (k0: K).(\forall (u: T).(drop h n (CTail k0 u 
(CHead c2 k t)) (CTail k0 u c3))))))) (\lambda (h: nat).(nat_ind (\lambda (n: 
nat).((drop n O (CHead c2 k t) c3) \to (\forall (k0: K).(\forall (u: T).(drop 
n O (CTail k0 u (CHead c2 k t)) (CTail k0 u c3)))))) (\lambda (H: (drop O O 
(CHead c2 k t) c3)).(\lambda (k0: K).(\lambda (u: T).(eq_ind C (CHead c2 k t) 
(\lambda (c: C).(drop O O (CTail k0 u (CHead c2 k t)) (CTail k0 u c))) 
(drop_refl (CTail k0 u (CHead c2 k t))) c3 (drop_gen_refl (CHead c2 k t) c3 
H))))) (\lambda (n: nat).(\lambda (_: (((drop n O (CHead c2 k t) c3) \to 
(\forall (k0: K).(\forall (u: T).(drop n O (CTail k0 u (CHead c2 k t)) (CTail 
k0 u c3))))))).(\lambda (H0: (drop (S n) O (CHead c2 k t) c3)).(\lambda (k0: 
K).(\lambda (u: T).(drop_drop k n (CTail k0 u c2) (CTail k0 u c3) (IHc c3 O 
(r k n) (drop_gen_drop k c2 c3 t n H0) k0 u) t)))))) h)) (\lambda (n: 
nat).(\lambda (H: ((\forall (h: nat).((drop h n (CHead c2 k t) c3) \to 
(\forall (k0: K).(\forall (u: T).(drop h n (CTail k0 u (CHead c2 k t)) (CTail 
k0 u c3)))))))).(\lambda (h: nat).(\lambda (H0: (drop h (S n) (CHead c2 k t) 
c3)).(\lambda (k0: K).(\lambda (u: T).(ex3_2_ind C T (\lambda (e: C).(\lambda 
(v: T).(eq C c3 (CHead e k v)))) (\lambda (_: C).(\lambda (v: T).(eq T t 
(lift h (r k n) v)))) (\lambda (e: C).(\lambda (_: T).(drop h (r k n) c2 e))) 
(drop h (S n) (CTail k0 u (CHead c2 k t)) (CTail k0 u c3)) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H1: (eq C c3 (CHead x0 k x1))).(\lambda (H2: 
(eq T t (lift h (r k n) x1))).(\lambda (H3: (drop h (r k n) c2 x0)).(let H4 
\def (eq_ind C c3 (\lambda (c: C).(\forall (h0: nat).((drop h0 n (CHead c2 k 
t) c) \to (\forall (k1: K).(\forall (u0: T).(drop h0 n (CTail k1 u0 (CHead c2 
k t)) (CTail k1 u0 c))))))) H (CHead x0 k x1) H1) in (eq_ind_r C (CHead x0 k 
x1) (\lambda (c: C).(drop h (S n) (CTail k0 u (CHead c2 k t)) (CTail k0 u 
c))) (let H5 \def (eq_ind T t (\lambda (t0: T).(\forall (h0: nat).((drop h0 n 
(CHead c2 k t0) (CHead x0 k x1)) \to (\forall (k1: K).(\forall (u0: T).(drop 
h0 n (CTail k1 u0 (CHead c2 k t0)) (CTail k1 u0 (CHead x0 k x1)))))))) H4 
(lift h (r k n) x1) H2) in (eq_ind_r T (lift h (r k n) x1) (\lambda (t0: 
T).(drop h (S n) (CTail k0 u (CHead c2 k t0)) (CTail k0 u (CHead x0 k x1)))) 
(drop_skip k h n (CTail k0 u c2) (CTail k0 u x0) (IHc x0 (r k n) h H3 k0 u) 
x1) t H2)) c3 H1))))))) (drop_gen_skip_l c2 c3 t h n k H0)))))))) d))))))) 
c1).
(* COMMENTS
Initial nodes: 1211
END *)

theorem drop_mono:
 \forall (c: C).(\forall (x1: C).(\forall (d: nat).(\forall (h: nat).((drop h 
d c x1) \to (\forall (x2: C).((drop h d c x2) \to (eq C x1 x2)))))))
\def
 \lambda (c: C).(C_ind (\lambda (c0: C).(\forall (x1: C).(\forall (d: 
nat).(\forall (h: nat).((drop h d c0 x1) \to (\forall (x2: C).((drop h d c0 
x2) \to (eq C x1 x2)))))))) (\lambda (n: nat).(\lambda (x1: C).(\lambda (d: 
nat).(\lambda (h: nat).(\lambda (H: (drop h d (CSort n) x1)).(\lambda (x2: 
C).(\lambda (H0: (drop h d (CSort n) x2)).(and3_ind (eq C x2 (CSort n)) (eq 
nat h O) (eq nat d O) (eq C x1 x2) (\lambda (H1: (eq C x2 (CSort 
n))).(\lambda (H2: (eq nat h O)).(\lambda (H3: (eq nat d O)).(and3_ind (eq C 
x1 (CSort n)) (eq nat h O) (eq nat d O) (eq C x1 x2) (\lambda (H4: (eq C x1 
(CSort n))).(\lambda (H5: (eq nat h O)).(\lambda (H6: (eq nat d O)).(eq_ind_r 
C (CSort n) (\lambda (c0: C).(eq C x1 c0)) (let H7 \def (eq_ind nat h 
(\lambda (n0: nat).(eq nat n0 O)) H2 O H5) in (let H8 \def (eq_ind nat d 
(\lambda (n0: nat).(eq nat n0 O)) H3 O H6) in (eq_ind_r C (CSort n) (\lambda 
(c0: C).(eq C c0 (CSort n))) (refl_equal C (CSort n)) x1 H4))) x2 H1)))) 
(drop_gen_sort n h d x1 H))))) (drop_gen_sort n h d x2 H0))))))))) (\lambda 
(c0: C).(\lambda (H: ((\forall (x1: C).(\forall (d: nat).(\forall (h: 
nat).((drop h d c0 x1) \to (\forall (x2: C).((drop h d c0 x2) \to (eq C x1 
x2))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (x1: C).(\lambda (d: 
nat).(nat_ind (\lambda (n: nat).(\forall (h: nat).((drop h n (CHead c0 k t) 
x1) \to (\forall (x2: C).((drop h n (CHead c0 k t) x2) \to (eq C x1 x2)))))) 
(\lambda (h: nat).(nat_ind (\lambda (n: nat).((drop n O (CHead c0 k t) x1) 
\to (\forall (x2: C).((drop n O (CHead c0 k t) x2) \to (eq C x1 x2))))) 
(\lambda (H0: (drop O O (CHead c0 k t) x1)).(\lambda (x2: C).(\lambda (H1: 
(drop O O (CHead c0 k t) x2)).(eq_ind C (CHead c0 k t) (\lambda (c1: C).(eq C 
x1 c1)) (eq_ind C (CHead c0 k t) (\lambda (c1: C).(eq C c1 (CHead c0 k t))) 
(refl_equal C (CHead c0 k t)) x1 (drop_gen_refl (CHead c0 k t) x1 H0)) x2 
(drop_gen_refl (CHead c0 k t) x2 H1))))) (\lambda (n: nat).(\lambda (_: 
(((drop n O (CHead c0 k t) x1) \to (\forall (x2: C).((drop n O (CHead c0 k t) 
x2) \to (eq C x1 x2)))))).(\lambda (H1: (drop (S n) O (CHead c0 k t) 
x1)).(\lambda (x2: C).(\lambda (H2: (drop (S n) O (CHead c0 k t) x2)).(H x1 O 
(r k n) (drop_gen_drop k c0 x1 t n H1) x2 (drop_gen_drop k c0 x2 t n 
H2))))))) h)) (\lambda (n: nat).(\lambda (H0: ((\forall (h: nat).((drop h n 
(CHead c0 k t) x1) \to (\forall (x2: C).((drop h n (CHead c0 k t) x2) \to (eq 
C x1 x2))))))).(\lambda (h: nat).(\lambda (H1: (drop h (S n) (CHead c0 k t) 
x1)).(\lambda (x2: C).(\lambda (H2: (drop h (S n) (CHead c0 k t) 
x2)).(ex3_2_ind C T (\lambda (e: C).(\lambda (v: T).(eq C x2 (CHead e k v)))) 
(\lambda (_: C).(\lambda (v: T).(eq T t (lift h (r k n) v)))) (\lambda (e: 
C).(\lambda (_: T).(drop h (r k n) c0 e))) (eq C x1 x2) (\lambda (x0: 
C).(\lambda (x3: T).(\lambda (H3: (eq C x2 (CHead x0 k x3))).(\lambda (H4: 
(eq T t (lift h (r k n) x3))).(\lambda (H5: (drop h (r k n) c0 
x0)).(ex3_2_ind C T (\lambda (e: C).(\lambda (v: T).(eq C x1 (CHead e k v)))) 
(\lambda (_: C).(\lambda (v: T).(eq T t (lift h (r k n) v)))) (\lambda (e: 
C).(\lambda (_: T).(drop h (r k n) c0 e))) (eq C x1 x2) (\lambda (x4: 
C).(\lambda (x5: T).(\lambda (H6: (eq C x1 (CHead x4 k x5))).(\lambda (H7: 
(eq T t (lift h (r k n) x5))).(\lambda (H8: (drop h (r k n) c0 x4)).(eq_ind_r 
C (CHead x0 k x3) (\lambda (c1: C).(eq C x1 c1)) (let H9 \def (eq_ind C x1 
(\lambda (c1: C).(\forall (h0: nat).((drop h0 n (CHead c0 k t) c1) \to 
(\forall (x6: C).((drop h0 n (CHead c0 k t) x6) \to (eq C c1 x6)))))) H0 
(CHead x4 k x5) H6) in (eq_ind_r C (CHead x4 k x5) (\lambda (c1: C).(eq C c1 
(CHead x0 k x3))) (let H10 \def (eq_ind T t (\lambda (t0: T).(\forall (h0: 
nat).((drop h0 n (CHead c0 k t0) (CHead x4 k x5)) \to (\forall (x6: C).((drop 
h0 n (CHead c0 k t0) x6) \to (eq C (CHead x4 k x5) x6)))))) H9 (lift h (r k 
n) x5) H7) in (let H11 \def (eq_ind T t (\lambda (t0: T).(eq T t0 (lift h (r 
k n) x3))) H4 (lift h (r k n) x5) H7) in (let H12 \def (eq_ind T x5 (\lambda 
(t0: T).(\forall (h0: nat).((drop h0 n (CHead c0 k (lift h (r k n) t0)) 
(CHead x4 k t0)) \to (\forall (x6: C).((drop h0 n (CHead c0 k (lift h (r k n) 
t0)) x6) \to (eq C (CHead x4 k t0) x6)))))) H10 x3 (lift_inj x5 x3 h (r k n) 
H11)) in (eq_ind_r T x3 (\lambda (t0: T).(eq C (CHead x4 k t0) (CHead x0 k 
x3))) (f_equal3 C K T C CHead x4 x0 k k x3 x3 (sym_eq C x0 x4 (H x0 (r k n) h 
H5 x4 H8)) (refl_equal K k) (refl_equal T x3)) x5 (lift_inj x5 x3 h (r k n) 
H11))))) x1 H6)) x2 H3)))))) (drop_gen_skip_l c0 x1 t h n k H1))))))) 
(drop_gen_skip_l c0 x2 t h n k H2)))))))) d))))))) c).
(* COMMENTS
Initial nodes: 1539
END *)

theorem drop_conf_lt:
 \forall (k: K).(\forall (i: nat).(\forall (u: T).(\forall (c0: C).(\forall 
(c: C).((drop i O c (CHead c0 k u)) \to (\forall (e: C).(\forall (h: 
nat).(\forall (d: nat).((drop h (S (plus i d)) c e) \to (ex3_2 T C (\lambda 
(v: T).(\lambda (_: C).(eq T u (lift h (r k d) v)))) (\lambda (v: T).(\lambda 
(e0: C).(drop i O e (CHead e0 k v)))) (\lambda (_: T).(\lambda (e0: C).(drop 
h (r k d) c0 e0)))))))))))))
\def
 \lambda (k: K).(\lambda (i: nat).(nat_ind (\lambda (n: nat).(\forall (u: 
T).(\forall (c0: C).(\forall (c: C).((drop n O c (CHead c0 k u)) \to (\forall 
(e: C).(\forall (h: nat).(\forall (d: nat).((drop h (S (plus n d)) c e) \to 
(ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h (r k d) v)))) 
(\lambda (v: T).(\lambda (e0: C).(drop n O e (CHead e0 k v)))) (\lambda (_: 
T).(\lambda (e0: C).(drop h (r k d) c0 e0))))))))))))) (\lambda (u: 
T).(\lambda (c0: C).(\lambda (c: C).(\lambda (H: (drop O O c (CHead c0 k 
u))).(\lambda (e: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H0: (drop 
h (S (plus O d)) c e)).(let H1 \def (eq_ind C c (\lambda (c1: C).(drop h (S 
(plus O d)) c1 e)) H0 (CHead c0 k u) (drop_gen_refl c (CHead c0 k u) H)) in 
(ex3_2_ind C T (\lambda (e0: C).(\lambda (v: T).(eq C e (CHead e0 k v)))) 
(\lambda (_: C).(\lambda (v: T).(eq T u (lift h (r k (plus O d)) v)))) 
(\lambda (e0: C).(\lambda (_: T).(drop h (r k (plus O d)) c0 e0))) (ex3_2 T C 
(\lambda (v: T).(\lambda (_: C).(eq T u (lift h (r k d) v)))) (\lambda (v: 
T).(\lambda (e0: C).(drop O O e (CHead e0 k v)))) (\lambda (_: T).(\lambda 
(e0: C).(drop h (r k d) c0 e0)))) (\lambda (x0: C).(\lambda (x1: T).(\lambda 
(H2: (eq C e (CHead x0 k x1))).(\lambda (H3: (eq T u (lift h (r k (plus O d)) 
x1))).(\lambda (H4: (drop h (r k (plus O d)) c0 x0)).(eq_ind_r C (CHead x0 k 
x1) (\lambda (c1: C).(ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift 
h (r k d) v)))) (\lambda (v: T).(\lambda (e0: C).(drop O O c1 (CHead e0 k 
v)))) (\lambda (_: T).(\lambda (e0: C).(drop h (r k d) c0 e0))))) (eq_ind_r T 
(lift h (r k (plus O d)) x1) (\lambda (t: T).(ex3_2 T C (\lambda (v: 
T).(\lambda (_: C).(eq T t (lift h (r k d) v)))) (\lambda (v: T).(\lambda 
(e0: C).(drop O O (CHead x0 k x1) (CHead e0 k v)))) (\lambda (_: T).(\lambda 
(e0: C).(drop h (r k d) c0 e0))))) (ex3_2_intro T C (\lambda (v: T).(\lambda 
(_: C).(eq T (lift h (r k (plus O d)) x1) (lift h (r k d) v)))) (\lambda (v: 
T).(\lambda (e0: C).(drop O O (CHead x0 k x1) (CHead e0 k v)))) (\lambda (_: 
T).(\lambda (e0: C).(drop h (r k d) c0 e0))) x1 x0 (refl_equal T (lift h (r k 
d) x1)) (drop_refl (CHead x0 k x1)) H4) u H3) e H2)))))) (drop_gen_skip_l c0 
e u h (plus O d) k H1))))))))))) (\lambda (i0: nat).(\lambda (H: ((\forall 
(u: T).(\forall (c0: C).(\forall (c: C).((drop i0 O c (CHead c0 k u)) \to 
(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h (S (plus i0 d)) 
c e) \to (ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h (r k d) 
v)))) (\lambda (v: T).(\lambda (e0: C).(drop i0 O e (CHead e0 k v)))) 
(\lambda (_: T).(\lambda (e0: C).(drop h (r k d) c0 e0)))))))))))))).(\lambda 
(u: T).(\lambda (c0: C).(\lambda (c: C).(C_ind (\lambda (c1: C).((drop (S i0) 
O c1 (CHead c0 k u)) \to (\forall (e: C).(\forall (h: nat).(\forall (d: 
nat).((drop h (S (plus (S i0) d)) c1 e) \to (ex3_2 T C (\lambda (v: 
T).(\lambda (_: C).(eq T u (lift h (r k d) v)))) (\lambda (v: T).(\lambda 
(e0: C).(drop (S i0) O e (CHead e0 k v)))) (\lambda (_: T).(\lambda (e0: 
C).(drop h (r k d) c0 e0)))))))))) (\lambda (n: nat).(\lambda (_: (drop (S 
i0) O (CSort n) (CHead c0 k u))).(\lambda (e: C).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (H1: (drop h (S (plus (S i0) d)) (CSort n) e)).(and3_ind 
(eq C e (CSort n)) (eq nat h O) (eq nat (S (plus (S i0) d)) O) (ex3_2 T C 
(\lambda (v: T).(\lambda (_: C).(eq T u (lift h (r k d) v)))) (\lambda (v: 
T).(\lambda (e0: C).(drop (S i0) O e (CHead e0 k v)))) (\lambda (_: 
T).(\lambda (e0: C).(drop h (r k d) c0 e0)))) (\lambda (_: (eq C e (CSort 
n))).(\lambda (_: (eq nat h O)).(\lambda (H4: (eq nat (S (plus (S i0) d)) 
O)).(let H5 \def (eq_ind nat (S (plus (S i0) d)) (\lambda (ee: nat).(match ee 
in nat return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) 
\Rightarrow True])) I O H4) in (False_ind (ex3_2 T C (\lambda (v: T).(\lambda 
(_: C).(eq T u (lift h (r k d) v)))) (\lambda (v: T).(\lambda (e0: C).(drop 
(S i0) O e (CHead e0 k v)))) (\lambda (_: T).(\lambda (e0: C).(drop h (r k d) 
c0 e0)))) H5))))) (drop_gen_sort n h (S (plus (S i0) d)) e H1)))))))) 
(\lambda (c1: C).(\lambda (H0: (((drop (S i0) O c1 (CHead c0 k u)) \to 
(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h (S (plus (S i0) 
d)) c1 e) \to (ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h (r k 
d) v)))) (\lambda (v: T).(\lambda (e0: C).(drop (S i0) O e (CHead e0 k v)))) 
(\lambda (_: T).(\lambda (e0: C).(drop h (r k d) c0 e0))))))))))).(\lambda 
(k0: K).(K_ind (\lambda (k1: K).(\forall (t: T).((drop (S i0) O (CHead c1 k1 
t) (CHead c0 k u)) \to (\forall (e: C).(\forall (h: nat).(\forall (d: 
nat).((drop h (S (plus (S i0) d)) (CHead c1 k1 t) e) \to (ex3_2 T C (\lambda 
(v: T).(\lambda (_: C).(eq T u (lift h (r k d) v)))) (\lambda (v: T).(\lambda 
(e0: C).(drop (S i0) O e (CHead e0 k v)))) (\lambda (_: T).(\lambda (e0: 
C).(drop h (r k d) c0 e0))))))))))) (\lambda (b: B).(\lambda (t: T).(\lambda 
(H1: (drop (S i0) O (CHead c1 (Bind b) t) (CHead c0 k u))).(\lambda (e: 
C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H2: (drop h (S (plus (S i0) 
d)) (CHead c1 (Bind b) t) e)).(ex3_2_ind C T (\lambda (e0: C).(\lambda (v: 
T).(eq C e (CHead e0 (Bind b) v)))) (\lambda (_: C).(\lambda (v: T).(eq T t 
(lift h (r (Bind b) (plus (S i0) d)) v)))) (\lambda (e0: C).(\lambda (_: 
T).(drop h (r (Bind b) (plus (S i0) d)) c1 e0))) (ex3_2 T C (\lambda (v: 
T).(\lambda (_: C).(eq T u (lift h (r k d) v)))) (\lambda (v: T).(\lambda 
(e0: C).(drop (S i0) O e (CHead e0 k v)))) (\lambda (_: T).(\lambda (e0: 
C).(drop h (r k d) c0 e0)))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H3: 
(eq C e (CHead x0 (Bind b) x1))).(\lambda (_: (eq T t (lift h (r (Bind b) 
(plus (S i0) d)) x1))).(\lambda (H5: (drop h (r (Bind b) (plus (S i0) d)) c1 
x0)).(eq_ind_r C (CHead x0 (Bind b) x1) (\lambda (c2: C).(ex3_2 T C (\lambda 
(v: T).(\lambda (_: C).(eq T u (lift h (r k d) v)))) (\lambda (v: T).(\lambda 
(e0: C).(drop (S i0) O c2 (CHead e0 k v)))) (\lambda (_: T).(\lambda (e0: 
C).(drop h (r k d) c0 e0))))) (let H6 \def (H u c0 c1 (drop_gen_drop (Bind b) 
c1 (CHead c0 k u) t i0 H1) x0 h d H5) in (ex3_2_ind T C (\lambda (v: 
T).(\lambda (_: C).(eq T u (lift h (r k d) v)))) (\lambda (v: T).(\lambda 
(e0: C).(drop i0 O x0 (CHead e0 k v)))) (\lambda (_: T).(\lambda (e0: 
C).(drop h (r k d) c0 e0))) (ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T 
u (lift h (r k d) v)))) (\lambda (v: T).(\lambda (e0: C).(drop (S i0) O 
(CHead x0 (Bind b) x1) (CHead e0 k v)))) (\lambda (_: T).(\lambda (e0: 
C).(drop h (r k d) c0 e0)))) (\lambda (x2: T).(\lambda (x3: C).(\lambda (H7: 
(eq T u (lift h (r k d) x2))).(\lambda (H8: (drop i0 O x0 (CHead x3 k 
x2))).(\lambda (H9: (drop h (r k d) c0 x3)).(ex3_2_intro T C (\lambda (v: 
T).(\lambda (_: C).(eq T u (lift h (r k d) v)))) (\lambda (v: T).(\lambda 
(e0: C).(drop (S i0) O (CHead x0 (Bind b) x1) (CHead e0 k v)))) (\lambda (_: 
T).(\lambda (e0: C).(drop h (r k d) c0 e0))) x2 x3 H7 (drop_drop (Bind b) i0 
x0 (CHead x3 k x2) H8 x1) H9)))))) H6)) e H3)))))) (drop_gen_skip_l c1 e t h 
(plus (S i0) d) (Bind b) H2))))))))) (\lambda (f: F).(\lambda (t: T).(\lambda 
(H1: (drop (S i0) O (CHead c1 (Flat f) t) (CHead c0 k u))).(\lambda (e: 
C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H2: (drop h (S (plus (S i0) 
d)) (CHead c1 (Flat f) t) e)).(ex3_2_ind C T (\lambda (e0: C).(\lambda (v: 
T).(eq C e (CHead e0 (Flat f) v)))) (\lambda (_: C).(\lambda (v: T).(eq T t 
(lift h (r (Flat f) (plus (S i0) d)) v)))) (\lambda (e0: C).(\lambda (_: 
T).(drop h (r (Flat f) (plus (S i0) d)) c1 e0))) (ex3_2 T C (\lambda (v: 
T).(\lambda (_: C).(eq T u (lift h (r k d) v)))) (\lambda (v: T).(\lambda 
(e0: C).(drop (S i0) O e (CHead e0 k v)))) (\lambda (_: T).(\lambda (e0: 
C).(drop h (r k d) c0 e0)))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H3: 
(eq C e (CHead x0 (Flat f) x1))).(\lambda (_: (eq T t (lift h (r (Flat f) 
(plus (S i0) d)) x1))).(\lambda (H5: (drop h (r (Flat f) (plus (S i0) d)) c1 
x0)).(eq_ind_r C (CHead x0 (Flat f) x1) (\lambda (c2: C).(ex3_2 T C (\lambda 
(v: T).(\lambda (_: C).(eq T u (lift h (r k d) v)))) (\lambda (v: T).(\lambda 
(e0: C).(drop (S i0) O c2 (CHead e0 k v)))) (\lambda (_: T).(\lambda (e0: 
C).(drop h (r k d) c0 e0))))) (ex3_2_ind T C (\lambda (v: T).(\lambda (_: 
C).(eq T u (lift h (r k d) v)))) (\lambda (v: T).(\lambda (e0: C).(drop (S 
i0) O x0 (CHead e0 k v)))) (\lambda (_: T).(\lambda (e0: C).(drop h (r k d) 
c0 e0))) (ex3_2 T C (\lambda (v: T).(\lambda (_: C).(eq T u (lift h (r k d) 
v)))) (\lambda (v: T).(\lambda (e0: C).(drop (S i0) O (CHead x0 (Flat f) x1) 
(CHead e0 k v)))) (\lambda (_: T).(\lambda (e0: C).(drop h (r k d) c0 e0)))) 
(\lambda (x2: T).(\lambda (x3: C).(\lambda (H6: (eq T u (lift h (r k d) 
x2))).(\lambda (H7: (drop (S i0) O x0 (CHead x3 k x2))).(\lambda (H8: (drop h 
(r k d) c0 x3)).(ex3_2_intro T C (\lambda (v: T).(\lambda (_: C).(eq T u 
(lift h (r k d) v)))) (\lambda (v: T).(\lambda (e0: C).(drop (S i0) O (CHead 
x0 (Flat f) x1) (CHead e0 k v)))) (\lambda (_: T).(\lambda (e0: C).(drop h (r 
k d) c0 e0))) x2 x3 H6 (drop_drop (Flat f) i0 x0 (CHead x3 k x2) H7 x1) 
H8)))))) (H0 (drop_gen_drop (Flat f) c1 (CHead c0 k u) t i0 H1) x0 h d H5)) e 
H3)))))) (drop_gen_skip_l c1 e t h (plus (S i0) d) (Flat f) H2))))))))) 
k0)))) c)))))) i)).
(* COMMENTS
Initial nodes: 2972
END *)

theorem drop_conf_ge:
 \forall (i: nat).(\forall (a: C).(\forall (c: C).((drop i O c a) \to 
(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) \to ((le 
(plus d h) i) \to (drop (minus i h) O e a)))))))))
\def
 \lambda (i: nat).(nat_ind (\lambda (n: nat).(\forall (a: C).(\forall (c: 
C).((drop n O c a) \to (\forall (e: C).(\forall (h: nat).(\forall (d: 
nat).((drop h d c e) \to ((le (plus d h) n) \to (drop (minus n h) O e 
a)))))))))) (\lambda (a: C).(\lambda (c: C).(\lambda (H: (drop O O c 
a)).(\lambda (e: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H0: (drop h 
d c e)).(\lambda (H1: (le (plus d h) O)).(let H2 \def (eq_ind C c (\lambda 
(c0: C).(drop h d c0 e)) H0 a (drop_gen_refl c a H)) in (let H_y \def 
(le_n_O_eq (plus d h) H1) in (land_ind (eq nat d O) (eq nat h O) (drop (minus 
O h) O e a) (\lambda (H3: (eq nat d O)).(\lambda (H4: (eq nat h O)).(let H5 
\def (eq_ind nat d (\lambda (n: nat).(drop h n a e)) H2 O H3) in (let H6 \def 
(eq_ind nat h (\lambda (n: nat).(drop n O a e)) H5 O H4) in (eq_ind_r nat O 
(\lambda (n: nat).(drop (minus O n) O e a)) (eq_ind C a (\lambda (c0: 
C).(drop (minus O O) O c0 a)) (drop_refl a) e (drop_gen_refl a e H6)) h 
H4))))) (plus_O d h (sym_eq nat O (plus d h) H_y))))))))))))) (\lambda (i0: 
nat).(\lambda (H: ((\forall (a: C).(\forall (c: C).((drop i0 O c a) \to 
(\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h d c e) \to ((le 
(plus d h) i0) \to (drop (minus i0 h) O e a))))))))))).(\lambda (a: 
C).(\lambda (c: C).(C_ind (\lambda (c0: C).((drop (S i0) O c0 a) \to (\forall 
(e: C).(\forall (h: nat).(\forall (d: nat).((drop h d c0 e) \to ((le (plus d 
h) (S i0)) \to (drop (minus (S i0) h) O e a)))))))) (\lambda (n: 
nat).(\lambda (H0: (drop (S i0) O (CSort n) a)).(\lambda (e: C).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H1: (drop h d (CSort n) e)).(\lambda (H2: 
(le (plus d h) (S i0))).(and3_ind (eq C e (CSort n)) (eq nat h O) (eq nat d 
O) (drop (minus (S i0) h) O e a) (\lambda (H3: (eq C e (CSort n))).(\lambda 
(H4: (eq nat h O)).(\lambda (H5: (eq nat d O)).(and3_ind (eq C a (CSort n)) 
(eq nat (S i0) O) (eq nat O O) (drop (minus (S i0) h) O e a) (\lambda (H6: 
(eq C a (CSort n))).(\lambda (H7: (eq nat (S i0) O)).(\lambda (_: (eq nat O 
O)).(let H9 \def (eq_ind nat d (\lambda (n0: nat).(le (plus n0 h) (S i0))) H2 
O H5) in (let H10 \def (eq_ind nat h (\lambda (n0: nat).(le (plus O n0) (S 
i0))) H9 O H4) in (eq_ind_r nat O (\lambda (n0: nat).(drop (minus (S i0) n0) 
O e a)) (eq_ind_r C (CSort n) (\lambda (c0: C).(drop (minus (S i0) O) O c0 
a)) (eq_ind_r C (CSort n) (\lambda (c0: C).(drop (minus (S i0) O) O (CSort n) 
c0)) (let H11 \def (eq_ind nat (S i0) (\lambda (ee: nat).(match ee in nat 
return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow 
True])) I O H7) in (False_ind (drop (minus (S i0) O) O (CSort n) (CSort n)) 
H11)) a H6) e H3) h H4)))))) (drop_gen_sort n (S i0) O a H0))))) 
(drop_gen_sort n h d e H1))))))))) (\lambda (c0: C).(\lambda (H0: (((drop (S 
i0) O c0 a) \to (\forall (e: C).(\forall (h: nat).(\forall (d: nat).((drop h 
d c0 e) \to ((le (plus d h) (S i0)) \to (drop (minus (S i0) h) O e 
a))))))))).(\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (t: T).((drop (S 
i0) O (CHead c0 k0 t) a) \to (\forall (e: C).(\forall (h: nat).(\forall (d: 
nat).((drop h d (CHead c0 k0 t) e) \to ((le (plus d h) (S i0)) \to (drop 
(minus (S i0) h) O e a))))))))) (\lambda (b: B).(\lambda (t: T).(\lambda (H1: 
(drop (S i0) O (CHead c0 (Bind b) t) a)).(\lambda (e: C).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H2: (drop h d (CHead c0 (Bind b) t) 
e)).(\lambda (H3: (le (plus d h) (S i0))).(nat_ind (\lambda (n: nat).((drop h 
n (CHead c0 (Bind b) t) e) \to ((le (plus n h) (S i0)) \to (drop (minus (S 
i0) h) O e a)))) (\lambda (H4: (drop h O (CHead c0 (Bind b) t) e)).(\lambda 
(H5: (le (plus O h) (S i0))).(nat_ind (\lambda (n: nat).((drop n O (CHead c0 
(Bind b) t) e) \to ((le (plus O n) (S i0)) \to (drop (minus (S i0) n) O e 
a)))) (\lambda (H6: (drop O O (CHead c0 (Bind b) t) e)).(\lambda (_: (le 
(plus O O) (S i0))).(eq_ind C (CHead c0 (Bind b) t) (\lambda (c1: C).(drop 
(minus (S i0) O) O c1 a)) (drop_drop (Bind b) i0 c0 a (drop_gen_drop (Bind b) 
c0 a t i0 H1) t) e (drop_gen_refl (CHead c0 (Bind b) t) e H6)))) (\lambda 
(h0: nat).(\lambda (_: (((drop h0 O (CHead c0 (Bind b) t) e) \to ((le (plus O 
h0) (S i0)) \to (drop (minus (S i0) h0) O e a))))).(\lambda (H6: (drop (S h0) 
O (CHead c0 (Bind b) t) e)).(\lambda (H7: (le (plus O (S h0)) (S i0))).(H a 
c0 (drop_gen_drop (Bind b) c0 a t i0 H1) e h0 O (drop_gen_drop (Bind b) c0 e 
t h0 H6) (le_S_n (plus O h0) i0 H7)))))) h H4 H5))) (\lambda (d0: 
nat).(\lambda (_: (((drop h d0 (CHead c0 (Bind b) t) e) \to ((le (plus d0 h) 
(S i0)) \to (drop (minus (S i0) h) O e a))))).(\lambda (H4: (drop h (S d0) 
(CHead c0 (Bind b) t) e)).(\lambda (H5: (le (plus (S d0) h) (S 
i0))).(ex3_2_ind C T (\lambda (e0: C).(\lambda (v: T).(eq C e (CHead e0 (Bind 
b) v)))) (\lambda (_: C).(\lambda (v: T).(eq T t (lift h (r (Bind b) d0) 
v)))) (\lambda (e0: C).(\lambda (_: T).(drop h (r (Bind b) d0) c0 e0))) (drop 
(minus (S i0) h) O e a) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: (eq C 
e (CHead x0 (Bind b) x1))).(\lambda (_: (eq T t (lift h (r (Bind b) d0) 
x1))).(\lambda (H8: (drop h (r (Bind b) d0) c0 x0)).(eq_ind_r C (CHead x0 
(Bind b) x1) (\lambda (c1: C).(drop (minus (S i0) h) O c1 a)) (eq_ind nat (S 
(minus i0 h)) (\lambda (n: nat).(drop n O (CHead x0 (Bind b) x1) a)) 
(drop_drop (Bind b) (minus i0 h) x0 a (H a c0 (drop_gen_drop (Bind b) c0 a t 
i0 H1) x0 h d0 H8 (le_S_n (plus d0 h) i0 H5)) x1) (minus (S i0) h) 
(minus_Sn_m i0 h (le_trans_plus_r d0 h i0 (le_S_n (plus d0 h) i0 H5)))) e 
H6)))))) (drop_gen_skip_l c0 e t h d0 (Bind b) H4)))))) d H2 H3))))))))) 
(\lambda (f: F).(\lambda (t: T).(\lambda (H1: (drop (S i0) O (CHead c0 (Flat 
f) t) a)).(\lambda (e: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H2: 
(drop h d (CHead c0 (Flat f) t) e)).(\lambda (H3: (le (plus d h) (S 
i0))).(nat_ind (\lambda (n: nat).((drop h n (CHead c0 (Flat f) t) e) \to ((le 
(plus n h) (S i0)) \to (drop (minus (S i0) h) O e a)))) (\lambda (H4: (drop h 
O (CHead c0 (Flat f) t) e)).(\lambda (H5: (le (plus O h) (S i0))).(nat_ind 
(\lambda (n: nat).((drop n O (CHead c0 (Flat f) t) e) \to ((le (plus O n) (S 
i0)) \to (drop (minus (S i0) n) O e a)))) (\lambda (H6: (drop O O (CHead c0 
(Flat f) t) e)).(\lambda (_: (le (plus O O) (S i0))).(eq_ind C (CHead c0 
(Flat f) t) (\lambda (c1: C).(drop (minus (S i0) O) O c1 a)) (drop_drop (Flat 
f) i0 c0 a (drop_gen_drop (Flat f) c0 a t i0 H1) t) e (drop_gen_refl (CHead 
c0 (Flat f) t) e H6)))) (\lambda (h0: nat).(\lambda (_: (((drop h0 O (CHead 
c0 (Flat f) t) e) \to ((le (plus O h0) (S i0)) \to (drop (minus (S i0) h0) O 
e a))))).(\lambda (H6: (drop (S h0) O (CHead c0 (Flat f) t) e)).(\lambda (H7: 
(le (plus O (S h0)) (S i0))).(H0 (drop_gen_drop (Flat f) c0 a t i0 H1) e (S 
h0) O (drop_gen_drop (Flat f) c0 e t h0 H6) H7))))) h H4 H5))) (\lambda (d0: 
nat).(\lambda (_: (((drop h d0 (CHead c0 (Flat f) t) e) \to ((le (plus d0 h) 
(S i0)) \to (drop (minus (S i0) h) O e a))))).(\lambda (H4: (drop h (S d0) 
(CHead c0 (Flat f) t) e)).(\lambda (H5: (le (plus (S d0) h) (S 
i0))).(ex3_2_ind C T (\lambda (e0: C).(\lambda (v: T).(eq C e (CHead e0 (Flat 
f) v)))) (\lambda (_: C).(\lambda (v: T).(eq T t (lift h (r (Flat f) d0) 
v)))) (\lambda (e0: C).(\lambda (_: T).(drop h (r (Flat f) d0) c0 e0))) (drop 
(minus (S i0) h) O e a) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: (eq C 
e (CHead x0 (Flat f) x1))).(\lambda (_: (eq T t (lift h (r (Flat f) d0) 
x1))).(\lambda (H8: (drop h (r (Flat f) d0) c0 x0)).(eq_ind_r C (CHead x0 
(Flat f) x1) (\lambda (c1: C).(drop (minus (S i0) h) O c1 a)) (let H9 \def 
(eq_ind_r nat (minus (S i0) h) (\lambda (n: nat).(drop n O x0 a)) (H0 
(drop_gen_drop (Flat f) c0 a t i0 H1) x0 h (S d0) H8 H5) (S (minus i0 h)) 
(minus_Sn_m i0 h (le_trans_plus_r d0 h i0 (le_S_n (plus d0 h) i0 H5)))) in 
(eq_ind nat (S (minus i0 h)) (\lambda (n: nat).(drop n O (CHead x0 (Flat f) 
x1) a)) (drop_drop (Flat f) (minus i0 h) x0 a H9 x1) (minus (S i0) h) 
(minus_Sn_m i0 h (le_trans_plus_r d0 h i0 (le_S_n (plus d0 h) i0 H5))))) e 
H6)))))) (drop_gen_skip_l c0 e t h d0 (Flat f) H4)))))) d H2 H3))))))))) 
k)))) c))))) i).
(* COMMENTS
Initial nodes: 2726
END *)

theorem drop_conf_rev:
 \forall (j: nat).(\forall (e1: C).(\forall (e2: C).((drop j O e1 e2) \to 
(\forall (c2: C).(\forall (i: nat).((drop i O c2 e2) \to (ex2 C (\lambda (c1: 
C).(drop j O c1 c2)) (\lambda (c1: C).(drop i j c1 e1)))))))))
\def
 \lambda (j: nat).(nat_ind (\lambda (n: nat).(\forall (e1: C).(\forall (e2: 
C).((drop n O e1 e2) \to (\forall (c2: C).(\forall (i: nat).((drop i O c2 e2) 
\to (ex2 C (\lambda (c1: C).(drop n O c1 c2)) (\lambda (c1: C).(drop i n c1 
e1)))))))))) (\lambda (e1: C).(\lambda (e2: C).(\lambda (H: (drop O O e1 
e2)).(\lambda (c2: C).(\lambda (i: nat).(\lambda (H0: (drop i O c2 e2)).(let 
H1 \def (eq_ind_r C e2 (\lambda (c: C).(drop i O c2 c)) H0 e1 (drop_gen_refl 
e1 e2 H)) in (ex_intro2 C (\lambda (c1: C).(drop O O c1 c2)) (\lambda (c1: 
C).(drop i O c1 e1)) c2 (drop_refl c2) H1)))))))) (\lambda (j0: nat).(\lambda 
(IHj: ((\forall (e1: C).(\forall (e2: C).((drop j0 O e1 e2) \to (\forall (c2: 
C).(\forall (i: nat).((drop i O c2 e2) \to (ex2 C (\lambda (c1: C).(drop j0 O 
c1 c2)) (\lambda (c1: C).(drop i j0 c1 e1))))))))))).(\lambda (e1: C).(C_ind 
(\lambda (c: C).(\forall (e2: C).((drop (S j0) O c e2) \to (\forall (c2: 
C).(\forall (i: nat).((drop i O c2 e2) \to (ex2 C (\lambda (c1: C).(drop (S 
j0) O c1 c2)) (\lambda (c1: C).(drop i (S j0) c1 c))))))))) (\lambda (n: 
nat).(\lambda (e2: C).(\lambda (H: (drop (S j0) O (CSort n) e2)).(\lambda 
(c2: C).(\lambda (i: nat).(\lambda (H0: (drop i O c2 e2)).(and3_ind (eq C e2 
(CSort n)) (eq nat (S j0) O) (eq nat O O) (ex2 C (\lambda (c1: C).(drop (S 
j0) O c1 c2)) (\lambda (c1: C).(drop i (S j0) c1 (CSort n)))) (\lambda (H1: 
(eq C e2 (CSort n))).(\lambda (H2: (eq nat (S j0) O)).(\lambda (_: (eq nat O 
O)).(let H4 \def (eq_ind C e2 (\lambda (c: C).(drop i O c2 c)) H0 (CSort n) 
H1) in (let H5 \def (eq_ind nat (S j0) (\lambda (ee: nat).(match ee in nat 
return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow 
True])) I O H2) in (False_ind (ex2 C (\lambda (c1: C).(drop (S j0) O c1 c2)) 
(\lambda (c1: C).(drop i (S j0) c1 (CSort n)))) H5)))))) (drop_gen_sort n (S 
j0) O e2 H)))))))) (\lambda (e2: C).(\lambda (IHe1: ((\forall (e3: C).((drop 
(S j0) O e2 e3) \to (\forall (c2: C).(\forall (i: nat).((drop i O c2 e3) \to 
(ex2 C (\lambda (c1: C).(drop (S j0) O c1 c2)) (\lambda (c1: C).(drop i (S 
j0) c1 e2)))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (e3: C).(\lambda 
(H: (drop (S j0) O (CHead e2 k t) e3)).(\lambda (c2: C).(\lambda (i: 
nat).(\lambda (H0: (drop i O c2 e3)).(K_ind (\lambda (k0: K).((drop (r k0 j0) 
O e2 e3) \to (ex2 C (\lambda (c1: C).(drop (S j0) O c1 c2)) (\lambda (c1: 
C).(drop i (S j0) c1 (CHead e2 k0 t)))))) (\lambda (b: B).(\lambda (H1: (drop 
(r (Bind b) j0) O e2 e3)).(let H_x \def (IHj e2 e3 H1 c2 i H0) in (let H2 
\def H_x in (ex2_ind C (\lambda (c1: C).(drop j0 O c1 c2)) (\lambda (c1: 
C).(drop i j0 c1 e2)) (ex2 C (\lambda (c1: C).(drop (S j0) O c1 c2)) (\lambda 
(c1: C).(drop i (S j0) c1 (CHead e2 (Bind b) t)))) (\lambda (x: C).(\lambda 
(H3: (drop j0 O x c2)).(\lambda (H4: (drop i j0 x e2)).(ex_intro2 C (\lambda 
(c1: C).(drop (S j0) O c1 c2)) (\lambda (c1: C).(drop i (S j0) c1 (CHead e2 
(Bind b) t))) (CHead x (Bind b) (lift i (r (Bind b) j0) t)) (drop_drop (Bind 
b) j0 x c2 H3 (lift i (r (Bind b) j0) t)) (drop_skip (Bind b) i j0 x e2 H4 
t))))) H2))))) (\lambda (f: F).(\lambda (H1: (drop (r (Flat f) j0) O e2 
e3)).(let H_x \def (IHe1 e3 H1 c2 i H0) in (let H2 \def H_x in (ex2_ind C 
(\lambda (c1: C).(drop (S j0) O c1 c2)) (\lambda (c1: C).(drop i (S j0) c1 
e2)) (ex2 C (\lambda (c1: C).(drop (S j0) O c1 c2)) (\lambda (c1: C).(drop i 
(S j0) c1 (CHead e2 (Flat f) t)))) (\lambda (x: C).(\lambda (H3: (drop (S j0) 
O x c2)).(\lambda (H4: (drop i (S j0) x e2)).(ex_intro2 C (\lambda (c1: 
C).(drop (S j0) O c1 c2)) (\lambda (c1: C).(drop i (S j0) c1 (CHead e2 (Flat 
f) t))) (CHead x (Flat f) (lift i (r (Flat f) j0) t)) (drop_drop (Flat f) j0 
x c2 H3 (lift i (r (Flat f) j0) t)) (drop_skip (Flat f) i j0 x e2 H4 t))))) 
H2))))) k (drop_gen_drop k e2 e3 t j0 H))))))))))) e1)))) j).
(* COMMENTS
Initial nodes: 1154
END *)

theorem drop_trans_le:
 \forall (i: nat).(\forall (d: nat).((le i d) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (h: nat).((drop h d c1 c2) \to (\forall (e2: C).((drop i O 
c2 e2) \to (ex2 C (\lambda (e1: C).(drop i O c1 e1)) (\lambda (e1: C).(drop h 
(minus d i) e1 e2)))))))))))
\def
 \lambda (i: nat).(nat_ind (\lambda (n: nat).(\forall (d: nat).((le n d) \to 
(\forall (c1: C).(\forall (c2: C).(\forall (h: nat).((drop h d c1 c2) \to 
(\forall (e2: C).((drop n O c2 e2) \to (ex2 C (\lambda (e1: C).(drop n O c1 
e1)) (\lambda (e1: C).(drop h (minus d n) e1 e2)))))))))))) (\lambda (d: 
nat).(\lambda (_: (le O d)).(\lambda (c1: C).(\lambda (c2: C).(\lambda (h: 
nat).(\lambda (H0: (drop h d c1 c2)).(\lambda (e2: C).(\lambda (H1: (drop O O 
c2 e2)).(let H2 \def (eq_ind C c2 (\lambda (c: C).(drop h d c1 c)) H0 e2 
(drop_gen_refl c2 e2 H1)) in (eq_ind nat d (\lambda (n: nat).(ex2 C (\lambda 
(e1: C).(drop O O c1 e1)) (\lambda (e1: C).(drop h n e1 e2)))) (ex_intro2 C 
(\lambda (e1: C).(drop O O c1 e1)) (\lambda (e1: C).(drop h d e1 e2)) c1 
(drop_refl c1) H2) (minus d O) (minus_n_O d))))))))))) (\lambda (i0: 
nat).(\lambda (IHi: ((\forall (d: nat).((le i0 d) \to (\forall (c1: 
C).(\forall (c2: C).(\forall (h: nat).((drop h d c1 c2) \to (\forall (e2: 
C).((drop i0 O c2 e2) \to (ex2 C (\lambda (e1: C).(drop i0 O c1 e1)) (\lambda 
(e1: C).(drop h (minus d i0) e1 e2))))))))))))).(\lambda (d: nat).(nat_ind 
(\lambda (n: nat).((le (S i0) n) \to (\forall (c1: C).(\forall (c2: 
C).(\forall (h: nat).((drop h n c1 c2) \to (\forall (e2: C).((drop (S i0) O 
c2 e2) \to (ex2 C (\lambda (e1: C).(drop (S i0) O c1 e1)) (\lambda (e1: 
C).(drop h (minus n (S i0)) e1 e2))))))))))) (\lambda (H: (le (S i0) 
O)).(\lambda (c1: C).(\lambda (c2: C).(\lambda (h: nat).(\lambda (_: (drop h 
O c1 c2)).(\lambda (e2: C).(\lambda (_: (drop (S i0) O c2 e2)).(ex2_ind nat 
(\lambda (n: nat).(eq nat O (S n))) (\lambda (n: nat).(le i0 n)) (ex2 C 
(\lambda (e1: C).(drop (S i0) O c1 e1)) (\lambda (e1: C).(drop h (minus O (S 
i0)) e1 e2))) (\lambda (x: nat).(\lambda (H2: (eq nat O (S x))).(\lambda (_: 
(le i0 x)).(let H4 \def (eq_ind nat O (\lambda (ee: nat).(match ee in nat 
return (\lambda (_: nat).Prop) with [O \Rightarrow True | (S _) \Rightarrow 
False])) I (S x) H2) in (False_ind (ex2 C (\lambda (e1: C).(drop (S i0) O c1 
e1)) (\lambda (e1: C).(drop h (minus O (S i0)) e1 e2))) H4))))) (le_gen_S i0 
O H))))))))) (\lambda (d0: nat).(\lambda (_: (((le (S i0) d0) \to (\forall 
(c1: C).(\forall (c2: C).(\forall (h: nat).((drop h d0 c1 c2) \to (\forall 
(e2: C).((drop (S i0) O c2 e2) \to (ex2 C (\lambda (e1: C).(drop (S i0) O c1 
e1)) (\lambda (e1: C).(drop h (minus d0 (S i0)) e1 e2)))))))))))).(\lambda 
(H: (le (S i0) (S d0))).(\lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: 
C).(\forall (h: nat).((drop h (S d0) c c2) \to (\forall (e2: C).((drop (S i0) 
O c2 e2) \to (ex2 C (\lambda (e1: C).(drop (S i0) O c e1)) (\lambda (e1: 
C).(drop h (minus (S d0) (S i0)) e1 e2))))))))) (\lambda (n: nat).(\lambda 
(c2: C).(\lambda (h: nat).(\lambda (H0: (drop h (S d0) (CSort n) 
c2)).(\lambda (e2: C).(\lambda (H1: (drop (S i0) O c2 e2)).(and3_ind (eq C c2 
(CSort n)) (eq nat h O) (eq nat (S d0) O) (ex2 C (\lambda (e1: C).(drop (S 
i0) O (CSort n) e1)) (\lambda (e1: C).(drop h (minus (S d0) (S i0)) e1 e2))) 
(\lambda (H2: (eq C c2 (CSort n))).(\lambda (_: (eq nat h O)).(\lambda (_: 
(eq nat (S d0) O)).(let H5 \def (eq_ind C c2 (\lambda (c: C).(drop (S i0) O c 
e2)) H1 (CSort n) H2) in (and3_ind (eq C e2 (CSort n)) (eq nat (S i0) O) (eq 
nat O O) (ex2 C (\lambda (e1: C).(drop (S i0) O (CSort n) e1)) (\lambda (e1: 
C).(drop h (minus (S d0) (S i0)) e1 e2))) (\lambda (H6: (eq C e2 (CSort 
n))).(\lambda (H7: (eq nat (S i0) O)).(\lambda (_: (eq nat O O)).(eq_ind_r C 
(CSort n) (\lambda (c: C).(ex2 C (\lambda (e1: C).(drop (S i0) O (CSort n) 
e1)) (\lambda (e1: C).(drop h (minus (S d0) (S i0)) e1 c)))) (let H9 \def 
(eq_ind nat (S i0) (\lambda (ee: nat).(match ee in nat return (\lambda (_: 
nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) I O H7) in 
(False_ind (ex2 C (\lambda (e1: C).(drop (S i0) O (CSort n) e1)) (\lambda 
(e1: C).(drop h (minus (S d0) (S i0)) e1 (CSort n)))) H9)) e2 H6)))) 
(drop_gen_sort n (S i0) O e2 H5)))))) (drop_gen_sort n h (S d0) c2 H0)))))))) 
(\lambda (c2: C).(\lambda (IHc: ((\forall (c3: C).(\forall (h: nat).((drop h 
(S d0) c2 c3) \to (\forall (e2: C).((drop (S i0) O c3 e2) \to (ex2 C (\lambda 
(e1: C).(drop (S i0) O c2 e1)) (\lambda (e1: C).(drop h (minus (S d0) (S i0)) 
e1 e2)))))))))).(\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (t: 
T).(\forall (c3: C).(\forall (h: nat).((drop h (S d0) (CHead c2 k0 t) c3) \to 
(\forall (e2: C).((drop (S i0) O c3 e2) \to (ex2 C (\lambda (e1: C).(drop (S 
i0) O (CHead c2 k0 t) e1)) (\lambda (e1: C).(drop h (minus (S d0) (S i0)) e1 
e2)))))))))) (\lambda (b: B).(\lambda (t: T).(\lambda (c3: C).(\lambda (h: 
nat).(\lambda (H0: (drop h (S d0) (CHead c2 (Bind b) t) c3)).(\lambda (e2: 
C).(\lambda (H1: (drop (S i0) O c3 e2)).(ex3_2_ind C T (\lambda (e: 
C).(\lambda (v: T).(eq C c3 (CHead e (Bind b) v)))) (\lambda (_: C).(\lambda 
(v: T).(eq T t (lift h (r (Bind b) d0) v)))) (\lambda (e: C).(\lambda (_: 
T).(drop h (r (Bind b) d0) c2 e))) (ex2 C (\lambda (e1: C).(drop (S i0) O 
(CHead c2 (Bind b) t) e1)) (\lambda (e1: C).(drop h (minus (S d0) (S i0)) e1 
e2))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H2: (eq C c3 (CHead x0 
(Bind b) x1))).(\lambda (H3: (eq T t (lift h (r (Bind b) d0) x1))).(\lambda 
(H4: (drop h (r (Bind b) d0) c2 x0)).(let H5 \def (eq_ind C c3 (\lambda (c: 
C).(drop (S i0) O c e2)) H1 (CHead x0 (Bind b) x1) H2) in (eq_ind_r T (lift h 
(r (Bind b) d0) x1) (\lambda (t0: T).(ex2 C (\lambda (e1: C).(drop (S i0) O 
(CHead c2 (Bind b) t0) e1)) (\lambda (e1: C).(drop h (minus (S d0) (S i0)) e1 
e2)))) (ex2_ind C (\lambda (e1: C).(drop i0 O c2 e1)) (\lambda (e1: C).(drop 
h (minus d0 i0) e1 e2)) (ex2 C (\lambda (e1: C).(drop (S i0) O (CHead c2 
(Bind b) (lift h (r (Bind b) d0) x1)) e1)) (\lambda (e1: C).(drop h (minus (S 
d0) (S i0)) e1 e2))) (\lambda (x: C).(\lambda (H6: (drop i0 O c2 x)).(\lambda 
(H7: (drop h (minus d0 i0) x e2)).(ex_intro2 C (\lambda (e1: C).(drop (S i0) 
O (CHead c2 (Bind b) (lift h (r (Bind b) d0) x1)) e1)) (\lambda (e1: C).(drop 
h (minus (S d0) (S i0)) e1 e2)) x (drop_drop (Bind b) i0 c2 x H6 (lift h (r 
(Bind b) d0) x1)) H7)))) (IHi d0 (le_S_n i0 d0 H) c2 x0 h H4 e2 
(drop_gen_drop (Bind b) x0 e2 x1 i0 H5))) t H3))))))) (drop_gen_skip_l c2 c3 
t h d0 (Bind b) H0))))))))) (\lambda (f: F).(\lambda (t: T).(\lambda (c3: 
C).(\lambda (h: nat).(\lambda (H0: (drop h (S d0) (CHead c2 (Flat f) t) 
c3)).(\lambda (e2: C).(\lambda (H1: (drop (S i0) O c3 e2)).(ex3_2_ind C T 
(\lambda (e: C).(\lambda (v: T).(eq C c3 (CHead e (Flat f) v)))) (\lambda (_: 
C).(\lambda (v: T).(eq T t (lift h (r (Flat f) d0) v)))) (\lambda (e: 
C).(\lambda (_: T).(drop h (r (Flat f) d0) c2 e))) (ex2 C (\lambda (e1: 
C).(drop (S i0) O (CHead c2 (Flat f) t) e1)) (\lambda (e1: C).(drop h (minus 
(S d0) (S i0)) e1 e2))) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H2: (eq C 
c3 (CHead x0 (Flat f) x1))).(\lambda (H3: (eq T t (lift h (r (Flat f) d0) 
x1))).(\lambda (H4: (drop h (r (Flat f) d0) c2 x0)).(let H5 \def (eq_ind C c3 
(\lambda (c: C).(drop (S i0) O c e2)) H1 (CHead x0 (Flat f) x1) H2) in 
(eq_ind_r T (lift h (r (Flat f) d0) x1) (\lambda (t0: T).(ex2 C (\lambda (e1: 
C).(drop (S i0) O (CHead c2 (Flat f) t0) e1)) (\lambda (e1: C).(drop h (minus 
(S d0) (S i0)) e1 e2)))) (ex2_ind C (\lambda (e1: C).(drop (S i0) O c2 e1)) 
(\lambda (e1: C).(drop h (minus (S d0) (S i0)) e1 e2)) (ex2 C (\lambda (e1: 
C).(drop (S i0) O (CHead c2 (Flat f) (lift h (r (Flat f) d0) x1)) e1)) 
(\lambda (e1: C).(drop h (minus (S d0) (S i0)) e1 e2))) (\lambda (x: 
C).(\lambda (H6: (drop (S i0) O c2 x)).(\lambda (H7: (drop h (minus (S d0) (S 
i0)) x e2)).(ex_intro2 C (\lambda (e1: C).(drop (S i0) O (CHead c2 (Flat f) 
(lift h (r (Flat f) d0) x1)) e1)) (\lambda (e1: C).(drop h (minus (S d0) (S 
i0)) e1 e2)) x (drop_drop (Flat f) i0 c2 x H6 (lift h (r (Flat f) d0) x1)) 
H7)))) (IHc x0 h H4 e2 (drop_gen_drop (Flat f) x0 e2 x1 i0 H5))) t H3))))))) 
(drop_gen_skip_l c2 c3 t h d0 (Flat f) H0))))))))) k)))) c1))))) d)))) i).
(* COMMENTS
Initial nodes: 2453
END *)

theorem drop_trans_ge:
 \forall (i: nat).(\forall (c1: C).(\forall (c2: C).(\forall (d: 
nat).(\forall (h: nat).((drop h d c1 c2) \to (\forall (e2: C).((drop i O c2 
e2) \to ((le d i) \to (drop (plus i h) O c1 e2)))))))))
\def
 \lambda (i: nat).(nat_ind (\lambda (n: nat).(\forall (c1: C).(\forall (c2: 
C).(\forall (d: nat).(\forall (h: nat).((drop h d c1 c2) \to (\forall (e2: 
C).((drop n O c2 e2) \to ((le d n) \to (drop (plus n h) O c1 e2)))))))))) 
(\lambda (c1: C).(\lambda (c2: C).(\lambda (d: nat).(\lambda (h: 
nat).(\lambda (H: (drop h d c1 c2)).(\lambda (e2: C).(\lambda (H0: (drop O O 
c2 e2)).(\lambda (H1: (le d O)).(eq_ind C c2 (\lambda (c: C).(drop (plus O h) 
O c1 c)) (let H_y \def (le_n_O_eq d H1) in (let H2 \def (eq_ind_r nat d 
(\lambda (n: nat).(drop h n c1 c2)) H O H_y) in H2)) e2 (drop_gen_refl c2 e2 
H0)))))))))) (\lambda (i0: nat).(\lambda (IHi: ((\forall (c1: C).(\forall 
(c2: C).(\forall (d: nat).(\forall (h: nat).((drop h d c1 c2) \to (\forall 
(e2: C).((drop i0 O c2 e2) \to ((le d i0) \to (drop (plus i0 h) O c1 
e2))))))))))).(\lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: 
C).(\forall (d: nat).(\forall (h: nat).((drop h d c c2) \to (\forall (e2: 
C).((drop (S i0) O c2 e2) \to ((le d (S i0)) \to (drop (plus (S i0) h) O c 
e2))))))))) (\lambda (n: nat).(\lambda (c2: C).(\lambda (d: nat).(\lambda (h: 
nat).(\lambda (H: (drop h d (CSort n) c2)).(\lambda (e2: C).(\lambda (H0: 
(drop (S i0) O c2 e2)).(\lambda (H1: (le d (S i0))).(and3_ind (eq C c2 (CSort 
n)) (eq nat h O) (eq nat d O) (drop (S (plus i0 h)) O (CSort n) e2) (\lambda 
(H2: (eq C c2 (CSort n))).(\lambda (H3: (eq nat h O)).(\lambda (H4: (eq nat d 
O)).(eq_ind_r nat O (\lambda (n0: nat).(drop (S (plus i0 n0)) O (CSort n) 
e2)) (let H5 \def (eq_ind nat d (\lambda (n0: nat).(le n0 (S i0))) H1 O H4) 
in (let H6 \def (eq_ind C c2 (\lambda (c: C).(drop (S i0) O c e2)) H0 (CSort 
n) H2) in (and3_ind (eq C e2 (CSort n)) (eq nat (S i0) O) (eq nat O O) (drop 
(S (plus i0 O)) O (CSort n) e2) (\lambda (H7: (eq C e2 (CSort n))).(\lambda 
(H8: (eq nat (S i0) O)).(\lambda (_: (eq nat O O)).(eq_ind_r C (CSort n) 
(\lambda (c: C).(drop (S (plus i0 O)) O (CSort n) c)) (let H10 \def (eq_ind 
nat (S i0) (\lambda (ee: nat).(match ee in nat return (\lambda (_: nat).Prop) 
with [O \Rightarrow False | (S _) \Rightarrow True])) I O H8) in (False_ind 
(drop (S (plus i0 O)) O (CSort n) (CSort n)) H10)) e2 H7)))) (drop_gen_sort n 
(S i0) O e2 H6)))) h H3)))) (drop_gen_sort n h d c2 H)))))))))) (\lambda (c2: 
C).(\lambda (IHc: ((\forall (c3: C).(\forall (d: nat).(\forall (h: 
nat).((drop h d c2 c3) \to (\forall (e2: C).((drop (S i0) O c3 e2) \to ((le d 
(S i0)) \to (drop (S (plus i0 h)) O c2 e2)))))))))).(\lambda (k: K).(\lambda 
(t: T).(\lambda (c3: C).(\lambda (d: nat).(nat_ind (\lambda (n: nat).(\forall 
(h: nat).((drop h n (CHead c2 k t) c3) \to (\forall (e2: C).((drop (S i0) O 
c3 e2) \to ((le n (S i0)) \to (drop (S (plus i0 h)) O (CHead c2 k t) 
e2))))))) (\lambda (h: nat).(nat_ind (\lambda (n: nat).((drop n O (CHead c2 k 
t) c3) \to (\forall (e2: C).((drop (S i0) O c3 e2) \to ((le O (S i0)) \to 
(drop (S (plus i0 n)) O (CHead c2 k t) e2)))))) (\lambda (H: (drop O O (CHead 
c2 k t) c3)).(\lambda (e2: C).(\lambda (H0: (drop (S i0) O c3 e2)).(\lambda 
(_: (le O (S i0))).(let H2 \def (eq_ind_r C c3 (\lambda (c: C).(drop (S i0) O 
c e2)) H0 (CHead c2 k t) (drop_gen_refl (CHead c2 k t) c3 H)) in (eq_ind nat 
i0 (\lambda (n: nat).(drop (S n) O (CHead c2 k t) e2)) (drop_drop k i0 c2 e2 
(drop_gen_drop k c2 e2 t i0 H2) t) (plus i0 O) (plus_n_O i0))))))) (\lambda 
(n: nat).(\lambda (_: (((drop n O (CHead c2 k t) c3) \to (\forall (e2: 
C).((drop (S i0) O c3 e2) \to ((le O (S i0)) \to (drop (S (plus i0 n)) O 
(CHead c2 k t) e2))))))).(\lambda (H0: (drop (S n) O (CHead c2 k t) 
c3)).(\lambda (e2: C).(\lambda (H1: (drop (S i0) O c3 e2)).(\lambda (H2: (le 
O (S i0))).(eq_ind nat (S (plus i0 n)) (\lambda (n0: nat).(drop (S n0) O 
(CHead c2 k t) e2)) (drop_drop k (S (plus i0 n)) c2 e2 (eq_ind_r nat (S (r k 
(plus i0 n))) (\lambda (n0: nat).(drop n0 O c2 e2)) (eq_ind_r nat (plus i0 (r 
k n)) (\lambda (n0: nat).(drop (S n0) O c2 e2)) (IHc c3 O (r k n) 
(drop_gen_drop k c2 c3 t n H0) e2 H1 H2) (r k (plus i0 n)) (r_plus_sym k i0 
n)) (r k (S (plus i0 n))) (r_S k (plus i0 n))) t) (plus i0 (S n)) (plus_n_Sm 
i0 n)))))))) h)) (\lambda (d0: nat).(\lambda (IHd: ((\forall (h: nat).((drop 
h d0 (CHead c2 k t) c3) \to (\forall (e2: C).((drop (S i0) O c3 e2) \to ((le 
d0 (S i0)) \to (drop (S (plus i0 h)) O (CHead c2 k t) e2)))))))).(\lambda (h: 
nat).(\lambda (H: (drop h (S d0) (CHead c2 k t) c3)).(\lambda (e2: 
C).(\lambda (H0: (drop (S i0) O c3 e2)).(\lambda (H1: (le (S d0) (S 
i0))).(ex3_2_ind C T (\lambda (e: C).(\lambda (v: T).(eq C c3 (CHead e k 
v)))) (\lambda (_: C).(\lambda (v: T).(eq T t (lift h (r k d0) v)))) (\lambda 
(e: C).(\lambda (_: T).(drop h (r k d0) c2 e))) (drop (S (plus i0 h)) O 
(CHead c2 k t) e2) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H2: (eq C c3 
(CHead x0 k x1))).(\lambda (H3: (eq T t (lift h (r k d0) x1))).(\lambda (H4: 
(drop h (r k d0) c2 x0)).(let H5 \def (eq_ind C c3 (\lambda (c: C).(\forall 
(h0: nat).((drop h0 d0 (CHead c2 k t) c) \to (\forall (e3: C).((drop (S i0) O 
c e3) \to ((le d0 (S i0)) \to (drop (S (plus i0 h0)) O (CHead c2 k t) 
e3))))))) IHd (CHead x0 k x1) H2) in (let H6 \def (eq_ind C c3 (\lambda (c: 
C).(drop (S i0) O c e2)) H0 (CHead x0 k x1) H2) in (let H7 \def (eq_ind T t 
(\lambda (t0: T).(\forall (h0: nat).((drop h0 d0 (CHead c2 k t0) (CHead x0 k 
x1)) \to (\forall (e3: C).((drop (S i0) O (CHead x0 k x1) e3) \to ((le d0 (S 
i0)) \to (drop (S (plus i0 h0)) O (CHead c2 k t0) e3))))))) H5 (lift h (r k 
d0) x1) H3) in (eq_ind_r T (lift h (r k d0) x1) (\lambda (t0: T).(drop (S 
(plus i0 h)) O (CHead c2 k t0) e2)) (drop_drop k (plus i0 h) c2 e2 (K_ind 
(\lambda (k0: K).((drop h (r k0 d0) c2 x0) \to ((drop (r k0 i0) O x0 e2) \to 
(drop (r k0 (plus i0 h)) O c2 e2)))) (\lambda (b: B).(\lambda (H8: (drop h (r 
(Bind b) d0) c2 x0)).(\lambda (H9: (drop (r (Bind b) i0) O x0 e2)).(IHi c2 x0 
(r (Bind b) d0) h H8 e2 H9 (le_S_n (r (Bind b) d0) i0 H1))))) (\lambda (f: 
F).(\lambda (H8: (drop h (r (Flat f) d0) c2 x0)).(\lambda (H9: (drop (r (Flat 
f) i0) O x0 e2)).(IHc x0 (r (Flat f) d0) h H8 e2 H9 H1)))) k H4 
(drop_gen_drop k x0 e2 x1 i0 H6)) (lift h (r k d0) x1)) t H3))))))))) 
(drop_gen_skip_l c2 c3 t h d0 k H))))))))) d))))))) c1)))) i).
(* COMMENTS
Initial nodes: 2020
END *)

