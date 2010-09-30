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

include "Basic-1/clear/fwd.ma".

include "Basic-1/drop/fwd.ma".

theorem drop_clear:
 \forall (c1: C).(\forall (c2: C).(\forall (i: nat).((drop (S i) O c1 c2) \to 
(ex2_3 B C T (\lambda (b: B).(\lambda (e: C).(\lambda (v: T).(clear c1 (CHead 
e (Bind b) v))))) (\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop i O e 
c2))))))))
\def
 \lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: C).(\forall (i: 
nat).((drop (S i) O c c2) \to (ex2_3 B C T (\lambda (b: B).(\lambda (e: 
C).(\lambda (v: T).(clear c (CHead e (Bind b) v))))) (\lambda (_: B).(\lambda 
(e: C).(\lambda (_: T).(drop i O e c2))))))))) (\lambda (n: nat).(\lambda 
(c2: C).(\lambda (i: nat).(\lambda (H: (drop (S i) O (CSort n) c2)).(and3_ind 
(eq C c2 (CSort n)) (eq nat (S i) O) (eq nat O O) (ex2_3 B C T (\lambda (b: 
B).(\lambda (e: C).(\lambda (v: T).(clear (CSort n) (CHead e (Bind b) v))))) 
(\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop i O e c2))))) (\lambda 
(_: (eq C c2 (CSort n))).(\lambda (H1: (eq nat (S i) O)).(\lambda (_: (eq nat 
O O)).(let H3 \def (eq_ind nat (S i) (\lambda (ee: nat).(match ee in nat 
return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow 
True])) I O H1) in (False_ind (ex2_3 B C T (\lambda (b: B).(\lambda (e: 
C).(\lambda (v: T).(clear (CSort n) (CHead e (Bind b) v))))) (\lambda (_: 
B).(\lambda (e: C).(\lambda (_: T).(drop i O e c2))))) H3))))) (drop_gen_sort 
n (S i) O c2 H)))))) (\lambda (c: C).(\lambda (H: ((\forall (c2: C).(\forall 
(i: nat).((drop (S i) O c c2) \to (ex2_3 B C T (\lambda (b: B).(\lambda (e: 
C).(\lambda (v: T).(clear c (CHead e (Bind b) v))))) (\lambda (_: B).(\lambda 
(e: C).(\lambda (_: T).(drop i O e c2)))))))))).(\lambda (k: K).(\lambda (t: 
T).(\lambda (c2: C).(\lambda (i: nat).(\lambda (H0: (drop (S i) O (CHead c k 
t) c2)).(K_ind (\lambda (k0: K).((drop (r k0 i) O c c2) \to (ex2_3 B C T 
(\lambda (b: B).(\lambda (e: C).(\lambda (v: T).(clear (CHead c k0 t) (CHead 
e (Bind b) v))))) (\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop i O e 
c2))))))) (\lambda (b: B).(\lambda (H1: (drop (r (Bind b) i) O c 
c2)).(ex2_3_intro B C T (\lambda (b0: B).(\lambda (e: C).(\lambda (v: 
T).(clear (CHead c (Bind b) t) (CHead e (Bind b0) v))))) (\lambda (_: 
B).(\lambda (e: C).(\lambda (_: T).(drop i O e c2)))) b c t (clear_bind b c 
t) H1))) (\lambda (f: F).(\lambda (H1: (drop (r (Flat f) i) O c c2)).(let H2 
\def (H c2 i H1) in (ex2_3_ind B C T (\lambda (b: B).(\lambda (e: C).(\lambda 
(v: T).(clear c (CHead e (Bind b) v))))) (\lambda (_: B).(\lambda (e: 
C).(\lambda (_: T).(drop i O e c2)))) (ex2_3 B C T (\lambda (b: B).(\lambda 
(e: C).(\lambda (v: T).(clear (CHead c (Flat f) t) (CHead e (Bind b) v))))) 
(\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop i O e c2))))) (\lambda 
(x0: B).(\lambda (x1: C).(\lambda (x2: T).(\lambda (H3: (clear c (CHead x1 
(Bind x0) x2))).(\lambda (H4: (drop i O x1 c2)).(ex2_3_intro B C T (\lambda 
(b: B).(\lambda (e: C).(\lambda (v: T).(clear (CHead c (Flat f) t) (CHead e 
(Bind b) v))))) (\lambda (_: B).(\lambda (e: C).(\lambda (_: T).(drop i O e 
c2)))) x0 x1 x2 (clear_flat c (CHead x1 (Bind x0) x2) H3 f t) H4)))))) H2)))) 
k (drop_gen_drop k c c2 t i H0))))))))) c1).
(* COMMENTS
Initial nodes: 770
END *)

theorem drop_clear_O:
 \forall (b: B).(\forall (c: C).(\forall (e1: C).(\forall (u: T).((clear c 
(CHead e1 (Bind b) u)) \to (\forall (e2: C).(\forall (i: nat).((drop i O e1 
e2) \to (drop (S i) O c e2))))))))
\def
 \lambda (b: B).(\lambda (c: C).(C_ind (\lambda (c0: C).(\forall (e1: 
C).(\forall (u: T).((clear c0 (CHead e1 (Bind b) u)) \to (\forall (e2: 
C).(\forall (i: nat).((drop i O e1 e2) \to (drop (S i) O c0 e2)))))))) 
(\lambda (n: nat).(\lambda (e1: C).(\lambda (u: T).(\lambda (H: (clear (CSort 
n) (CHead e1 (Bind b) u))).(\lambda (e2: C).(\lambda (i: nat).(\lambda (_: 
(drop i O e1 e2)).(clear_gen_sort (CHead e1 (Bind b) u) n H (drop (S i) O 
(CSort n) e2))))))))) (\lambda (c0: C).(\lambda (H: ((\forall (e1: 
C).(\forall (u: T).((clear c0 (CHead e1 (Bind b) u)) \to (\forall (e2: 
C).(\forall (i: nat).((drop i O e1 e2) \to (drop (S i) O c0 
e2))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (e1: C).(\lambda (u: 
T).(\lambda (H0: (clear (CHead c0 k t) (CHead e1 (Bind b) u))).(\lambda (e2: 
C).(\lambda (i: nat).(\lambda (H1: (drop i O e1 e2)).(K_ind (\lambda (k0: 
K).((clear (CHead c0 k0 t) (CHead e1 (Bind b) u)) \to (drop (S i) O (CHead c0 
k0 t) e2))) (\lambda (b0: B).(\lambda (H2: (clear (CHead c0 (Bind b0) t) 
(CHead e1 (Bind b) u))).(let H3 \def (f_equal C C (\lambda (e: C).(match e in 
C return (\lambda (_: C).C) with [(CSort _) \Rightarrow e1 | (CHead c1 _ _) 
\Rightarrow c1])) (CHead e1 (Bind b) u) (CHead c0 (Bind b0) t) 
(clear_gen_bind b0 c0 (CHead e1 (Bind b) u) t H2)) in ((let H4 \def (f_equal 
C B (\lambda (e: C).(match e in C return (\lambda (_: C).B) with [(CSort _) 
\Rightarrow b | (CHead _ k0 _) \Rightarrow (match k0 in K return (\lambda (_: 
K).B) with [(Bind b1) \Rightarrow b1 | (Flat _) \Rightarrow b])])) (CHead e1 
(Bind b) u) (CHead c0 (Bind b0) t) (clear_gen_bind b0 c0 (CHead e1 (Bind b) 
u) t H2)) in ((let H5 \def (f_equal C T (\lambda (e: C).(match e in C return 
(\lambda (_: C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow 
t0])) (CHead e1 (Bind b) u) (CHead c0 (Bind b0) t) (clear_gen_bind b0 c0 
(CHead e1 (Bind b) u) t H2)) in (\lambda (H6: (eq B b b0)).(\lambda (H7: (eq 
C e1 c0)).(let H8 \def (eq_ind C e1 (\lambda (c1: C).(drop i O c1 e2)) H1 c0 
H7) in (eq_ind B b (\lambda (b1: B).(drop (S i) O (CHead c0 (Bind b1) t) e2)) 
(drop_drop (Bind b) i c0 e2 H8 t) b0 H6))))) H4)) H3)))) (\lambda (f: 
F).(\lambda (H2: (clear (CHead c0 (Flat f) t) (CHead e1 (Bind b) 
u))).(drop_drop (Flat f) i c0 e2 (H e1 u (clear_gen_flat f c0 (CHead e1 (Bind 
b) u) t H2) e2 i H1) t))) k H0))))))))))) c)).
(* COMMENTS
Initial nodes: 619
END *)

theorem drop_clear_S:
 \forall (x2: C).(\forall (x1: C).(\forall (h: nat).(\forall (d: nat).((drop 
h (S d) x1 x2) \to (\forall (b: B).(\forall (c2: C).(\forall (u: T).((clear 
x2 (CHead c2 (Bind b) u)) \to (ex2 C (\lambda (c1: C).(clear x1 (CHead c1 
(Bind b) (lift h d u)))) (\lambda (c1: C).(drop h d c1 c2)))))))))))
\def
 \lambda (x2: C).(C_ind (\lambda (c: C).(\forall (x1: C).(\forall (h: 
nat).(\forall (d: nat).((drop h (S d) x1 c) \to (\forall (b: B).(\forall (c2: 
C).(\forall (u: T).((clear c (CHead c2 (Bind b) u)) \to (ex2 C (\lambda (c1: 
C).(clear x1 (CHead c1 (Bind b) (lift h d u)))) (\lambda (c1: C).(drop h d c1 
c2)))))))))))) (\lambda (n: nat).(\lambda (x1: C).(\lambda (h: nat).(\lambda 
(d: nat).(\lambda (_: (drop h (S d) x1 (CSort n))).(\lambda (b: B).(\lambda 
(c2: C).(\lambda (u: T).(\lambda (H0: (clear (CSort n) (CHead c2 (Bind b) 
u))).(clear_gen_sort (CHead c2 (Bind b) u) n H0 (ex2 C (\lambda (c1: 
C).(clear x1 (CHead c1 (Bind b) (lift h d u)))) (\lambda (c1: C).(drop h d c1 
c2))))))))))))) (\lambda (c: C).(\lambda (H: ((\forall (x1: C).(\forall (h: 
nat).(\forall (d: nat).((drop h (S d) x1 c) \to (\forall (b: B).(\forall (c2: 
C).(\forall (u: T).((clear c (CHead c2 (Bind b) u)) \to (ex2 C (\lambda (c1: 
C).(clear x1 (CHead c1 (Bind b) (lift h d u)))) (\lambda (c1: C).(drop h d c1 
c2))))))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (x1: C).(\lambda (h: 
nat).(\lambda (d: nat).(\lambda (H0: (drop h (S d) x1 (CHead c k 
t))).(\lambda (b: B).(\lambda (c2: C).(\lambda (u: T).(\lambda (H1: (clear 
(CHead c k t) (CHead c2 (Bind b) u))).(ex2_ind C (\lambda (e: C).(eq C x1 
(CHead e k (lift h (r k d) t)))) (\lambda (e: C).(drop h (r k d) e c)) (ex2 C 
(\lambda (c1: C).(clear x1 (CHead c1 (Bind b) (lift h d u)))) (\lambda (c1: 
C).(drop h d c1 c2))) (\lambda (x: C).(\lambda (H2: (eq C x1 (CHead x k (lift 
h (r k d) t)))).(\lambda (H3: (drop h (r k d) x c)).(eq_ind_r C (CHead x k 
(lift h (r k d) t)) (\lambda (c0: C).(ex2 C (\lambda (c1: C).(clear c0 (CHead 
c1 (Bind b) (lift h d u)))) (\lambda (c1: C).(drop h d c1 c2)))) (K_ind 
(\lambda (k0: K).((clear (CHead c k0 t) (CHead c2 (Bind b) u)) \to ((drop h 
(r k0 d) x c) \to (ex2 C (\lambda (c1: C).(clear (CHead x k0 (lift h (r k0 d) 
t)) (CHead c1 (Bind b) (lift h d u)))) (\lambda (c1: C).(drop h d c1 c2)))))) 
(\lambda (b0: B).(\lambda (H4: (clear (CHead c (Bind b0) t) (CHead c2 (Bind 
b) u))).(\lambda (H5: (drop h (r (Bind b0) d) x c)).(let H6 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow c2 | (CHead c0 _ _) \Rightarrow c0])) (CHead c2 (Bind b) u) 
(CHead c (Bind b0) t) (clear_gen_bind b0 c (CHead c2 (Bind b) u) t H4)) in 
((let H7 \def (f_equal C B (\lambda (e: C).(match e in C return (\lambda (_: 
C).B) with [(CSort _) \Rightarrow b | (CHead _ k0 _) \Rightarrow (match k0 in 
K return (\lambda (_: K).B) with [(Bind b1) \Rightarrow b1 | (Flat _) 
\Rightarrow b])])) (CHead c2 (Bind b) u) (CHead c (Bind b0) t) 
(clear_gen_bind b0 c (CHead c2 (Bind b) u) t H4)) in ((let H8 \def (f_equal C 
T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) (CHead c2 (Bind b) u) (CHead 
c (Bind b0) t) (clear_gen_bind b0 c (CHead c2 (Bind b) u) t H4)) in (\lambda 
(H9: (eq B b b0)).(\lambda (H10: (eq C c2 c)).(eq_ind_r T t (\lambda (t0: 
T).(ex2 C (\lambda (c1: C).(clear (CHead x (Bind b0) (lift h (r (Bind b0) d) 
t)) (CHead c1 (Bind b) (lift h d t0)))) (\lambda (c1: C).(drop h d c1 c2)))) 
(eq_ind_r C c (\lambda (c0: C).(ex2 C (\lambda (c1: C).(clear (CHead x (Bind 
b0) (lift h (r (Bind b0) d) t)) (CHead c1 (Bind b) (lift h d t)))) (\lambda 
(c1: C).(drop h d c1 c0)))) (eq_ind_r B b0 (\lambda (b1: B).(ex2 C (\lambda 
(c1: C).(clear (CHead x (Bind b0) (lift h (r (Bind b0) d) t)) (CHead c1 (Bind 
b1) (lift h d t)))) (\lambda (c1: C).(drop h d c1 c)))) (ex_intro2 C (\lambda 
(c1: C).(clear (CHead x (Bind b0) (lift h (r (Bind b0) d) t)) (CHead c1 (Bind 
b0) (lift h d t)))) (\lambda (c1: C).(drop h d c1 c)) x (clear_bind b0 x 
(lift h d t)) H5) b H9) c2 H10) u H8)))) H7)) H6))))) (\lambda (f: 
F).(\lambda (H4: (clear (CHead c (Flat f) t) (CHead c2 (Bind b) u))).(\lambda 
(H5: (drop h (r (Flat f) d) x c)).(let H6 \def (H x h d H5 b c2 u 
(clear_gen_flat f c (CHead c2 (Bind b) u) t H4)) in (ex2_ind C (\lambda (c1: 
C).(clear x (CHead c1 (Bind b) (lift h d u)))) (\lambda (c1: C).(drop h d c1 
c2)) (ex2 C (\lambda (c1: C).(clear (CHead x (Flat f) (lift h (r (Flat f) d) 
t)) (CHead c1 (Bind b) (lift h d u)))) (\lambda (c1: C).(drop h d c1 c2))) 
(\lambda (x0: C).(\lambda (H7: (clear x (CHead x0 (Bind b) (lift h d 
u)))).(\lambda (H8: (drop h d x0 c2)).(ex_intro2 C (\lambda (c1: C).(clear 
(CHead x (Flat f) (lift h (r (Flat f) d) t)) (CHead c1 (Bind b) (lift h d 
u)))) (\lambda (c1: C).(drop h d c1 c2)) x0 (clear_flat x (CHead x0 (Bind b) 
(lift h d u)) H7 f (lift h (r (Flat f) d) t)) H8)))) H6))))) k H1 H3) x1 
H2)))) (drop_gen_skip_r c x1 t h d k H0)))))))))))))) x2).
(* COMMENTS
Initial nodes: 1449
END *)

