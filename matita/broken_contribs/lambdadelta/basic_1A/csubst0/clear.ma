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

include "basic_1A/csubst0/props.ma".

include "basic_1A/csubst0/fwd.ma".

include "basic_1A/clear/fwd.ma".

lemma csubst0_clear_O:
 \forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 O v c1 c2) \to 
(\forall (c: C).((clear c1 c) \to (clear c2 c))))))
\def
 \lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: C).(\forall (v: 
T).((csubst0 O v c c2) \to (\forall (c0: C).((clear c c0) \to (clear c2 
c0))))))) (\lambda (n: nat).(\lambda (c2: C).(\lambda (v: T).(\lambda (H: 
(csubst0 O v (CSort n) c2)).(\lambda (c: C).(\lambda (_: (clear (CSort n) 
c)).(csubst0_gen_sort c2 v O n H (clear c2 c)))))))) (\lambda (c: C).(\lambda 
(H: ((\forall (c2: C).(\forall (v: T).((csubst0 O v c c2) \to (\forall (c0: 
C).((clear c c0) \to (clear c2 c0)))))))).(\lambda (k: K).(\lambda (t: 
T).(\lambda (c2: C).(\lambda (v: T).(\lambda (H0: (csubst0 O v (CHead c k t) 
c2)).(\lambda (c0: C).(\lambda (H1: (clear (CHead c k t) c0)).(let H2 \def 
(csubst0_gen_head k c c2 t v O H0) in (or3_ind (ex3_2 T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat O (s k j)))) (\lambda (u2: T).(\lambda (_: 
nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j 
v t u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat O (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c c3)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat O (s k j))))) (\lambda (u2: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3))))) (clear c2 c0) 
(\lambda (H3: (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat O (s k 
j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda 
(u2: T).(\lambda (j: nat).(subst0 j v t u2))))).(ex3_2_ind T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat O (s k j)))) (\lambda (u2: T).(\lambda (_: 
nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j 
v t u2))) (clear c2 c0) (\lambda (x0: T).(\lambda (x1: nat).(\lambda (H4: (eq 
nat O (s k x1))).(\lambda (H5: (eq C c2 (CHead c k x0))).(\lambda (H6: 
(subst0 x1 v t x0)).(eq_ind_r C (CHead c k x0) (\lambda (c3: C).(clear c3 
c0)) (K_ind (\lambda (k0: K).((clear (CHead c k0 t) c0) \to ((eq nat O (s k0 
x1)) \to (clear (CHead c k0 x0) c0)))) (\lambda (b: B).(\lambda (_: (clear 
(CHead c (Bind b) t) c0)).(\lambda (H8: (eq nat O (s (Bind b) x1))).(let H9 
\def (eq_ind nat O (\lambda (ee: nat).(match ee with [O \Rightarrow True | (S 
_) \Rightarrow False])) I (S x1) H8) in (False_ind (clear (CHead c (Bind b) 
x0) c0) H9))))) (\lambda (f: F).(\lambda (H7: (clear (CHead c (Flat f) t) 
c0)).(\lambda (H8: (eq nat O (s (Flat f) x1))).(let H9 \def (eq_ind_r nat x1 
(\lambda (n: nat).(subst0 n v t x0)) H6 O H8) in (clear_flat c c0 
(clear_gen_flat f c c0 t H7) f x0))))) k H1 H4) c2 H5)))))) H3)) (\lambda 
(H3: (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat O (s k j)))) 
(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c c3))))).(ex3_2_ind C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat O (s k j)))) (\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j 
v c c3))) (clear c2 c0) (\lambda (x0: C).(\lambda (x1: nat).(\lambda (H4: (eq 
nat O (s k x1))).(\lambda (H5: (eq C c2 (CHead x0 k t))).(\lambda (H6: 
(csubst0 x1 v c x0)).(eq_ind_r C (CHead x0 k t) (\lambda (c3: C).(clear c3 
c0)) (K_ind (\lambda (k0: K).((clear (CHead c k0 t) c0) \to ((eq nat O (s k0 
x1)) \to (clear (CHead x0 k0 t) c0)))) (\lambda (b: B).(\lambda (_: (clear 
(CHead c (Bind b) t) c0)).(\lambda (H8: (eq nat O (s (Bind b) x1))).(let H9 
\def (eq_ind nat O (\lambda (ee: nat).(match ee with [O \Rightarrow True | (S 
_) \Rightarrow False])) I (S x1) H8) in (False_ind (clear (CHead x0 (Bind b) 
t) c0) H9))))) (\lambda (f: F).(\lambda (H7: (clear (CHead c (Flat f) t) 
c0)).(\lambda (H8: (eq nat O (s (Flat f) x1))).(let H9 \def (eq_ind_r nat x1 
(\lambda (n: nat).(csubst0 n v c x0)) H6 O H8) in (clear_flat x0 c0 (H x0 v 
H9 c0 (clear_gen_flat f c c0 t H7)) f t))))) k H1 H4) c2 H5)))))) H3)) 
(\lambda (H3: (ex4_3 T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat O (s k j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda 
(j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c c3)))))).(ex4_3_ind T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat O (s k j))))) (\lambda (u2: T).(\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda 
(_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c c3)))) (clear c2 c0) (\lambda (x0: 
T).(\lambda (x1: C).(\lambda (x2: nat).(\lambda (H4: (eq nat O (s k 
x2))).(\lambda (H5: (eq C c2 (CHead x1 k x0))).(\lambda (H6: (subst0 x2 v t 
x0)).(\lambda (H7: (csubst0 x2 v c x1)).(eq_ind_r C (CHead x1 k x0) (\lambda 
(c3: C).(clear c3 c0)) (K_ind (\lambda (k0: K).((clear (CHead c k0 t) c0) \to 
((eq nat O (s k0 x2)) \to (clear (CHead x1 k0 x0) c0)))) (\lambda (b: 
B).(\lambda (_: (clear (CHead c (Bind b) t) c0)).(\lambda (H9: (eq nat O (s 
(Bind b) x2))).(let H10 \def (eq_ind nat O (\lambda (ee: nat).(match ee with 
[O \Rightarrow True | (S _) \Rightarrow False])) I (S x2) H9) in (False_ind 
(clear (CHead x1 (Bind b) x0) c0) H10))))) (\lambda (f: F).(\lambda (H8: 
(clear (CHead c (Flat f) t) c0)).(\lambda (H9: (eq nat O (s (Flat f) 
x2))).(let H10 \def (eq_ind_r nat x2 (\lambda (n: nat).(csubst0 n v c x1)) H7 
O H9) in (let H11 \def (eq_ind_r nat x2 (\lambda (n: nat).(subst0 n v t x0)) 
H6 O H9) in (clear_flat x1 c0 (H x1 v H10 c0 (clear_gen_flat f c c0 t H8)) f 
x0)))))) k H1 H4) c2 H5)))))))) H3)) H2))))))))))) c1).

lemma csubst0_clear_O_back:
 \forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 O v c1 c2) \to 
(\forall (c: C).((clear c2 c) \to (clear c1 c))))))
\def
 \lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: C).(\forall (v: 
T).((csubst0 O v c c2) \to (\forall (c0: C).((clear c2 c0) \to (clear c 
c0))))))) (\lambda (n: nat).(\lambda (c2: C).(\lambda (v: T).(\lambda (H: 
(csubst0 O v (CSort n) c2)).(\lambda (c: C).(\lambda (_: (clear c2 
c)).(csubst0_gen_sort c2 v O n H (clear (CSort n) c)))))))) (\lambda (c: 
C).(\lambda (H: ((\forall (c2: C).(\forall (v: T).((csubst0 O v c c2) \to 
(\forall (c0: C).((clear c2 c0) \to (clear c c0)))))))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (c2: C).(\lambda (v: T).(\lambda (H0: (csubst0 O 
v (CHead c k t) c2)).(\lambda (c0: C).(\lambda (H1: (clear c2 c0)).(let H2 
\def (csubst0_gen_head k c c2 t v O H0) in (or3_ind (ex3_2 T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat O (s k j)))) (\lambda (u2: T).(\lambda (_: 
nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j 
v t u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat O (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c c3)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat O (s k j))))) (\lambda (u2: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3))))) (clear (CHead c 
k t) c0) (\lambda (H3: (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat 
O (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) 
(\lambda (u2: T).(\lambda (j: nat).(subst0 j v t u2))))).(ex3_2_ind T nat 
(\lambda (_: T).(\lambda (j: nat).(eq nat O (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v t u2))) (clear (CHead c k t) c0) (\lambda (x0: T).(\lambda 
(x1: nat).(\lambda (H4: (eq nat O (s k x1))).(\lambda (H5: (eq C c2 (CHead c 
k x0))).(\lambda (H6: (subst0 x1 v t x0)).(let H7 \def (eq_ind C c2 (\lambda 
(c3: C).(clear c3 c0)) H1 (CHead c k x0) H5) in (K_ind (\lambda (k0: K).((eq 
nat O (s k0 x1)) \to ((clear (CHead c k0 x0) c0) \to (clear (CHead c k0 t) 
c0)))) (\lambda (b: B).(\lambda (H8: (eq nat O (s (Bind b) x1))).(\lambda (_: 
(clear (CHead c (Bind b) x0) c0)).(let H10 \def (eq_ind nat O (\lambda (ee: 
nat).(match ee with [O \Rightarrow True | (S _) \Rightarrow False])) I (S x1) 
H8) in (False_ind (clear (CHead c (Bind b) t) c0) H10))))) (\lambda (f: 
F).(\lambda (H8: (eq nat O (s (Flat f) x1))).(\lambda (H9: (clear (CHead c 
(Flat f) x0) c0)).(let H10 \def (eq_ind_r nat x1 (\lambda (n: nat).(subst0 n 
v t x0)) H6 O H8) in (clear_flat c c0 (clear_gen_flat f c c0 x0 H9) f t))))) 
k H4 H7))))))) H3)) (\lambda (H3: (ex3_2 C nat (\lambda (_: C).(\lambda (j: 
nat).(eq nat O (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead 
c3 k t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c 
c3))))).(ex3_2_ind C nat (\lambda (_: C).(\lambda (j: nat).(eq nat O (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c c3))) (clear (CHead c k t) c0) 
(\lambda (x0: C).(\lambda (x1: nat).(\lambda (H4: (eq nat O (s k 
x1))).(\lambda (H5: (eq C c2 (CHead x0 k t))).(\lambda (H6: (csubst0 x1 v c 
x0)).(let H7 \def (eq_ind C c2 (\lambda (c3: C).(clear c3 c0)) H1 (CHead x0 k 
t) H5) in (K_ind (\lambda (k0: K).((eq nat O (s k0 x1)) \to ((clear (CHead x0 
k0 t) c0) \to (clear (CHead c k0 t) c0)))) (\lambda (b: B).(\lambda (H8: (eq 
nat O (s (Bind b) x1))).(\lambda (_: (clear (CHead x0 (Bind b) t) c0)).(let 
H10 \def (eq_ind nat O (\lambda (ee: nat).(match ee with [O \Rightarrow True 
| (S _) \Rightarrow False])) I (S x1) H8) in (False_ind (clear (CHead c (Bind 
b) t) c0) H10))))) (\lambda (f: F).(\lambda (H8: (eq nat O (s (Flat f) 
x1))).(\lambda (H9: (clear (CHead x0 (Flat f) t) c0)).(let H10 \def (eq_ind_r 
nat x1 (\lambda (n: nat).(csubst0 n v c x0)) H6 O H8) in (clear_flat c c0 (H 
x0 v H10 c0 (clear_gen_flat f x0 c0 t H9)) f t))))) k H4 H7))))))) H3)) 
(\lambda (H3: (ex4_3 T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat O (s k j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda 
(j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c c3)))))).(ex4_3_ind T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat O (s k j))))) (\lambda (u2: T).(\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda 
(_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c c3)))) (clear (CHead c k t) c0) (\lambda 
(x0: T).(\lambda (x1: C).(\lambda (x2: nat).(\lambda (H4: (eq nat O (s k 
x2))).(\lambda (H5: (eq C c2 (CHead x1 k x0))).(\lambda (H6: (subst0 x2 v t 
x0)).(\lambda (H7: (csubst0 x2 v c x1)).(let H8 \def (eq_ind C c2 (\lambda 
(c3: C).(clear c3 c0)) H1 (CHead x1 k x0) H5) in (K_ind (\lambda (k0: K).((eq 
nat O (s k0 x2)) \to ((clear (CHead x1 k0 x0) c0) \to (clear (CHead c k0 t) 
c0)))) (\lambda (b: B).(\lambda (H9: (eq nat O (s (Bind b) x2))).(\lambda (_: 
(clear (CHead x1 (Bind b) x0) c0)).(let H11 \def (eq_ind nat O (\lambda (ee: 
nat).(match ee with [O \Rightarrow True | (S _) \Rightarrow False])) I (S x2) 
H9) in (False_ind (clear (CHead c (Bind b) t) c0) H11))))) (\lambda (f: 
F).(\lambda (H9: (eq nat O (s (Flat f) x2))).(\lambda (H10: (clear (CHead x1 
(Flat f) x0) c0)).(let H11 \def (eq_ind_r nat x2 (\lambda (n: nat).(csubst0 n 
v c x1)) H7 O H9) in (let H12 \def (eq_ind_r nat x2 (\lambda (n: nat).(subst0 
n v t x0)) H6 O H9) in (clear_flat c c0 (H x1 v H11 c0 (clear_gen_flat f x1 
c0 x0 H10)) f t)))))) k H4 H8))))))))) H3)) H2))))))))))) c1).

lemma csubst0_clear_S:
 \forall (c1: C).(\forall (c2: C).(\forall (v: T).(\forall (i: nat).((csubst0 
(S i) v c1 c2) \to (\forall (c: C).((clear c1 c) \to (or4 (clear c2 c) (ex3_4 
B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq 
C c (CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: 
T).(\lambda (u2: T).(clear c2 (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear c2 (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c (CHead e1 (Bind b) u1))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear c2 (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 i v e1 e2))))))))))))))
\def
 \lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: C).(\forall (v: 
T).(\forall (i: nat).((csubst0 (S i) v c c2) \to (\forall (c0: C).((clear c 
c0) \to (or4 (clear c2 c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear c2 
(CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear c2 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))))))))))) (\lambda (n: nat).(\lambda (c2: C).(\lambda (v: T).(\lambda 
(i: nat).(\lambda (H: (csubst0 (S i) v (CSort n) c2)).(\lambda (c: 
C).(\lambda (_: (clear (CSort n) c)).(csubst0_gen_sort c2 v (S i) n H (or4 
(clear c2 c) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e (Bind 
b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear c2 
(CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e2 (Bind b) u2))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2)))))))))))))))) 
(\lambda (c: C).(\lambda (H: ((\forall (c2: C).(\forall (v: T).(\forall (i: 
nat).((csubst0 (S i) v c c2) \to (\forall (c0: C).((clear c c0) \to (or4 
(clear c2 c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e (Bind 
b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear c2 
(CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e2 (Bind b) u2))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))))))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c2: C).(\lambda 
(v: T).(\lambda (i: nat).(\lambda (H0: (csubst0 (S i) v (CHead c k t) 
c2)).(\lambda (c0: C).(\lambda (H1: (clear (CHead c k t) c0)).(let H2 \def 
(csubst0_gen_head k c c2 t v (S i) H0) in (or3_ind (ex3_2 T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat (S i) (s k j)))) (\lambda (u2: T).(\lambda (_: 
nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j 
v t u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat (S i) (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c c3)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat (S i) (s k j))))) (\lambda (u2: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3))))) (or4 (clear c2 
c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: 
C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e (Bind b) u2)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v 
u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear c2 (CHead e2 (Bind 
b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind 
b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(clear c2 (CHead e2 (Bind b) u2))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 i v e1 e2)))))))) (\lambda (H3: (ex3_2 T nat 
(\lambda (_: T).(\lambda (j: nat).(eq nat (S i) (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v t u2))))).(ex3_2_ind T nat (\lambda (_: T).(\lambda (j: 
nat).(eq nat (S i) (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 
(CHead c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v t u2))) (or4 
(clear c2 c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e (Bind 
b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear c2 
(CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e2 (Bind b) u2))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2)))))))) (\lambda 
(x0: T).(\lambda (x1: nat).(\lambda (H4: (eq nat (S i) (s k x1))).(\lambda 
(H5: (eq C c2 (CHead c k x0))).(\lambda (H6: (subst0 x1 v t x0)).(eq_ind_r C 
(CHead c k x0) (\lambda (c3: C).(or4 (clear c3 c0) (ex3_4 B C T T (\lambda 
(b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e 
(Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda 
(u2: T).(clear c3 (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear c3 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
c3 (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
i v e1 e2))))))))) (K_ind (\lambda (k0: K).((clear (CHead c k0 t) c0) \to 
((eq nat (S i) (s k0 x1)) \to (or4 (clear (CHead c k0 x0) c0) (ex3_4 B C T T 
(\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: 
T).(\lambda (u2: T).(clear (CHead c k0 x0) (CHead e (Bind b) u2)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v 
u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead c k0 x0) 
(CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead c k0 x0) (CHead e2 (Bind b) 
u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))))))) (\lambda (b: B).(\lambda (H7: (clear (CHead c (Bind b) t) 
c0)).(\lambda (H8: (eq nat (S i) (s (Bind b) x1))).(let H9 \def (f_equal nat 
nat (\lambda (e: nat).(match e with [O \Rightarrow i | (S n) \Rightarrow n])) 
(S i) (S x1) H8) in (let H10 \def (eq_ind_r nat x1 (\lambda (n: nat).(subst0 
n v t x0)) H6 i H9) in (eq_ind_r C (CHead c (Bind b) t) (\lambda (c3: C).(or4 
(clear (CHead c (Bind b) x0) c3) (ex3_4 B C T T (\lambda (b0: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c3 (CHead e (Bind b0) u1)))))) 
(\lambda (b0: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead c (Bind b) x0) (CHead e (Bind b0) u2)))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C 
T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c3 
(CHead e1 (Bind b0) u)))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead c (Bind b) x0) (CHead e2 (Bind b0) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c3 (CHead e1 (Bind b0) u1))))))) 
(\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead c (Bind b) x0) (CHead e2 (Bind b0) u2))))))) (\lambda 
(_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))))) (or4_intro1 
(clear (CHead c (Bind b) x0) (CHead c (Bind b) t)) (ex3_4 B C T T (\lambda 
(b0: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead c (Bind 
b) t) (CHead e (Bind b0) u1)))))) (\lambda (b0: B).(\lambda (e: C).(\lambda 
(_: T).(\lambda (u2: T).(clear (CHead c (Bind b) x0) (CHead e (Bind b0) 
u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b0: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead c (Bind b) t) (CHead e1 (Bind 
b0) u)))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear (CHead c (Bind b) x0) (CHead e2 (Bind b0) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C (CHead c (Bind b) t) (CHead e1 (Bind b0) 
u1))))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(clear (CHead c (Bind b) x0) (CHead e2 (Bind b0) 
u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))) 
(ex3_4_intro B C T T (\lambda (b0: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C (CHead c (Bind b) t) (CHead e (Bind b0) u1)))))) 
(\lambda (b0: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead c (Bind b) x0) (CHead e (Bind b0) u2)))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2))))) b c t x0 
(refl_equal C (CHead c (Bind b) t)) (clear_bind b c x0) H10)) c0 
(clear_gen_bind b c c0 t H7))))))) (\lambda (f: F).(\lambda (H7: (clear 
(CHead c (Flat f) t) c0)).(\lambda (H8: (eq nat (S i) (s (Flat f) x1))).(let 
H9 \def (f_equal nat nat (\lambda (e: nat).e) (S i) (s (Flat f) x1) H8) in 
(let H10 \def (eq_ind_r nat x1 (\lambda (n: nat).(subst0 n v t x0)) H6 (S i) 
H9) in (or4_intro0 (clear (CHead c (Flat f) x0) c0) (ex3_4 B C T T (\lambda 
(b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e 
(Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead c (Flat f) x0) (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead c (Flat f) x0) (CHead e2 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(clear (CHead c (Flat f) x0) (CHead e2 (Bind b) 
u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))) 
(clear_flat c c0 (clear_gen_flat f c c0 t H7) f x0))))))) k H1 H4) c2 
H5)))))) H3)) (\lambda (H3: (ex3_2 C nat (\lambda (_: C).(\lambda (j: 
nat).(eq nat (S i) (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 
(CHead c3 k t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c 
c3))))).(ex3_2_ind C nat (\lambda (_: C).(\lambda (j: nat).(eq nat (S i) (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c c3))) (or4 (clear c2 c0) (ex3_4 B C 
T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: 
T).(\lambda (u2: T).(clear c2 (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear c2 (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear c2 (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 i v e1 e2)))))))) (\lambda (x0: C).(\lambda (x1: 
nat).(\lambda (H4: (eq nat (S i) (s k x1))).(\lambda (H5: (eq C c2 (CHead x0 
k t))).(\lambda (H6: (csubst0 x1 v c x0)).(eq_ind_r C (CHead x0 k t) (\lambda 
(c3: C).(or4 (clear c3 c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear c3 
(CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear c3 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear c3 (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))))) (K_ind (\lambda (k0: K).((clear (CHead c k0 t) c0) \to ((eq nat 
(S i) (s k0 x1)) \to (or4 (clear (CHead x0 k0 t) c0) (ex3_4 B C T T (\lambda 
(b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e 
(Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x0 k0 t) (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x0 k0 t) (CHead e2 (Bind b) 
u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind 
b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(clear (CHead x0 k0 t) (CHead e2 (Bind b) u2))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))))))) 
(\lambda (b: B).(\lambda (H7: (clear (CHead c (Bind b) t) c0)).(\lambda (H8: 
(eq nat (S i) (s (Bind b) x1))).(let H9 \def (f_equal nat nat (\lambda (e: 
nat).(match e with [O \Rightarrow i | (S n) \Rightarrow n])) (S i) (S x1) H8) 
in (let H10 \def (eq_ind_r nat x1 (\lambda (n: nat).(csubst0 n v c x0)) H6 i 
H9) in (eq_ind_r C (CHead c (Bind b) t) (\lambda (c3: C).(or4 (clear (CHead 
x0 (Bind b) t) c3) (ex3_4 B C T T (\lambda (b0: B).(\lambda (e: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C c3 (CHead e (Bind b0) u1)))))) (\lambda (b0: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x0 (Bind b) 
t) (CHead e (Bind b0) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b0: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c3 (CHead e1 (Bind 
b0) u)))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear (CHead x0 (Bind b) t) (CHead e2 (Bind b0) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C c3 (CHead e1 (Bind b0) u1))))))) (\lambda (b0: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x0 (Bind b) t) (CHead e2 (Bind b0) u2))))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 
u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 i v e1 e2))))))))) (or4_intro2 (clear (CHead x0 
(Bind b) t) (CHead c (Bind b) t)) (ex3_4 B C T T (\lambda (b0: B).(\lambda 
(e: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead c (Bind b) t) (CHead e 
(Bind b0) u1)))))) (\lambda (b0: B).(\lambda (e: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x0 (Bind b) t) (CHead e (Bind b0) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C (CHead c (Bind b) t) (CHead e1 (Bind b0) u)))))) (\lambda (b0: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x0 (Bind b) 
t) (CHead e2 (Bind b0) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b0: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C 
(CHead c (Bind b) t) (CHead e1 (Bind b0) u1))))))) (\lambda (b0: B).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x0 
(Bind b) t) (CHead e2 (Bind b0) u2))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 i v e1 e2))))))) (ex3_4_intro B C C T (\lambda (b0: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead c (Bind b) 
t) (CHead e1 (Bind b0) u)))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x0 (Bind b) t) (CHead e2 (Bind b0) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2))))) b c x0 t (refl_equal C (CHead c (Bind b) t)) (clear_bind b x0 t) 
H10)) c0 (clear_gen_bind b c c0 t H7))))))) (\lambda (f: F).(\lambda (H7: 
(clear (CHead c (Flat f) t) c0)).(\lambda (H8: (eq nat (S i) (s (Flat f) 
x1))).(let H9 \def (f_equal nat nat (\lambda (e: nat).e) (S i) (s (Flat f) 
x1) H8) in (let H10 \def (eq_ind_r nat x1 (\lambda (n: nat).(csubst0 n v c 
x0)) H6 (S i) H9) in (let H11 \def (H x0 v i H10 c0 (clear_gen_flat f c c0 t 
H7)) in (or4_ind (clear x0 c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear x0 
(CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear x0 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear x0 (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))) (or4 (clear (CHead x0 (Flat f) t) c0) (ex3_4 B C T T (\lambda (b: 
B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind 
b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: 
T).(clear (CHead x0 (Flat f) t) (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x0 (Flat f) t) (CHead e2 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(clear (CHead x0 (Flat f) t) (CHead e2 (Bind b) 
u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))))) (\lambda (H12: (clear x0 c0)).(or4_intro0 (clear (CHead x0 (Flat 
f) t) c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x0 (Flat f) 
t) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear (CHead x0 (Flat f) t) (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x0 (Flat f) t) (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 
u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 i v e1 e2))))))) (clear_flat x0 c0 H12 f t))) 
(\lambda (H12: (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear x0 (CHead e (Bind 
b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2))))))).(ex3_4_ind B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear x0 
(CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2))))) (or4 (clear (CHead x0 (Flat f) t) 
c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x0 (Flat f) t) (CHead e 
(Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear 
(CHead x0 (Flat f) t) (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C 
C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x0 (Flat f) t) (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 
u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 i v e1 e2)))))))) (\lambda (x2: B).(\lambda (x3: 
C).(\lambda (x4: T).(\lambda (x5: T).(\lambda (H13: (eq C c0 (CHead x3 (Bind 
x2) x4))).(\lambda (H14: (clear x0 (CHead x3 (Bind x2) x5))).(\lambda (H15: 
(subst0 i v x4 x5)).(or4_intro1 (clear (CHead x0 (Flat f) t) c0) (ex3_4 B C T 
T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: 
T).(\lambda (u2: T).(clear (CHead x0 (Flat f) t) (CHead e (Bind b) u2)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v 
u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x0 (Flat f) 
t) (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x0 (Flat f) t) (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))) (ex3_4_intro B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x0 (Flat f) 
t) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2))))) x2 x3 x4 x5 H13 (clear_flat x0 
(CHead x3 (Bind x2) x5) H14 f t) H15))))))))) H12)) (\lambda (H12: (ex3_4 B C 
C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear x0 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 
e2))))))).(ex3_4_ind B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear x0 (CHead e2 (Bind 
b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 i v e1 e2))))) (or4 (clear (CHead x0 (Flat f) t) c0) (ex3_4 B C T 
T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: 
T).(\lambda (u2: T).(clear (CHead x0 (Flat f) t) (CHead e (Bind b) u2)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v 
u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x0 (Flat f) 
t) (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x0 (Flat f) t) (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))))) (\lambda (x2: B).(\lambda (x3: C).(\lambda (x4: C).(\lambda (x5: 
T).(\lambda (H13: (eq C c0 (CHead x3 (Bind x2) x5))).(\lambda (H14: (clear x0 
(CHead x4 (Bind x2) x5))).(\lambda (H15: (csubst0 i v x3 x4)).(or4_intro2 
(clear (CHead x0 (Flat f) t) c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x0 (Flat f) t) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x0 (Flat f) t) (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x0 (Flat f) t) (CHead e2 (Bind b) u2))))))) (\lambda 
(_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))) (ex3_4_intro B C 
C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x0 (Flat f) t) (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2))))) x2 x3 x4 x5 H13 (clear_flat x0 (CHead x4 (Bind x2) x5) H14 f t) 
H15))))))))) H12)) (\lambda (H12: (ex4_5 B C C T T (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(clear x0 (CHead e2 (Bind b) u2))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 i v e1 e2)))))))).(ex4_5_ind B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear x0 (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))) (or4 (clear (CHead x0 (Flat f) t) c0) (ex3_4 B C T T (\lambda (b: 
B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind 
b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: 
T).(clear (CHead x0 (Flat f) t) (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x0 (Flat f) t) (CHead e2 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(clear (CHead x0 (Flat f) t) (CHead e2 (Bind b) 
u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))))) (\lambda (x2: B).(\lambda (x3: C).(\lambda (x4: C).(\lambda (x5: 
T).(\lambda (x6: T).(\lambda (H13: (eq C c0 (CHead x3 (Bind x2) 
x5))).(\lambda (H14: (clear x0 (CHead x4 (Bind x2) x6))).(\lambda (H15: 
(subst0 i v x5 x6)).(\lambda (H16: (csubst0 i v x3 x4)).(or4_intro3 (clear 
(CHead x0 (Flat f) t) c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x0 (Flat f) t) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x0 (Flat f) t) (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x0 (Flat f) t) (CHead e2 (Bind b) u2))))))) (\lambda 
(_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))) (ex4_5_intro B C 
C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x0 (Flat f) t) (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 
u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 i v e1 e2)))))) x2 x3 x4 x5 x6 H13 (clear_flat x0 
(CHead x4 (Bind x2) x6) H14 f t) H15 H16))))))))))) H12)) H11))))))) k H1 H4) 
c2 H5)))))) H3)) (\lambda (H3: (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (S i) (s k j))))) (\lambda (u2: T).(\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda 
(_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c c3)))))).(ex4_3_ind T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat (S i) (s k j))))) (\lambda (u2: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3)))) (or4 (clear c2 
c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: 
C).(\lambda (_: T).(\lambda (u2: T).(clear c2 (CHead e (Bind b) u2)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v 
u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear c2 (CHead e2 (Bind 
b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind 
b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(clear c2 (CHead e2 (Bind b) u2))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 i v e1 e2)))))))) (\lambda (x0: T).(\lambda 
(x1: C).(\lambda (x2: nat).(\lambda (H4: (eq nat (S i) (s k x2))).(\lambda 
(H5: (eq C c2 (CHead x1 k x0))).(\lambda (H6: (subst0 x2 v t x0)).(\lambda 
(H7: (csubst0 x2 v c x1)).(eq_ind_r C (CHead x1 k x0) (\lambda (c3: C).(or4 
(clear c3 c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear c3 (CHead e (Bind 
b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear c3 
(CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear c3 (CHead e2 (Bind b) u2))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))))) (K_ind 
(\lambda (k0: K).((clear (CHead c k0 t) c0) \to ((eq nat (S i) (s k0 x2)) \to 
(or4 (clear (CHead x1 k0 x0) c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x1 k0 x0) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x1 k0 x0) (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x1 k0 x0) (CHead e2 (Bind b) u2))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))))))) (\lambda (b: B).(\lambda 
(H8: (clear (CHead c (Bind b) t) c0)).(\lambda (H9: (eq nat (S i) (s (Bind b) 
x2))).(let H10 \def (f_equal nat nat (\lambda (e: nat).(match e with [O 
\Rightarrow i | (S n) \Rightarrow n])) (S i) (S x2) H9) in (let H11 \def 
(eq_ind_r nat x2 (\lambda (n: nat).(csubst0 n v c x1)) H7 i H10) in (let H12 
\def (eq_ind_r nat x2 (\lambda (n: nat).(subst0 n v t x0)) H6 i H10) in 
(eq_ind_r C (CHead c (Bind b) t) (\lambda (c3: C).(or4 (clear (CHead x1 (Bind 
b) x0) c3) (ex3_4 B C T T (\lambda (b0: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c3 (CHead e (Bind b0) u1)))))) (\lambda (b0: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x1 (Bind b) 
x0) (CHead e (Bind b0) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b0: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c3 (CHead e1 (Bind 
b0) u)))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear (CHead x1 (Bind b) x0) (CHead e2 (Bind b0) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C c3 (CHead e1 (Bind b0) u1))))))) (\lambda (b0: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x1 (Bind b) x0) (CHead e2 (Bind b0) u2))))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 
u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 i v e1 e2))))))))) (or4_intro3 (clear (CHead x1 
(Bind b) x0) (CHead c (Bind b) t)) (ex3_4 B C T T (\lambda (b0: B).(\lambda 
(e: C).(\lambda (u1: T).(\lambda (_: T).(eq C (CHead c (Bind b) t) (CHead e 
(Bind b0) u1)))))) (\lambda (b0: B).(\lambda (e: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x1 (Bind b) x0) (CHead e (Bind b0) u2)))))) (\lambda 
(_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 
u2)))))) (ex3_4 B C C T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C (CHead c (Bind b) t) (CHead e1 (Bind b0) u)))))) 
(\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear 
(CHead x1 (Bind b) x0) (CHead e2 (Bind b0) u)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C 
C T T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C (CHead c (Bind b) t) (CHead e1 (Bind b0) u1))))))) 
(\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x1 (Bind b) x0) (CHead e2 (Bind b0) u2))))))) (\lambda 
(_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))) (ex4_5_intro B C 
C T T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C (CHead c (Bind b) t) (CHead e1 (Bind b0) u1))))))) 
(\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x1 (Bind b) x0) (CHead e2 (Bind b0) u2))))))) (\lambda 
(_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2)))))) b c x1 t x0 
(refl_equal C (CHead c (Bind b) t)) (clear_bind b x1 x0) H12 H11)) c0 
(clear_gen_bind b c c0 t H8)))))))) (\lambda (f: F).(\lambda (H8: (clear 
(CHead c (Flat f) t) c0)).(\lambda (H9: (eq nat (S i) (s (Flat f) x2))).(let 
H10 \def (f_equal nat nat (\lambda (e: nat).e) (S i) (s (Flat f) x2) H9) in 
(let H11 \def (eq_ind_r nat x2 (\lambda (n: nat).(csubst0 n v c x1)) H7 (S i) 
H10) in (let H12 \def (eq_ind_r nat x2 (\lambda (n: nat).(subst0 n v t x0)) 
H6 (S i) H10) in (let H13 \def (H x1 v i H11 c0 (clear_gen_flat f c c0 t H8)) 
in (or4_ind (clear x1 c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear x1 
(CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear x1 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear x1 (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))) (or4 (clear (CHead x1 (Flat f) x0) c0) (ex3_4 B C T T (\lambda (b: 
B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind 
b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: 
T).(clear (CHead x1 (Flat f) x0) (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x1 (Flat f) x0) (CHead e2 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(clear (CHead x1 (Flat f) x0) (CHead e2 (Bind b) 
u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))))) (\lambda (H14: (clear x1 c0)).(or4_intro0 (clear (CHead x1 (Flat 
f) x0) c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x1 (Flat f) 
x0) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear (CHead x1 (Flat f) x0) (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x1 (Flat f) x0) (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 
u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 i v e1 e2))))))) (clear_flat x1 c0 H14 f x0))) 
(\lambda (H14: (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear x1 (CHead e (Bind 
b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2))))))).(ex3_4_ind B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear x1 
(CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2))))) (or4 (clear (CHead x1 (Flat f) x0) 
c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x1 (Flat f) x0) (CHead e 
(Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear 
(CHead x1 (Flat f) x0) (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C 
C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x1 (Flat f) x0) (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 
u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 i v e1 e2)))))))) (\lambda (x3: B).(\lambda (x4: 
C).(\lambda (x5: T).(\lambda (x6: T).(\lambda (H15: (eq C c0 (CHead x4 (Bind 
x3) x5))).(\lambda (H16: (clear x1 (CHead x4 (Bind x3) x6))).(\lambda (H17: 
(subst0 i v x5 x6)).(or4_intro1 (clear (CHead x1 (Flat f) x0) c0) (ex3_4 B C 
T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: 
T).(\lambda (u2: T).(clear (CHead x1 (Flat f) x0) (CHead e (Bind b) u2)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v 
u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x1 (Flat f) 
x0) (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x1 (Flat f) x0) (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2))))))) (ex3_4_intro B C T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x1 (Flat f) 
x0) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2))))) x3 x4 x5 x6 H15 (clear_flat x1 
(CHead x4 (Bind x3) x6) H16 f x0) H17))))))))) H14)) (\lambda (H14: (ex3_4 B 
C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C 
c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear x1 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v e1 
e2))))))).(ex3_4_ind B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear x1 (CHead e2 (Bind 
b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 i v e1 e2))))) (or4 (clear (CHead x1 (Flat f) x0) c0) (ex3_4 B C 
T T (\lambda (b: B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e (Bind b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: 
T).(\lambda (u2: T).(clear (CHead x1 (Flat f) x0) (CHead e (Bind b) u2)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v 
u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x1 (Flat f) 
x0) (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear (CHead x1 (Flat f) x0) (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))))) (\lambda (x3: B).(\lambda (x4: C).(\lambda (x5: C).(\lambda (x6: 
T).(\lambda (H15: (eq C c0 (CHead x4 (Bind x3) x6))).(\lambda (H16: (clear x1 
(CHead x5 (Bind x3) x6))).(\lambda (H17: (csubst0 i v x4 x5)).(or4_intro2 
(clear (CHead x1 (Flat f) x0) c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x1 (Flat f) x0) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C 
T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x1 (Flat f) x0) (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x1 (Flat f) x0) (CHead e2 (Bind b) u2))))))) (\lambda 
(_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))) (ex3_4_intro B C 
C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x1 (Flat f) x0) (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2))))) x3 x4 x5 x6 H15 (clear_flat x1 (CHead x5 (Bind x3) x6) H16 f x0) 
H17))))))))) H14)) (\lambda (H14: (ex4_5 B C C T T (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(clear x1 (CHead e2 (Bind b) u2))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 i v e1 e2)))))))).(ex4_5_ind B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear x1 (CHead e2 
(Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))) (or4 (clear (CHead x1 (Flat f) x0) c0) (ex3_4 B C T T (\lambda (b: 
B).(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind 
b) u1)))))) (\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: 
T).(clear (CHead x1 (Flat f) x0) (CHead e (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) 
(ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(clear (CHead x1 (Flat f) x0) (CHead e2 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 i v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 
(Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(clear (CHead x1 (Flat f) x0) (CHead e2 (Bind b) 
u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 
e2)))))))) (\lambda (x3: B).(\lambda (x4: C).(\lambda (x5: C).(\lambda (x6: 
T).(\lambda (x7: T).(\lambda (H15: (eq C c0 (CHead x4 (Bind x3) 
x6))).(\lambda (H16: (clear x1 (CHead x5 (Bind x3) x7))).(\lambda (H17: 
(subst0 i v x6 x7)).(\lambda (H18: (csubst0 i v x4 x5)).(or4_intro3 (clear 
(CHead x1 (Flat f) x0) c0) (ex3_4 B C T T (\lambda (b: B).(\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x1 (Flat f) x0) (CHead e (Bind b) u2)))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 u2)))))) (ex3_4 B C C 
T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(clear (CHead x1 (Flat f) x0) (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(clear (CHead x1 (Flat f) x0) (CHead e2 (Bind b) u2))))))) (\lambda 
(_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 i v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v e1 e2))))))) (ex4_5_intro B C 
C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C c0 (CHead e1 (Bind b) u1))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
(CHead x1 (Flat f) x0) (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v u1 
u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 i v e1 e2)))))) x3 x4 x5 x6 x7 H15 (clear_flat x1 
(CHead x5 (Bind x3) x7) H16 f x0) H17 H18))))))))))) H14)) H13)))))))) k H1 
H4) c2 H5)))))))) H3)) H2)))))))))))) c1).

lemma csubst0_clear_trans:
 \forall (c1: C).(\forall (c2: C).(\forall (v: T).(\forall (i: nat).((csubst0 
i v c1 c2) \to (\forall (e2: C).((clear c2 e2) \to (or (clear c1 e2) (ex2 C 
(\lambda (e1: C).(csubst0 i v e1 e2)) (\lambda (e1: C).(clear c1 e1))))))))))
\def
 \lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: C).(\forall (v: 
T).(\forall (i: nat).((csubst0 i v c c2) \to (\forall (e2: C).((clear c2 e2) 
\to (or (clear c e2) (ex2 C (\lambda (e1: C).(csubst0 i v e1 e2)) (\lambda 
(e1: C).(clear c e1))))))))))) (\lambda (n: nat).(\lambda (c2: C).(\lambda 
(v: T).(\lambda (i: nat).(\lambda (H: (csubst0 i v (CSort n) c2)).(\lambda 
(e2: C).(\lambda (_: (clear c2 e2)).(csubst0_gen_sort c2 v i n H (or (clear 
(CSort n) e2) (ex2 C (\lambda (e1: C).(csubst0 i v e1 e2)) (\lambda (e1: 
C).(clear (CSort n) e1)))))))))))) (\lambda (c: C).(\lambda (H: ((\forall 
(c2: C).(\forall (v: T).(\forall (i: nat).((csubst0 i v c c2) \to (\forall 
(e2: C).((clear c2 e2) \to (or (clear c e2) (ex2 C (\lambda (e1: C).(csubst0 
i v e1 e2)) (\lambda (e1: C).(clear c e1)))))))))))).(\lambda (k: K).(\lambda 
(t: T).(\lambda (c2: C).(\lambda (v: T).(\lambda (i: nat).(\lambda (H0: 
(csubst0 i v (CHead c k t) c2)).(\lambda (e2: C).(\lambda (H1: (clear c2 
e2)).(let H2 \def (csubst0_gen_head k c c2 t v i H0) in (or3_ind (ex3_2 T nat 
(\lambda (_: T).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v t u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat i (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k 
t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3)))) (ex4_3 T C nat 
(\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat i (s k j))))) 
(\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k 
u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t 
u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c 
c3))))) (or (clear (CHead c k t) e2) (ex2 C (\lambda (e1: C).(csubst0 i v e1 
e2)) (\lambda (e1: C).(clear (CHead c k t) e1)))) (\lambda (H3: (ex3_2 T nat 
(\lambda (_: T).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v t u2))))).(ex3_2_ind T nat (\lambda (_: T).(\lambda (j: 
nat).(eq nat i (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead 
c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v t u2))) (or (clear 
(CHead c k t) e2) (ex2 C (\lambda (e1: C).(csubst0 i v e1 e2)) (\lambda (e1: 
C).(clear (CHead c k t) e1)))) (\lambda (x0: T).(\lambda (x1: nat).(\lambda 
(H4: (eq nat i (s k x1))).(\lambda (H5: (eq C c2 (CHead c k x0))).(\lambda 
(H6: (subst0 x1 v t x0)).(eq_ind_r nat (s k x1) (\lambda (n: nat).(or (clear 
(CHead c k t) e2) (ex2 C (\lambda (e1: C).(csubst0 n v e1 e2)) (\lambda (e1: 
C).(clear (CHead c k t) e1))))) (let H7 \def (eq_ind C c2 (\lambda (c0: 
C).(clear c0 e2)) H1 (CHead c k x0) H5) in (K_ind (\lambda (k0: K).((clear 
(CHead c k0 x0) e2) \to (or (clear (CHead c k0 t) e2) (ex2 C (\lambda (e1: 
C).(csubst0 (s k0 x1) v e1 e2)) (\lambda (e1: C).(clear (CHead c k0 t) 
e1)))))) (\lambda (b: B).(\lambda (H8: (clear (CHead c (Bind b) x0) 
e2)).(eq_ind_r C (CHead c (Bind b) x0) (\lambda (c0: C).(or (clear (CHead c 
(Bind b) t) c0) (ex2 C (\lambda (e1: C).(csubst0 (s (Bind b) x1) v e1 c0)) 
(\lambda (e1: C).(clear (CHead c (Bind b) t) e1))))) (or_intror (clear (CHead 
c (Bind b) t) (CHead c (Bind b) x0)) (ex2 C (\lambda (e1: C).(csubst0 (s 
(Bind b) x1) v e1 (CHead c (Bind b) x0))) (\lambda (e1: C).(clear (CHead c 
(Bind b) t) e1))) (ex_intro2 C (\lambda (e1: C).(csubst0 (s (Bind b) x1) v e1 
(CHead c (Bind b) x0))) (\lambda (e1: C).(clear (CHead c (Bind b) t) e1)) 
(CHead c (Bind b) t) (csubst0_snd (Bind b) x1 v t x0 H6 c) (clear_bind b c 
t))) e2 (clear_gen_bind b c e2 x0 H8)))) (\lambda (f: F).(\lambda (H8: (clear 
(CHead c (Flat f) x0) e2)).(or_introl (clear (CHead c (Flat f) t) e2) (ex2 C 
(\lambda (e1: C).(csubst0 (s (Flat f) x1) v e1 e2)) (\lambda (e1: C).(clear 
(CHead c (Flat f) t) e1))) (clear_flat c e2 (clear_gen_flat f c e2 x0 H8) f 
t)))) k H7)) i H4)))))) H3)) (\lambda (H3: (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j 
v c c3))))).(ex3_2_ind C nat (\lambda (_: C).(\lambda (j: nat).(eq nat i (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c c3))) (or (clear (CHead c k t) e2) 
(ex2 C (\lambda (e1: C).(csubst0 i v e1 e2)) (\lambda (e1: C).(clear (CHead c 
k t) e1)))) (\lambda (x0: C).(\lambda (x1: nat).(\lambda (H4: (eq nat i (s k 
x1))).(\lambda (H5: (eq C c2 (CHead x0 k t))).(\lambda (H6: (csubst0 x1 v c 
x0)).(eq_ind_r nat (s k x1) (\lambda (n: nat).(or (clear (CHead c k t) e2) 
(ex2 C (\lambda (e1: C).(csubst0 n v e1 e2)) (\lambda (e1: C).(clear (CHead c 
k t) e1))))) (let H7 \def (eq_ind C c2 (\lambda (c0: C).(clear c0 e2)) H1 
(CHead x0 k t) H5) in (K_ind (\lambda (k0: K).((clear (CHead x0 k0 t) e2) \to 
(or (clear (CHead c k0 t) e2) (ex2 C (\lambda (e1: C).(csubst0 (s k0 x1) v e1 
e2)) (\lambda (e1: C).(clear (CHead c k0 t) e1)))))) (\lambda (b: B).(\lambda 
(H8: (clear (CHead x0 (Bind b) t) e2)).(eq_ind_r C (CHead x0 (Bind b) t) 
(\lambda (c0: C).(or (clear (CHead c (Bind b) t) c0) (ex2 C (\lambda (e1: 
C).(csubst0 (s (Bind b) x1) v e1 c0)) (\lambda (e1: C).(clear (CHead c (Bind 
b) t) e1))))) (or_intror (clear (CHead c (Bind b) t) (CHead x0 (Bind b) t)) 
(ex2 C (\lambda (e1: C).(csubst0 (s (Bind b) x1) v e1 (CHead x0 (Bind b) t))) 
(\lambda (e1: C).(clear (CHead c (Bind b) t) e1))) (ex_intro2 C (\lambda (e1: 
C).(csubst0 (s (Bind b) x1) v e1 (CHead x0 (Bind b) t))) (\lambda (e1: 
C).(clear (CHead c (Bind b) t) e1)) (CHead c (Bind b) t) (csubst0_fst (Bind 
b) x1 c x0 v H6 t) (clear_bind b c t))) e2 (clear_gen_bind b x0 e2 t H8)))) 
(\lambda (f: F).(\lambda (H8: (clear (CHead x0 (Flat f) t) e2)).(let H_x \def 
(H x0 v x1 H6 e2 (clear_gen_flat f x0 e2 t H8)) in (let H9 \def H_x in 
(or_ind (clear c e2) (ex2 C (\lambda (e1: C).(csubst0 x1 v e1 e2)) (\lambda 
(e1: C).(clear c e1))) (or (clear (CHead c (Flat f) t) e2) (ex2 C (\lambda 
(e1: C).(csubst0 (s (Flat f) x1) v e1 e2)) (\lambda (e1: C).(clear (CHead c 
(Flat f) t) e1)))) (\lambda (H10: (clear c e2)).(or_introl (clear (CHead c 
(Flat f) t) e2) (ex2 C (\lambda (e1: C).(csubst0 (s (Flat f) x1) v e1 e2)) 
(\lambda (e1: C).(clear (CHead c (Flat f) t) e1))) (clear_flat c e2 H10 f 
t))) (\lambda (H10: (ex2 C (\lambda (e1: C).(csubst0 x1 v e1 e2)) (\lambda 
(e1: C).(clear c e1)))).(ex2_ind C (\lambda (e1: C).(csubst0 x1 v e1 e2)) 
(\lambda (e1: C).(clear c e1)) (or (clear (CHead c (Flat f) t) e2) (ex2 C 
(\lambda (e1: C).(csubst0 (s (Flat f) x1) v e1 e2)) (\lambda (e1: C).(clear 
(CHead c (Flat f) t) e1)))) (\lambda (x: C).(\lambda (H11: (csubst0 x1 v x 
e2)).(\lambda (H12: (clear c x)).(or_intror (clear (CHead c (Flat f) t) e2) 
(ex2 C (\lambda (e1: C).(csubst0 (s (Flat f) x1) v e1 e2)) (\lambda (e1: 
C).(clear (CHead c (Flat f) t) e1))) (ex_intro2 C (\lambda (e1: C).(csubst0 
(s (Flat f) x1) v e1 e2)) (\lambda (e1: C).(clear (CHead c (Flat f) t) e1)) x 
H11 (clear_flat c x H12 f t)))))) H10)) H9))))) k H7)) i H4)))))) H3)) 
(\lambda (H3: (ex4_3 T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat i (s k j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda 
(j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c c3)))))).(ex4_3_ind T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat i (s k j))))) (\lambda (u2: T).(\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda 
(_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c c3)))) (or (clear (CHead c k t) e2) (ex2 
C (\lambda (e1: C).(csubst0 i v e1 e2)) (\lambda (e1: C).(clear (CHead c k t) 
e1)))) (\lambda (x0: T).(\lambda (x1: C).(\lambda (x2: nat).(\lambda (H4: (eq 
nat i (s k x2))).(\lambda (H5: (eq C c2 (CHead x1 k x0))).(\lambda (H6: 
(subst0 x2 v t x0)).(\lambda (H7: (csubst0 x2 v c x1)).(eq_ind_r nat (s k x2) 
(\lambda (n: nat).(or (clear (CHead c k t) e2) (ex2 C (\lambda (e1: 
C).(csubst0 n v e1 e2)) (\lambda (e1: C).(clear (CHead c k t) e1))))) (let H8 
\def (eq_ind C c2 (\lambda (c0: C).(clear c0 e2)) H1 (CHead x1 k x0) H5) in 
(K_ind (\lambda (k0: K).((clear (CHead x1 k0 x0) e2) \to (or (clear (CHead c 
k0 t) e2) (ex2 C (\lambda (e1: C).(csubst0 (s k0 x2) v e1 e2)) (\lambda (e1: 
C).(clear (CHead c k0 t) e1)))))) (\lambda (b: B).(\lambda (H9: (clear (CHead 
x1 (Bind b) x0) e2)).(eq_ind_r C (CHead x1 (Bind b) x0) (\lambda (c0: C).(or 
(clear (CHead c (Bind b) t) c0) (ex2 C (\lambda (e1: C).(csubst0 (s (Bind b) 
x2) v e1 c0)) (\lambda (e1: C).(clear (CHead c (Bind b) t) e1))))) (or_intror 
(clear (CHead c (Bind b) t) (CHead x1 (Bind b) x0)) (ex2 C (\lambda (e1: 
C).(csubst0 (s (Bind b) x2) v e1 (CHead x1 (Bind b) x0))) (\lambda (e1: 
C).(clear (CHead c (Bind b) t) e1))) (ex_intro2 C (\lambda (e1: C).(csubst0 
(s (Bind b) x2) v e1 (CHead x1 (Bind b) x0))) (\lambda (e1: C).(clear (CHead 
c (Bind b) t) e1)) (CHead c (Bind b) t) (csubst0_both (Bind b) x2 v t x0 H6 c 
x1 H7) (clear_bind b c t))) e2 (clear_gen_bind b x1 e2 x0 H9)))) (\lambda (f: 
F).(\lambda (H9: (clear (CHead x1 (Flat f) x0) e2)).(let H_x \def (H x1 v x2 
H7 e2 (clear_gen_flat f x1 e2 x0 H9)) in (let H10 \def H_x in (or_ind (clear 
c e2) (ex2 C (\lambda (e1: C).(csubst0 x2 v e1 e2)) (\lambda (e1: C).(clear c 
e1))) (or (clear (CHead c (Flat f) t) e2) (ex2 C (\lambda (e1: C).(csubst0 (s 
(Flat f) x2) v e1 e2)) (\lambda (e1: C).(clear (CHead c (Flat f) t) e1)))) 
(\lambda (H11: (clear c e2)).(or_introl (clear (CHead c (Flat f) t) e2) (ex2 
C (\lambda (e1: C).(csubst0 (s (Flat f) x2) v e1 e2)) (\lambda (e1: C).(clear 
(CHead c (Flat f) t) e1))) (clear_flat c e2 H11 f t))) (\lambda (H11: (ex2 C 
(\lambda (e1: C).(csubst0 x2 v e1 e2)) (\lambda (e1: C).(clear c 
e1)))).(ex2_ind C (\lambda (e1: C).(csubst0 x2 v e1 e2)) (\lambda (e1: 
C).(clear c e1)) (or (clear (CHead c (Flat f) t) e2) (ex2 C (\lambda (e1: 
C).(csubst0 (s (Flat f) x2) v e1 e2)) (\lambda (e1: C).(clear (CHead c (Flat 
f) t) e1)))) (\lambda (x: C).(\lambda (H12: (csubst0 x2 v x e2)).(\lambda 
(H13: (clear c x)).(or_intror (clear (CHead c (Flat f) t) e2) (ex2 C (\lambda 
(e1: C).(csubst0 (s (Flat f) x2) v e1 e2)) (\lambda (e1: C).(clear (CHead c 
(Flat f) t) e1))) (ex_intro2 C (\lambda (e1: C).(csubst0 (s (Flat f) x2) v e1 
e2)) (\lambda (e1: C).(clear (CHead c (Flat f) t) e1)) x H12 (clear_flat c x 
H13 f t)))))) H11)) H10))))) k H8)) i H4)))))))) H3)) H2)))))))))))) c1).

