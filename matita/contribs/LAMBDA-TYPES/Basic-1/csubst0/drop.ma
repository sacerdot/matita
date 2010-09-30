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

include "Basic-1/csubst0/fwd.ma".

include "Basic-1/drop/fwd.ma".

include "Basic-1/s/props.ma".

theorem csubst0_drop_gt:
 \forall (n: nat).(\forall (i: nat).((lt i n) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (e: C).((drop n O 
c1 e) \to (drop n O c2 e)))))))))
\def
 \lambda (n: nat).(nat_ind (\lambda (n0: nat).(\forall (i: nat).((lt i n0) 
\to (\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 c2) 
\to (\forall (e: C).((drop n0 O c1 e) \to (drop n0 O c2 e)))))))))) (\lambda 
(i: nat).(\lambda (H: (lt i O)).(\lambda (c1: C).(\lambda (c2: C).(\lambda 
(v: T).(\lambda (_: (csubst0 i v c1 c2)).(\lambda (e: C).(\lambda (_: (drop O 
O c1 e)).(lt_x_O i H (drop O O c2 e)))))))))) (\lambda (n0: nat).(\lambda (H: 
((\forall (i: nat).((lt i n0) \to (\forall (c1: C).(\forall (c2: C).(\forall 
(v: T).((csubst0 i v c1 c2) \to (\forall (e: C).((drop n0 O c1 e) \to (drop 
n0 O c2 e))))))))))).(\lambda (i: nat).(\lambda (H0: (lt i (S n0))).(\lambda 
(c1: C).(C_ind (\lambda (c: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v 
c c2) \to (\forall (e: C).((drop (S n0) O c e) \to (drop (S n0) O c2 e))))))) 
(\lambda (n1: nat).(\lambda (c2: C).(\lambda (v: T).(\lambda (_: (csubst0 i v 
(CSort n1) c2)).(\lambda (e: C).(\lambda (H2: (drop (S n0) O (CSort n1) 
e)).(and3_ind (eq C e (CSort n1)) (eq nat (S n0) O) (eq nat O O) (drop (S n0) 
O c2 e) (\lambda (H3: (eq C e (CSort n1))).(\lambda (H4: (eq nat (S n0) 
O)).(\lambda (_: (eq nat O O)).(eq_ind_r C (CSort n1) (\lambda (c: C).(drop 
(S n0) O c2 c)) (let H6 \def (eq_ind nat (S n0) (\lambda (ee: nat).(match ee 
in nat return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) 
\Rightarrow True])) I O H4) in (False_ind (drop (S n0) O c2 (CSort n1)) H6)) 
e H3)))) (drop_gen_sort n1 (S n0) O e H2)))))))) (\lambda (c: C).(\lambda 
(H1: ((\forall (c2: C).(\forall (v: T).((csubst0 i v c c2) \to (\forall (e: 
C).((drop (S n0) O c e) \to (drop (S n0) O c2 e)))))))).(\lambda (k: 
K).(\lambda (t: T).(\lambda (c2: C).(\lambda (v: T).(\lambda (H2: (csubst0 i 
v (CHead c k t) c2)).(\lambda (e: C).(\lambda (H3: (drop (S n0) O (CHead c k 
t) e)).(or3_ind (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat i (s k 
j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda 
(u2: T).(\lambda (j: nat).(subst0 j v t u2)))) (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j 
v c c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat i (s k j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda 
(j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c c3))))) (drop (S n0) O c2 e) (\lambda (H4: (ex3_2 T nat 
(\lambda (_: T).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v t u2))))).(ex3_2_ind T nat (\lambda (_: T).(\lambda (j: 
nat).(eq nat i (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead 
c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v t u2))) (drop (S 
n0) O c2 e) (\lambda (x0: T).(\lambda (x1: nat).(\lambda (H5: (eq nat i (s k 
x1))).(\lambda (H6: (eq C c2 (CHead c k x0))).(\lambda (_: (subst0 x1 v t 
x0)).(eq_ind_r C (CHead c k x0) (\lambda (c0: C).(drop (S n0) O c0 e)) (let 
H8 \def (eq_ind nat i (\lambda (n1: nat).(\forall (c3: C).(\forall (v0: 
T).((csubst0 n1 v0 c c3) \to (\forall (e0: C).((drop (S n0) O c e0) \to (drop 
(S n0) O c3 e0))))))) H1 (s k x1) H5) in (let H9 \def (eq_ind nat i (\lambda 
(n1: nat).(lt n1 (S n0))) H0 (s k x1) H5) in (K_ind (\lambda (k0: K).((drop 
(r k0 n0) O c e) \to (((\forall (c3: C).(\forall (v0: T).((csubst0 (s k0 x1) 
v0 c c3) \to (\forall (e0: C).((drop (S n0) O c e0) \to (drop (S n0) O c3 
e0))))))) \to ((lt (s k0 x1) (S n0)) \to (drop (S n0) O (CHead c k0 x0) 
e))))) (\lambda (b: B).(\lambda (H10: (drop (r (Bind b) n0) O c e)).(\lambda 
(_: ((\forall (c3: C).(\forall (v0: T).((csubst0 (s (Bind b) x1) v0 c c3) \to 
(\forall (e0: C).((drop (S n0) O c e0) \to (drop (S n0) O c3 
e0)))))))).(\lambda (_: (lt (s (Bind b) x1) (S n0))).(drop_drop (Bind b) n0 c 
e H10 x0))))) (\lambda (f: F).(\lambda (H10: (drop (r (Flat f) n0) O c 
e)).(\lambda (_: ((\forall (c3: C).(\forall (v0: T).((csubst0 (s (Flat f) x1) 
v0 c c3) \to (\forall (e0: C).((drop (S n0) O c e0) \to (drop (S n0) O c3 
e0)))))))).(\lambda (H12: (lt (s (Flat f) x1) (S n0))).(or_ind (eq nat x1 O) 
(ex2 nat (\lambda (m: nat).(eq nat x1 (S m))) (\lambda (m: nat).(lt m n0))) 
(drop (S n0) O (CHead c (Flat f) x0) e) (\lambda (_: (eq nat x1 
O)).(drop_drop (Flat f) n0 c e H10 x0)) (\lambda (H13: (ex2 nat (\lambda (m: 
nat).(eq nat x1 (S m))) (\lambda (m: nat).(lt m n0)))).(ex2_ind nat (\lambda 
(m: nat).(eq nat x1 (S m))) (\lambda (m: nat).(lt m n0)) (drop (S n0) O 
(CHead c (Flat f) x0) e) (\lambda (x: nat).(\lambda (_: (eq nat x1 (S 
x))).(\lambda (_: (lt x n0)).(drop_drop (Flat f) n0 c e H10 x0)))) H13)) 
(lt_gen_xS x1 n0 H12)))))) k (drop_gen_drop k c e t n0 H3) H8 H9))) c2 
H6)))))) H4)) (\lambda (H4: (ex3_2 C nat (\lambda (_: C).(\lambda (j: 
nat).(eq nat i (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead 
c3 k t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c 
c3))))).(ex3_2_ind C nat (\lambda (_: C).(\lambda (j: nat).(eq nat i (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c c3))) (drop (S n0) O c2 e) (\lambda 
(x0: C).(\lambda (x1: nat).(\lambda (H5: (eq nat i (s k x1))).(\lambda (H6: 
(eq C c2 (CHead x0 k t))).(\lambda (H7: (csubst0 x1 v c x0)).(eq_ind_r C 
(CHead x0 k t) (\lambda (c0: C).(drop (S n0) O c0 e)) (let H8 \def (eq_ind 
nat i (\lambda (n1: nat).(\forall (c3: C).(\forall (v0: T).((csubst0 n1 v0 c 
c3) \to (\forall (e0: C).((drop (S n0) O c e0) \to (drop (S n0) O c3 
e0))))))) H1 (s k x1) H5) in (let H9 \def (eq_ind nat i (\lambda (n1: 
nat).(lt n1 (S n0))) H0 (s k x1) H5) in (K_ind (\lambda (k0: K).((drop (r k0 
n0) O c e) \to (((\forall (c3: C).(\forall (v0: T).((csubst0 (s k0 x1) v0 c 
c3) \to (\forall (e0: C).((drop (S n0) O c e0) \to (drop (S n0) O c3 
e0))))))) \to ((lt (s k0 x1) (S n0)) \to (drop (S n0) O (CHead x0 k0 t) 
e))))) (\lambda (b: B).(\lambda (H10: (drop (r (Bind b) n0) O c e)).(\lambda 
(_: ((\forall (c3: C).(\forall (v0: T).((csubst0 (s (Bind b) x1) v0 c c3) \to 
(\forall (e0: C).((drop (S n0) O c e0) \to (drop (S n0) O c3 
e0)))))))).(\lambda (H12: (lt (s (Bind b) x1) (S n0))).(drop_drop (Bind b) n0 
x0 e (H x1 (lt_S_n x1 n0 H12) c x0 v H7 e H10) t))))) (\lambda (f: 
F).(\lambda (H10: (drop (r (Flat f) n0) O c e)).(\lambda (H11: ((\forall (c3: 
C).(\forall (v0: T).((csubst0 (s (Flat f) x1) v0 c c3) \to (\forall (e0: 
C).((drop (S n0) O c e0) \to (drop (S n0) O c3 e0)))))))).(\lambda (H12: (lt 
(s (Flat f) x1) (S n0))).(or_ind (eq nat x1 O) (ex2 nat (\lambda (m: nat).(eq 
nat x1 (S m))) (\lambda (m: nat).(lt m n0))) (drop (S n0) O (CHead x0 (Flat 
f) t) e) (\lambda (_: (eq nat x1 O)).(drop_drop (Flat f) n0 x0 e (H11 x0 v H7 
e H10) t)) (\lambda (H13: (ex2 nat (\lambda (m: nat).(eq nat x1 (S m))) 
(\lambda (m: nat).(lt m n0)))).(ex2_ind nat (\lambda (m: nat).(eq nat x1 (S 
m))) (\lambda (m: nat).(lt m n0)) (drop (S n0) O (CHead x0 (Flat f) t) e) 
(\lambda (x: nat).(\lambda (_: (eq nat x1 (S x))).(\lambda (_: (lt x 
n0)).(drop_drop (Flat f) n0 x0 e (H11 x0 v H7 e H10) t)))) H13)) (lt_gen_xS 
x1 n0 H12)))))) k (drop_gen_drop k c e t n0 H3) H8 H9))) c2 H6)))))) H4)) 
(\lambda (H4: (ex4_3 T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat i (s k j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda 
(j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c c3)))))).(ex4_3_ind T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat i (s k j))))) (\lambda (u2: T).(\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda 
(_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c c3)))) (drop (S n0) O c2 e) (\lambda (x0: 
T).(\lambda (x1: C).(\lambda (x2: nat).(\lambda (H5: (eq nat i (s k 
x2))).(\lambda (H6: (eq C c2 (CHead x1 k x0))).(\lambda (_: (subst0 x2 v t 
x0)).(\lambda (H8: (csubst0 x2 v c x1)).(eq_ind_r C (CHead x1 k x0) (\lambda 
(c0: C).(drop (S n0) O c0 e)) (let H9 \def (eq_ind nat i (\lambda (n1: 
nat).(\forall (c3: C).(\forall (v0: T).((csubst0 n1 v0 c c3) \to (\forall 
(e0: C).((drop (S n0) O c e0) \to (drop (S n0) O c3 e0))))))) H1 (s k x2) H5) 
in (let H10 \def (eq_ind nat i (\lambda (n1: nat).(lt n1 (S n0))) H0 (s k x2) 
H5) in (K_ind (\lambda (k0: K).((drop (r k0 n0) O c e) \to (((\forall (c3: 
C).(\forall (v0: T).((csubst0 (s k0 x2) v0 c c3) \to (\forall (e0: C).((drop 
(S n0) O c e0) \to (drop (S n0) O c3 e0))))))) \to ((lt (s k0 x2) (S n0)) \to 
(drop (S n0) O (CHead x1 k0 x0) e))))) (\lambda (b: B).(\lambda (H11: (drop 
(r (Bind b) n0) O c e)).(\lambda (_: ((\forall (c3: C).(\forall (v0: 
T).((csubst0 (s (Bind b) x2) v0 c c3) \to (\forall (e0: C).((drop (S n0) O c 
e0) \to (drop (S n0) O c3 e0)))))))).(\lambda (H13: (lt (s (Bind b) x2) (S 
n0))).(drop_drop (Bind b) n0 x1 e (H x2 (lt_S_n x2 n0 H13) c x1 v H8 e H11) 
x0))))) (\lambda (f: F).(\lambda (H11: (drop (r (Flat f) n0) O c e)).(\lambda 
(H12: ((\forall (c3: C).(\forall (v0: T).((csubst0 (s (Flat f) x2) v0 c c3) 
\to (\forall (e0: C).((drop (S n0) O c e0) \to (drop (S n0) O c3 
e0)))))))).(\lambda (H13: (lt (s (Flat f) x2) (S n0))).(or_ind (eq nat x2 O) 
(ex2 nat (\lambda (m: nat).(eq nat x2 (S m))) (\lambda (m: nat).(lt m n0))) 
(drop (S n0) O (CHead x1 (Flat f) x0) e) (\lambda (_: (eq nat x2 
O)).(drop_drop (Flat f) n0 x1 e (H12 x1 v H8 e H11) x0)) (\lambda (H14: (ex2 
nat (\lambda (m: nat).(eq nat x2 (S m))) (\lambda (m: nat).(lt m 
n0)))).(ex2_ind nat (\lambda (m: nat).(eq nat x2 (S m))) (\lambda (m: 
nat).(lt m n0)) (drop (S n0) O (CHead x1 (Flat f) x0) e) (\lambda (x: 
nat).(\lambda (_: (eq nat x2 (S x))).(\lambda (_: (lt x n0)).(drop_drop (Flat 
f) n0 x1 e (H12 x1 v H8 e H11) x0)))) H14)) (lt_gen_xS x2 n0 H13)))))) k 
(drop_gen_drop k c e t n0 H3) H9 H10))) c2 H6)))))))) H4)) (csubst0_gen_head 
k c c2 t v i H2))))))))))) c1)))))) n).
(* COMMENTS
Initial nodes: 3092
END *)

theorem csubst0_drop_gt_back:
 \forall (n: nat).(\forall (i: nat).((lt i n) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (e: C).((drop n O 
c2 e) \to (drop n O c1 e)))))))))
\def
 \lambda (n: nat).(nat_ind (\lambda (n0: nat).(\forall (i: nat).((lt i n0) 
\to (\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 c2) 
\to (\forall (e: C).((drop n0 O c2 e) \to (drop n0 O c1 e)))))))))) (\lambda 
(i: nat).(\lambda (H: (lt i O)).(\lambda (c1: C).(\lambda (c2: C).(\lambda 
(v: T).(\lambda (_: (csubst0 i v c1 c2)).(\lambda (e: C).(\lambda (_: (drop O 
O c2 e)).(lt_x_O i H (drop O O c1 e)))))))))) (\lambda (n0: nat).(\lambda (H: 
((\forall (i: nat).((lt i n0) \to (\forall (c1: C).(\forall (c2: C).(\forall 
(v: T).((csubst0 i v c1 c2) \to (\forall (e: C).((drop n0 O c2 e) \to (drop 
n0 O c1 e))))))))))).(\lambda (i: nat).(\lambda (H0: (lt i (S n0))).(\lambda 
(c1: C).(C_ind (\lambda (c: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v 
c c2) \to (\forall (e: C).((drop (S n0) O c2 e) \to (drop (S n0) O c e))))))) 
(\lambda (n1: nat).(\lambda (c2: C).(\lambda (v: T).(\lambda (H1: (csubst0 i 
v (CSort n1) c2)).(\lambda (e: C).(\lambda (_: (drop (S n0) O c2 
e)).(csubst0_gen_sort c2 v i n1 H1 (drop (S n0) O (CSort n1) e)))))))) 
(\lambda (c: C).(\lambda (H1: ((\forall (c2: C).(\forall (v: T).((csubst0 i v 
c c2) \to (\forall (e: C).((drop (S n0) O c2 e) \to (drop (S n0) O c 
e)))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c2: C).(\lambda (v: 
T).(\lambda (H2: (csubst0 i v (CHead c k t) c2)).(\lambda (e: C).(\lambda 
(H3: (drop (S n0) O c2 e)).(or3_ind (ex3_2 T nat (\lambda (_: T).(\lambda (j: 
nat).(eq nat i (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead 
c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v t u2)))) (ex3_2 C 
nat (\lambda (_: C).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat i (s k j))))) (\lambda (u2: T).(\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda 
(_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c c3))))) (drop (S n0) O (CHead c k t) e) 
(\lambda (H4: (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat i (s k 
j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda 
(u2: T).(\lambda (j: nat).(subst0 j v t u2))))).(ex3_2_ind T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (u2: T).(\lambda (_: 
nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j 
v t u2))) (drop (S n0) O (CHead c k t) e) (\lambda (x0: T).(\lambda (x1: 
nat).(\lambda (H5: (eq nat i (s k x1))).(\lambda (H6: (eq C c2 (CHead c k 
x0))).(\lambda (_: (subst0 x1 v t x0)).(let H8 \def (eq_ind C c2 (\lambda 
(c0: C).(drop (S n0) O c0 e)) H3 (CHead c k x0) H6) in (let H9 \def (eq_ind 
nat i (\lambda (n1: nat).(\forall (c3: C).(\forall (v0: T).((csubst0 n1 v0 c 
c3) \to (\forall (e0: C).((drop (S n0) O c3 e0) \to (drop (S n0) O c 
e0))))))) H1 (s k x1) H5) in (let H10 \def (eq_ind nat i (\lambda (n1: 
nat).(lt n1 (S n0))) H0 (s k x1) H5) in (K_ind (\lambda (k0: K).(((\forall 
(c3: C).(\forall (v0: T).((csubst0 (s k0 x1) v0 c c3) \to (\forall (e0: 
C).((drop (S n0) O c3 e0) \to (drop (S n0) O c e0))))))) \to ((lt (s k0 x1) 
(S n0)) \to ((drop (r k0 n0) O c e) \to (drop (S n0) O (CHead c k0 t) e))))) 
(\lambda (b: B).(\lambda (_: ((\forall (c3: C).(\forall (v0: T).((csubst0 (s 
(Bind b) x1) v0 c c3) \to (\forall (e0: C).((drop (S n0) O c3 e0) \to (drop 
(S n0) O c e0)))))))).(\lambda (_: (lt (s (Bind b) x1) (S n0))).(\lambda 
(H13: (drop (r (Bind b) n0) O c e)).(drop_drop (Bind b) n0 c e H13 t))))) 
(\lambda (f: F).(\lambda (_: ((\forall (c3: C).(\forall (v0: T).((csubst0 (s 
(Flat f) x1) v0 c c3) \to (\forall (e0: C).((drop (S n0) O c3 e0) \to (drop 
(S n0) O c e0)))))))).(\lambda (H12: (lt (s (Flat f) x1) (S n0))).(\lambda 
(H13: (drop (r (Flat f) n0) O c e)).(or_ind (eq nat x1 O) (ex2 nat (\lambda 
(m: nat).(eq nat x1 (S m))) (\lambda (m: nat).(lt m n0))) (drop (S n0) O 
(CHead c (Flat f) t) e) (\lambda (_: (eq nat x1 O)).(drop_drop (Flat f) n0 c 
e H13 t)) (\lambda (H14: (ex2 nat (\lambda (m: nat).(eq nat x1 (S m))) 
(\lambda (m: nat).(lt m n0)))).(ex2_ind nat (\lambda (m: nat).(eq nat x1 (S 
m))) (\lambda (m: nat).(lt m n0)) (drop (S n0) O (CHead c (Flat f) t) e) 
(\lambda (x: nat).(\lambda (_: (eq nat x1 (S x))).(\lambda (_: (lt x 
n0)).(drop_drop (Flat f) n0 c e H13 t)))) H14)) (lt_gen_xS x1 n0 H12)))))) k 
H9 H10 (drop_gen_drop k c e x0 n0 H8)))))))))) H4)) (\lambda (H4: (ex3_2 C 
nat (\lambda (_: C).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c c3))))).(ex3_2_ind C nat (\lambda (_: C).(\lambda (j: 
nat).(eq nat i (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead 
c3 k t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3))) (drop (S 
n0) O (CHead c k t) e) (\lambda (x0: C).(\lambda (x1: nat).(\lambda (H5: (eq 
nat i (s k x1))).(\lambda (H6: (eq C c2 (CHead x0 k t))).(\lambda (H7: 
(csubst0 x1 v c x0)).(let H8 \def (eq_ind C c2 (\lambda (c0: C).(drop (S n0) 
O c0 e)) H3 (CHead x0 k t) H6) in (let H9 \def (eq_ind nat i (\lambda (n1: 
nat).(\forall (c3: C).(\forall (v0: T).((csubst0 n1 v0 c c3) \to (\forall 
(e0: C).((drop (S n0) O c3 e0) \to (drop (S n0) O c e0))))))) H1 (s k x1) H5) 
in (let H10 \def (eq_ind nat i (\lambda (n1: nat).(lt n1 (S n0))) H0 (s k x1) 
H5) in (K_ind (\lambda (k0: K).(((\forall (c3: C).(\forall (v0: T).((csubst0 
(s k0 x1) v0 c c3) \to (\forall (e0: C).((drop (S n0) O c3 e0) \to (drop (S 
n0) O c e0))))))) \to ((lt (s k0 x1) (S n0)) \to ((drop (r k0 n0) O x0 e) \to 
(drop (S n0) O (CHead c k0 t) e))))) (\lambda (b: B).(\lambda (_: ((\forall 
(c3: C).(\forall (v0: T).((csubst0 (s (Bind b) x1) v0 c c3) \to (\forall (e0: 
C).((drop (S n0) O c3 e0) \to (drop (S n0) O c e0)))))))).(\lambda (H12: (lt 
(s (Bind b) x1) (S n0))).(\lambda (H13: (drop (r (Bind b) n0) O x0 
e)).(drop_drop (Bind b) n0 c e (H x1 (lt_S_n x1 n0 H12) c x0 v H7 e H13) 
t))))) (\lambda (f: F).(\lambda (H11: ((\forall (c3: C).(\forall (v0: 
T).((csubst0 (s (Flat f) x1) v0 c c3) \to (\forall (e0: C).((drop (S n0) O c3 
e0) \to (drop (S n0) O c e0)))))))).(\lambda (H12: (lt (s (Flat f) x1) (S 
n0))).(\lambda (H13: (drop (r (Flat f) n0) O x0 e)).(or_ind (eq nat x1 O) 
(ex2 nat (\lambda (m: nat).(eq nat x1 (S m))) (\lambda (m: nat).(lt m n0))) 
(drop (S n0) O (CHead c (Flat f) t) e) (\lambda (_: (eq nat x1 O)).(drop_drop 
(Flat f) n0 c e (H11 x0 v H7 e H13) t)) (\lambda (H14: (ex2 nat (\lambda (m: 
nat).(eq nat x1 (S m))) (\lambda (m: nat).(lt m n0)))).(ex2_ind nat (\lambda 
(m: nat).(eq nat x1 (S m))) (\lambda (m: nat).(lt m n0)) (drop (S n0) O 
(CHead c (Flat f) t) e) (\lambda (x: nat).(\lambda (_: (eq nat x1 (S 
x))).(\lambda (_: (lt x n0)).(drop_drop (Flat f) n0 c e (H11 x0 v H7 e H13) 
t)))) H14)) (lt_gen_xS x1 n0 H12)))))) k H9 H10 (drop_gen_drop k x0 e t n0 
H8)))))))))) H4)) (\lambda (H4: (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat i (s k j))))) (\lambda (u2: T).(\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda 
(_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c c3)))))).(ex4_3_ind T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat i (s k j))))) (\lambda (u2: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3)))) (drop (S n0) O 
(CHead c k t) e) (\lambda (x0: T).(\lambda (x1: C).(\lambda (x2: 
nat).(\lambda (H5: (eq nat i (s k x2))).(\lambda (H6: (eq C c2 (CHead x1 k 
x0))).(\lambda (_: (subst0 x2 v t x0)).(\lambda (H8: (csubst0 x2 v c 
x1)).(let H9 \def (eq_ind C c2 (\lambda (c0: C).(drop (S n0) O c0 e)) H3 
(CHead x1 k x0) H6) in (let H10 \def (eq_ind nat i (\lambda (n1: 
nat).(\forall (c3: C).(\forall (v0: T).((csubst0 n1 v0 c c3) \to (\forall 
(e0: C).((drop (S n0) O c3 e0) \to (drop (S n0) O c e0))))))) H1 (s k x2) H5) 
in (let H11 \def (eq_ind nat i (\lambda (n1: nat).(lt n1 (S n0))) H0 (s k x2) 
H5) in (K_ind (\lambda (k0: K).(((\forall (c3: C).(\forall (v0: T).((csubst0 
(s k0 x2) v0 c c3) \to (\forall (e0: C).((drop (S n0) O c3 e0) \to (drop (S 
n0) O c e0))))))) \to ((lt (s k0 x2) (S n0)) \to ((drop (r k0 n0) O x1 e) \to 
(drop (S n0) O (CHead c k0 t) e))))) (\lambda (b: B).(\lambda (_: ((\forall 
(c3: C).(\forall (v0: T).((csubst0 (s (Bind b) x2) v0 c c3) \to (\forall (e0: 
C).((drop (S n0) O c3 e0) \to (drop (S n0) O c e0)))))))).(\lambda (H13: (lt 
(s (Bind b) x2) (S n0))).(\lambda (H14: (drop (r (Bind b) n0) O x1 
e)).(drop_drop (Bind b) n0 c e (H x2 (lt_S_n x2 n0 H13) c x1 v H8 e H14) 
t))))) (\lambda (f: F).(\lambda (H12: ((\forall (c3: C).(\forall (v0: 
T).((csubst0 (s (Flat f) x2) v0 c c3) \to (\forall (e0: C).((drop (S n0) O c3 
e0) \to (drop (S n0) O c e0)))))))).(\lambda (H13: (lt (s (Flat f) x2) (S 
n0))).(\lambda (H14: (drop (r (Flat f) n0) O x1 e)).(or_ind (eq nat x2 O) 
(ex2 nat (\lambda (m: nat).(eq nat x2 (S m))) (\lambda (m: nat).(lt m n0))) 
(drop (S n0) O (CHead c (Flat f) t) e) (\lambda (_: (eq nat x2 O)).(drop_drop 
(Flat f) n0 c e (H12 x1 v H8 e H14) t)) (\lambda (H15: (ex2 nat (\lambda (m: 
nat).(eq nat x2 (S m))) (\lambda (m: nat).(lt m n0)))).(ex2_ind nat (\lambda 
(m: nat).(eq nat x2 (S m))) (\lambda (m: nat).(lt m n0)) (drop (S n0) O 
(CHead c (Flat f) t) e) (\lambda (x: nat).(\lambda (_: (eq nat x2 (S 
x))).(\lambda (_: (lt x n0)).(drop_drop (Flat f) n0 c e (H12 x1 v H8 e H14) 
t)))) H15)) (lt_gen_xS x2 n0 H13)))))) k H10 H11 (drop_gen_drop k x1 e x0 n0 
H9)))))))))))) H4)) (csubst0_gen_head k c c2 t v i H2))))))))))) c1)))))) n).
(* COMMENTS
Initial nodes: 2989
END *)

theorem csubst0_drop_lt:
 \forall (n: nat).(\forall (i: nat).((lt n i) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (e: C).((drop n O 
c1 e) \to (or4 (drop n O c2 e) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k u)))))) (\lambda (k: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n O c2 (CHead e0 k 
w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (s k n)) v u w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k 
u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop n O c2 (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus i (s k n)) v e1 e2)))))) (ex4_5 K C C 
T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop n O c2 (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (s k n)) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (s k 
n)) v e1 e2))))))))))))))))
\def
 \lambda (n: nat).(nat_ind (\lambda (n0: nat).(\forall (i: nat).((lt n0 i) 
\to (\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 c2) 
\to (\forall (e: C).((drop n0 O c1 e) \to (or4 (drop n0 O c2 e) (ex3_4 K C T 
T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop n0 O c2 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k n0)) v u w)))))) 
(ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop n0 O c2 (CHead e2 k u)))))) (\lambda (k: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (s k n0)) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop n0 
O c2 (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k n0)) v u w)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i (s k n0)) v e1 e2))))))))))))))))) (\lambda (i: 
nat).(\lambda (_: (lt O i)).(\lambda (c1: C).(\lambda (c2: C).(\lambda (v: 
T).(\lambda (H0: (csubst0 i v c1 c2)).(\lambda (e: C).(\lambda (H1: (drop O O 
c1 e)).(eq_ind C c1 (\lambda (c: C).(or4 (drop O O c2 c) (ex3_4 K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop O O c2 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k O)) v u w)))))) 
(ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop O O c2 (CHead e2 k u)))))) (\lambda (k: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (s k O)) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop O O 
c2 (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k O)) v u w)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i (s k O)) v e1 e2))))))))) (csubst0_ind (\lambda (n0: 
nat).(\lambda (t: T).(\lambda (c: C).(\lambda (c0: C).(or4 (drop O O c0 c) 
(ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C c (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop O O c0 (CHead e0 k w)))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus n0 (s k O)) t u w)))))) 
(ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop O O c0 (CHead e2 k u)))))) (\lambda (k: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus n0 (s k O)) t e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop O O 
c0 (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus n0 (s k O)) t u w)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus n0 (s k O)) t e1 e2)))))))))))) (\lambda (k: 
K).(\lambda (i0: nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (H2: (subst0 i0 v0 u1 u2)).(\lambda (c: C).(let H3 \def (eq_ind_r 
nat i0 (\lambda (n0: nat).(subst0 n0 v0 u1 u2)) H2 (minus (s k i0) (s k O)) 
(s_arith0 k i0)) in (or4_intro1 (drop O O (CHead c k u2) (CHead c k u1)) 
(ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C (CHead c k u1) (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop O O (CHead c k u2) (CHead e0 k0 
w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s k i0) (s k0 O)) v0 u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead c k u1) 
(CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop O O (CHead c k u2) (CHead e2 k0 u)))))) (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s 
k i0) (s k0 O)) v0 e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c k u1) 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop O O (CHead c k u2) (CHead e2 k0 
w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s k i0) (s k0 O)) v0 u w)))))) (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: 
T).(csubst0 (minus (s k i0) (s k0 O)) v0 e1 e2))))))) (ex3_4_intro K C T T 
(\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead c k u1) (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop O O (CHead c k u2) (CHead e0 k0 
w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s k i0) (s k0 O)) v0 u w))))) k c u1 u2 (refl_equal C 
(CHead c k u1)) (drop_refl (CHead c k u2)) H3)))))))))) (\lambda (k: 
K).(\lambda (i0: nat).(\lambda (c3: C).(\lambda (c4: C).(\lambda (v0: 
T).(\lambda (H2: (csubst0 i0 v0 c3 c4)).(\lambda (H3: (or4 (drop O O c4 c3) 
(ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C c3 (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop O O c4 (CHead e0 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i0 (s k0 
O)) v0 u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C c3 (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop O O c4 (CHead e2 k0 
u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus i0 (s k0 O)) v0 e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop O O c4 (CHead e2 k0 w))))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i0 (s k0 O)) v0 u w)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (s k0 
O)) v0 e1 e2))))))))).(\lambda (u: T).(let H4 \def (eq_ind_r nat i0 (\lambda 
(n0: nat).(csubst0 n0 v0 c3 c4)) H2 (minus (s k i0) (s k O)) (s_arith0 k i0)) 
in (let H5 \def (eq_ind_r nat i0 (\lambda (n0: nat).(or4 (drop O O c4 c3) 
(ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda 
(_: T).(eq C c3 (CHead e0 k0 u0)))))) (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop O O c4 (CHead e0 k0 w)))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus n0 (s 
k0 O)) v0 u0 w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(eq C c3 (CHead e1 k0 u0)))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop O O c4 (CHead 
e2 k0 u0)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 (minus n0 (s k0 O)) v0 e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C c3 (CHead e1 k0 u0))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop O O c4 (CHead e2 k0 w))))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda 
(w: T).(subst0 (minus n0 (s k0 O)) v0 u0 w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus n0 
(s k0 O)) v0 e1 e2))))))))) H3 (minus (s k i0) (s k O)) (s_arith0 k i0)) in 
(or4_intro2 (drop O O (CHead c4 k u) (CHead c3 k u)) (ex3_4 K C T T (\lambda 
(k0: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead c3 k 
u) (CHead e0 k0 u0)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop O O (CHead c4 k u) (CHead e0 k0 w)))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus (s k 
i0) (s k0 O)) v0 u0 w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(eq C (CHead c3 k u) (CHead e1 k0 
u0)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop O O (CHead c4 k u) (CHead e2 k0 u0)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s k i0) (s k0 O)) 
v0 e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead c3 k u) (CHead e1 k0 
u0))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop O O (CHead c4 k u) (CHead e2 k0 w))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s k i0) (s k0 O)) v0 u0 w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s k 
i0) (s k0 O)) v0 e1 e2))))))) (ex3_4_intro K C C T (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C (CHead c3 k u) (CHead e1 k0 
u0)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop O O (CHead c4 k u) (CHead e2 k0 u0)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s k i0) (s k0 O)) 
v0 e1 e2))))) k c3 c4 u (refl_equal C (CHead c3 k u)) (drop_refl (CHead c4 k 
u)) H4)))))))))))) (\lambda (k: K).(\lambda (i0: nat).(\lambda (v0: 
T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H2: (subst0 i0 v0 u1 
u2)).(\lambda (c3: C).(\lambda (c4: C).(\lambda (H3: (csubst0 i0 v0 c3 
c4)).(\lambda (_: (or4 (drop O O c4 c3) (ex3_4 K C T T (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e0 k0 
u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop O O c4 (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i0 (s k0 O)) v0 u w)))))) 
(ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c3 (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(drop O O c4 (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i0 (s k0 
O)) v0 e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e1 k0 
u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop O O c4 (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus i0 (s k0 O)) v0 u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (s k0 O)) v0 e1 
e2))))))))).(let H5 \def (eq_ind_r nat i0 (\lambda (n0: nat).(subst0 n0 v0 u1 
u2)) H2 (minus (s k i0) (s k O)) (s_arith0 k i0)) in (let H6 \def (eq_ind_r 
nat i0 (\lambda (n0: nat).(csubst0 n0 v0 c3 c4)) H3 (minus (s k i0) (s k O)) 
(s_arith0 k i0)) in (or4_intro3 (drop O O (CHead c4 k u2) (CHead c3 k u1)) 
(ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C (CHead c3 k u1) (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop O O (CHead c4 k u2) (CHead e0 k0 
w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s k i0) (s k0 O)) v0 u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead c3 k 
u1) (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop O O (CHead c4 k u2) (CHead e2 k0 u)))))) (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s 
k i0) (s k0 O)) v0 e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c3 k u1) 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop O O (CHead c4 k u2) (CHead e2 k0 
w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s k i0) (s k0 O)) v0 u w)))))) (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: 
T).(csubst0 (minus (s k i0) (s k0 O)) v0 e1 e2))))))) (ex4_5_intro K C C T T 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C (CHead c3 k u1) (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop O O (CHead c4 k 
u2) (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k i0) (s k0 O)) v0 u 
w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus (s k i0) (s k0 O)) v0 e1 e2)))))) k c3 c4 
u1 u2 (refl_equal C (CHead c3 k u1)) (drop_refl (CHead c4 k u2)) H5 
H6)))))))))))))) i v c1 c2 H0) e (drop_gen_refl c1 e H1)))))))))) (\lambda 
(n0: nat).(\lambda (IHn: ((\forall (i: nat).((lt n0 i) \to (\forall (c1: 
C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (e: 
C).((drop n0 O c1 e) \to (or4 (drop n0 O c2 e) (ex3_4 K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k 
u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop n0 O c2 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus i (s k n0)) v u w)))))) (ex3_4 K C C T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u: T).(drop n0 O c2 (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (s k n0)) v e1 e2)))))) 
(ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O c2 (CHead 
e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus i (s k n0)) v u w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus i (s k n0)) v e1 e2)))))))))))))))))).(\lambda (i: nat).(\lambda (H: 
(lt (S n0) i)).(\lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: 
C).(\forall (v: T).((csubst0 i v c c2) \to (\forall (e: C).((drop (S n0) O c 
e) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k u)))))) (\lambda (k: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead 
e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k 
u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O c2 (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O c2 (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k (S n0))) v u w)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i (s k (S n0))) v e1 e2)))))))))))))) (\lambda (n1: 
nat).(\lambda (c2: C).(\lambda (v: T).(\lambda (_: (csubst0 i v (CSort n1) 
c2)).(\lambda (e: C).(\lambda (H1: (drop (S n0) O (CSort n1) e)).(and3_ind 
(eq C e (CSort n1)) (eq nat (S n0) O) (eq nat O O) (or4 (drop (S n0) O c2 e) 
(ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k u)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus i (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (s k (S 
n0))) v e1 e2)))))))) (\lambda (H2: (eq C e (CSort n1))).(\lambda (H3: (eq 
nat (S n0) O)).(\lambda (_: (eq nat O O)).(eq_ind_r C (CSort n1) (\lambda (c: 
C).(or4 (drop (S n0) O c2 c) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e0 k u)))))) (\lambda (k: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead 
e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 k 
u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O c2 (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O c2 (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k (S n0))) v u w)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i (s k (S n0))) v e1 e2))))))))) (let H5 \def (eq_ind 
nat (S n0) (\lambda (ee: nat).(match ee in nat return (\lambda (_: nat).Prop) 
with [O \Rightarrow False | (S _) \Rightarrow True])) I O H3) in (False_ind 
(or4 (drop (S n0) O c2 (CSort n1)) (ex3_4 K C T T (\lambda (k: K).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CSort n1) (CHead e0 k u)))))) 
(\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) 
O c2 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus i (s k (S n0))) v u w)))))) (ex3_4 K C C T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CSort 
n1) (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k u)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (s k 
(S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CSort n1) (CHead e1 
k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus i (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (s k (S n0))) v e1 
e2)))))))) H5)) e H2)))) (drop_gen_sort n1 (S n0) O e H1)))))))) (\lambda (c: 
C).(\lambda (H0: ((\forall (c2: C).(\forall (v: T).((csubst0 i v c c2) \to 
(\forall (e: C).((drop (S n0) O c e) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C 
T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k (S n0))) v u w)))))) 
(ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k u)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (s k 
(S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus i (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (s k (S n0))) v e1 
e2))))))))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c2: C).(\lambda 
(v: T).(\lambda (H1: (csubst0 i v (CHead c k t) c2)).(\lambda (e: C).(\lambda 
(H2: (drop (S n0) O (CHead c k t) e)).(or3_ind (ex3_2 T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (u2: T).(\lambda (_: 
nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j 
v t u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat i (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c c3)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat i (s k j))))) (\lambda (u2: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3))))) (or4 (drop (S 
n0) O c2 e) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 k0 
w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 
u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O c2 (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c2 (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus i (s k0 (S n0))) v e1 e2)))))))) 
(\lambda (H3: (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat i (s k 
j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda 
(u2: T).(\lambda (j: nat).(subst0 j v t u2))))).(ex3_2_ind T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (u2: T).(\lambda (_: 
nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j 
v t u2))) (or4 (drop (S n0) O c2 e) (ex3_4 K C T T (\lambda (k0: K).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda 
(k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 
(CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus i (s k0 (S n0))) v u w)))))) (ex3_4 K C C T 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (s k0 
(S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 
u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus i (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (s k0 
(S n0))) v e1 e2)))))))) (\lambda (x0: T).(\lambda (x1: nat).(\lambda (H4: 
(eq nat i (s k x1))).(\lambda (H5: (eq C c2 (CHead c k x0))).(\lambda (_: 
(subst0 x1 v t x0)).(eq_ind_r C (CHead c k x0) (\lambda (c0: C).(or4 (drop (S 
n0) O c0 e) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead e0 k0 
w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 
u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O c0 (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c0 (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus i (s k0 (S n0))) v e1 e2))))))))) (let 
H7 \def (eq_ind nat i (\lambda (n1: nat).(\forall (c3: C).(\forall (v0: 
T).((csubst0 n1 v0 c c3) \to (\forall (e0: C).((drop (S n0) O c e0) \to (or4 
(drop (S n0) O c3 e0) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e0 (CHead e1 k0 u)))))) (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c3 
(CHead e1 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus n1 (s k0 (S n0))) v0 u w)))))) (ex3_4 K C C 
T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e0 
(CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O c3 (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus n1 (s k0 
(S n0))) v0 e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e0 (CHead e1 k0 
u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c3 (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus n1 (s k0 (S n0))) v0 u w)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus n1 (s k0 
(S n0))) v0 e1 e2)))))))))))))) H0 (s k x1) H4) in (let H8 \def (eq_ind nat i 
(\lambda (n1: nat).(lt (S n0) n1)) H (s k x1) H4) in (eq_ind_r nat (s k x1) 
(\lambda (n1: nat).(or4 (drop (S n0) O (CHead c k x0) e) (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c k x0) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus n1 (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O 
(CHead c k x0) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus n1 (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead c k x0) (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus n1 (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus n1 (s k0 
(S n0))) v e1 e2))))))))) (K_ind (\lambda (k0: K).((drop (r k0 n0) O c e) \to 
(((\forall (c3: C).(\forall (v0: T).((csubst0 (s k0 x1) v0 c c3) \to (\forall 
(e0: C).((drop (S n0) O c e0) \to (or4 (drop (S n0) O c3 e0) (ex3_4 K C T T 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (u: T).(\lambda (_: T).(eq C e0 
(CHead e1 k1 u)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c3 (CHead e1 k1 w)))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k0 x1) 
(s k1 (S n0))) v0 u w)))))) (ex3_4 K C C T (\lambda (k1: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e0 (CHead e1 k1 u)))))) (\lambda 
(k1: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c3 
(CHead e2 k1 u)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s k0 x1) (s k1 (S n0))) v0 e1 e2)))))) 
(ex4_5 K C C T T (\lambda (k1: K).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e0 (CHead e1 k1 u))))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O c3 (CHead e2 k1 w))))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k0 x1) (s k1 (S n0))) v0 
u w)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus (s k0 x1) (s k1 (S n0))) v0 e1 
e2)))))))))))))) \to ((lt (S n0) (s k0 x1)) \to (or4 (drop (S n0) O (CHead c 
k0 x0) e) (ex3_4 K C T T (\lambda (k1: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 k1 u)))))) (\lambda (k1: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c k0 x0) (CHead 
e0 k1 w)))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s k0 x1) (s k1 (S n0))) v u w)))))) (ex3_4 K C C T 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 k1 u)))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead c k0 x0) (CHead e2 k1 u)))))) 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s k0 x1) (s k1 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k1: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k1 u))))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c k0 x0) (CHead e2 
k1 w))))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s k0 x1) (s k1 (S n0))) v u w)))))) 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus (s k0 x1) (s k1 (S n0))) v e1 e2)))))))))))) (\lambda 
(b: B).(\lambda (H9: (drop (r (Bind b) n0) O c e)).(\lambda (_: ((\forall 
(c3: C).(\forall (v0: T).((csubst0 (s (Bind b) x1) v0 c c3) \to (\forall (e0: 
C).((drop (S n0) O c e0) \to (or4 (drop (S n0) O c3 e0) (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (u: T).(\lambda (_: T).(eq C e0 
(CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c3 (CHead e1 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
x1) (s k0 (S n0))) v0 u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e0 (CHead e1 k0 u)))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c3 
(CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 (S n0))) v0 e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e0 (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c3 (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
x1) (s k0 (S n0))) v0 u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 
(S n0))) v0 e1 e2))))))))))))))).(\lambda (_: (lt (S n0) (s (Bind b) 
x1))).(or4_intro0 (drop (S n0) O (CHead c (Bind b) x0) e) (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c (Bind b) x0) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) x1) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 
u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead c (Bind b) x0) (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) x1) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c (Bind b) x0) 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x1) (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 (S n0))) v e1 
e2))))))) (drop_drop (Bind b) n0 c e H9 x0)))))) (\lambda (f: F).(\lambda 
(H9: (drop (r (Flat f) n0) O c e)).(\lambda (_: ((\forall (c3: C).(\forall 
(v0: T).((csubst0 (s (Flat f) x1) v0 c c3) \to (\forall (e0: C).((drop (S n0) 
O c e0) \to (or4 (drop (S n0) O c3 e0) (ex3_4 K C T T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (u: T).(\lambda (_: T).(eq C e0 (CHead e1 k0 
u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c3 (CHead e1 k0 w)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x1) (s k0 (S 
n0))) v0 u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C e0 (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c3 (CHead 
e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s (Flat f) x1) (s k0 (S n0))) v0 e1 e2)))))) (ex4_5 K C C 
T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e0 (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c3 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x1) (s k0 (S 
n0))) v0 u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) x1) (s k0 (S 
n0))) v0 e1 e2))))))))))))))).(\lambda (_: (lt (S n0) (s (Flat f) 
x1))).(or4_intro0 (drop (S n0) O (CHead c (Flat f) x0) e) (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c (Flat f) x0) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) x1) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 
u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead c (Flat f) x0) (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) x1) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c (Flat f) x0) 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x1) (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) x1) (s k0 (S n0))) v e1 
e2))))))) (drop_drop (Flat f) n0 c e H9 x0)))))) k (drop_gen_drop k c e t n0 
H2) H7 H8) i H4))) c2 H5)))))) H3)) (\lambda (H3: (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j 
v c c3))))).(ex3_2_ind C nat (\lambda (_: C).(\lambda (j: nat).(eq nat i (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c c3))) (or4 (drop (S n0) O c2 e) 
(ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k0 (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k0 
u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus i (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k0 w))))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (s k0 
(S n0))) v e1 e2)))))))) (\lambda (x0: C).(\lambda (x1: nat).(\lambda (H4: 
(eq nat i (s k x1))).(\lambda (H5: (eq C c2 (CHead x0 k t))).(\lambda (H6: 
(csubst0 x1 v c x0)).(eq_ind_r C (CHead x0 k t) (\lambda (c0: C).(or4 (drop 
(S n0) O c0 e) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead e0 k0 
w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 
u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O c0 (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c0 (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus i (s k0 (S n0))) v e1 e2))))))))) (let 
H7 \def (eq_ind nat i (\lambda (n1: nat).(\forall (c3: C).(\forall (v0: 
T).((csubst0 n1 v0 c c3) \to (\forall (e0: C).((drop (S n0) O c e0) \to (or4 
(drop (S n0) O c3 e0) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e0 (CHead e1 k0 u)))))) (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c3 
(CHead e1 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus n1 (s k0 (S n0))) v0 u w)))))) (ex3_4 K C C 
T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e0 
(CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O c3 (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus n1 (s k0 
(S n0))) v0 e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e0 (CHead e1 k0 
u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c3 (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus n1 (s k0 (S n0))) v0 u w)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus n1 (s k0 
(S n0))) v0 e1 e2)))))))))))))) H0 (s k x1) H4) in (let H8 \def (eq_ind nat i 
(\lambda (n1: nat).(lt (S n0) n1)) H (s k x1) H4) in (eq_ind_r nat (s k x1) 
(\lambda (n1: nat).(or4 (drop (S n0) O (CHead x0 k t) e) (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 k t) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus n1 (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O 
(CHead x0 k t) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus n1 (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x0 k t) (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus n1 (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus n1 (s k0 
(S n0))) v e1 e2))))))))) (K_ind (\lambda (k0: K).((drop (r k0 n0) O c e) \to 
(((\forall (c3: C).(\forall (v0: T).((csubst0 (s k0 x1) v0 c c3) \to (\forall 
(e0: C).((drop (S n0) O c e0) \to (or4 (drop (S n0) O c3 e0) (ex3_4 K C T T 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (u: T).(\lambda (_: T).(eq C e0 
(CHead e1 k1 u)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c3 (CHead e1 k1 w)))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k0 x1) 
(s k1 (S n0))) v0 u w)))))) (ex3_4 K C C T (\lambda (k1: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e0 (CHead e1 k1 u)))))) (\lambda 
(k1: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c3 
(CHead e2 k1 u)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s k0 x1) (s k1 (S n0))) v0 e1 e2)))))) 
(ex4_5 K C C T T (\lambda (k1: K).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e0 (CHead e1 k1 u))))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O c3 (CHead e2 k1 w))))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k0 x1) (s k1 (S n0))) v0 
u w)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus (s k0 x1) (s k1 (S n0))) v0 e1 
e2)))))))))))))) \to ((lt (S n0) (s k0 x1)) \to (or4 (drop (S n0) O (CHead x0 
k0 t) e) (ex3_4 K C T T (\lambda (k1: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 k1 u)))))) (\lambda (k1: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 k0 t) (CHead 
e0 k1 w)))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s k0 x1) (s k1 (S n0))) v u w)))))) (ex3_4 K C C T 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 k1 u)))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x0 k0 t) (CHead e2 k1 u)))))) 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s k0 x1) (s k1 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k1: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k1 u))))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 k0 t) (CHead e2 
k1 w))))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s k0 x1) (s k1 (S n0))) v u w)))))) 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus (s k0 x1) (s k1 (S n0))) v e1 e2)))))))))))) (\lambda 
(b: B).(\lambda (H9: (drop (r (Bind b) n0) O c e)).(\lambda (_: ((\forall 
(c3: C).(\forall (v0: T).((csubst0 (s (Bind b) x1) v0 c c3) \to (\forall (e0: 
C).((drop (S n0) O c e0) \to (or4 (drop (S n0) O c3 e0) (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (u: T).(\lambda (_: T).(eq C e0 
(CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c3 (CHead e1 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
x1) (s k0 (S n0))) v0 u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e0 (CHead e1 k0 u)))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c3 
(CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 (S n0))) v0 e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e0 (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c3 (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
x1) (s k0 (S n0))) v0 u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 
(S n0))) v0 e1 e2))))))))))))))).(\lambda (H11: (lt (S n0) (s (Bind b) 
x1))).(let H12 \def (IHn x1 (le_S_n (S n0) x1 H11) c x0 v H6 e H9) in 
(or4_ind (drop n0 O x0 e) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O x0 (CHead e0 
k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus x1 (s k0 n0)) v u w)))))) (ex3_4 K C C T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 
u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop n0 O x0 (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus x1 (s k0 n0)) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop n0 O x0 (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus x1 (s k0 
n0)) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus x1 (s k0 n0)) v e1 e2))))))) (or4 
(drop (S n0) O (CHead x0 (Bind b) t) e) (ex3_4 K C T T (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k0 
u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e0 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
x1) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 
(Bind b) t) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) x1) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s 
(Bind b) x1) (s k0 (S n0))) v e1 e2)))))))) (\lambda (H13: (drop n0 O x0 
e)).(or4_intro0 (drop (S n0) O (CHead x0 (Bind b) t) e) (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) x1) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 
u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) x1) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x1) (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 (S n0))) v e1 
e2))))))) (drop_drop (Bind b) n0 x0 e H13 t))) (\lambda (H13: (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop n0 O x0 (CHead e0 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus x1 (s k0 
n0)) v u w))))))).(ex3_4_ind K C T T (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O x0 (CHead e0 
k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus x1 (s k0 n0)) v u w))))) (or4 (drop (S n0) O (CHead x0 
(Bind b) t) e) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) 
(CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Bind b) x1) (s k0 (S n0))) v u w)))))) 
(ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 k0 
u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s (Bind b) x1) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C 
T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead 
x0 (Bind b) t) (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
x1) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 
(S n0))) v e1 e2)))))))) (\lambda (x2: K).(\lambda (x3: C).(\lambda (x4: 
T).(\lambda (x5: T).(\lambda (H14: (eq C e (CHead x3 x2 x4))).(\lambda (H15: 
(drop n0 O x0 (CHead x3 x2 x5))).(\lambda (H16: (subst0 (minus x1 (s x2 n0)) 
v x4 x5)).(eq_ind_r C (CHead x3 x2 x4) (\lambda (c0: C).(or4 (drop (S n0) O 
(CHead x0 (Bind b) t) c0) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e0 k0 u)))))) (\lambda 
(k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O 
(CHead x0 (Bind b) t) (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x1) (s k0 (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C c0 (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 
(Bind b) t) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) x1) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s 
(Bind b) x1) (s k0 (S n0))) v e1 e2))))))))) (or4_intro1 (drop (S n0) O 
(CHead x0 (Bind b) t) (CHead x3 x2 x4)) (ex3_4 K C T T (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x3 x2 x4) 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) x1) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x3 x2 
x4) (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 k0 u)))))) 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Bind b) x1) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq 
C (CHead x3 x2 x4) (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 
(Bind b) t) (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x1) (s k0 
(S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 (S 
n0))) v e1 e2))))))) (ex3_4_intro K C T T (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x3 x2 x4) (CHead e0 k0 
u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e0 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
x1) (s k0 (S n0))) v u w))))) x2 x3 x4 x5 (refl_equal C (CHead x3 x2 x4)) 
(drop_drop (Bind b) n0 x0 (CHead x3 x2 x5) H15 t) (eq_ind_r nat (S (s x2 n0)) 
(\lambda (n1: nat).(subst0 (minus (s (Bind b) x1) n1) v x4 x5)) H16 (s x2 (S 
n0)) (s_S x2 n0)))) e H14)))))))) H13)) (\lambda (H13: (ex3_4 K C C T 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop n0 O x0 (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus x1 (s k0 
n0)) v e1 e2))))))).(ex3_4_ind K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop n0 O x0 (CHead e2 
k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus x1 (s k0 n0)) v e1 e2))))) (or4 (drop (S n0) O (CHead x0 
(Bind b) t) e) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) 
(CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Bind b) x1) (s k0 (S n0))) v u w)))))) 
(ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 k0 
u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s (Bind b) x1) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C 
T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead 
x0 (Bind b) t) (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
x1) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 
(S n0))) v e1 e2)))))))) (\lambda (x2: K).(\lambda (x3: C).(\lambda (x4: 
C).(\lambda (x5: T).(\lambda (H14: (eq C e (CHead x3 x2 x5))).(\lambda (H15: 
(drop n0 O x0 (CHead x4 x2 x5))).(\lambda (H16: (csubst0 (minus x1 (s x2 n0)) 
v x3 x4)).(eq_ind_r C (CHead x3 x2 x5) (\lambda (c0: C).(or4 (drop (S n0) O 
(CHead x0 (Bind b) t) c0) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e0 k0 u)))))) (\lambda 
(k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O 
(CHead x0 (Bind b) t) (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x1) (s k0 (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C c0 (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 
(Bind b) t) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) x1) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s 
(Bind b) x1) (s k0 (S n0))) v e1 e2))))))))) (or4_intro2 (drop (S n0) O 
(CHead x0 (Bind b) t) (CHead x3 x2 x5)) (ex3_4 K C T T (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x3 x2 x5) 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) x1) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x3 x2 
x5) (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 k0 u)))))) 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Bind b) x1) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq 
C (CHead x3 x2 x5) (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 
(Bind b) t) (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x1) (s k0 
(S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 (S 
n0))) v e1 e2))))))) (ex3_4_intro K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x3 x2 x5) (CHead e1 k0 
u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) x1) (s k0 (S n0))) v e1 e2))))) x2 x3 x4 x5 (refl_equal C (CHead x3 x2 
x5)) (drop_drop (Bind b) n0 x0 (CHead x4 x2 x5) H15 t) (eq_ind_r nat (S (s x2 
n0)) (\lambda (n1: nat).(csubst0 (minus (s (Bind b) x1) n1) v x3 x4)) H16 (s 
x2 (S n0)) (s_S x2 n0)))) e H14)))))))) H13)) (\lambda (H13: (ex4_5 K C C T T 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O x0 (CHead e2 
k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus x1 (s k0 n0)) v u w)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus x1 (s k0 n0)) v e1 e2)))))))).(ex4_5_ind K C C T T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop n0 O x0 (CHead e2 k0 w))))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus x1 (s k0 n0)) v u w)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus x1 (s k0 
n0)) v e1 e2)))))) (or4 (drop (S n0) O (CHead x0 (Bind b) t) e) (ex3_4 K C T 
T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) x1) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 
u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) x1) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x1) (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 (S n0))) v e1 
e2)))))))) (\lambda (x2: K).(\lambda (x3: C).(\lambda (x4: C).(\lambda (x5: 
T).(\lambda (x6: T).(\lambda (H14: (eq C e (CHead x3 x2 x5))).(\lambda (H15: 
(drop n0 O x0 (CHead x4 x2 x6))).(\lambda (H16: (subst0 (minus x1 (s x2 n0)) 
v x5 x6)).(\lambda (H17: (csubst0 (minus x1 (s x2 n0)) v x3 x4)).(eq_ind_r C 
(CHead x3 x2 x5) (\lambda (c0: C).(or4 (drop (S n0) O (CHead x0 (Bind b) t) 
c0) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda 
(_: T).(eq C c0 (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) 
(CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Bind b) x1) (s k0 (S n0))) v u w)))))) 
(ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 k0 
u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s (Bind b) x1) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C 
T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C c0 (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead 
x0 (Bind b) t) (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
x1) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 
(S n0))) v e1 e2))))))))) (or4_intro3 (drop (S n0) O (CHead x0 (Bind b) t) 
(CHead x3 x2 x5)) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C (CHead x3 x2 x5) (CHead e0 k0 u)))))) (\lambda 
(k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O 
(CHead x0 (Bind b) t) (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x1) (s k0 (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C (CHead x3 x2 x5) (CHead e1 k0 u)))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O 
(CHead x0 (Bind b) t) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 (S 
n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x3 x2 x5) 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x1) (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x1) (s k0 (S n0))) v e1 
e2))))))) (ex4_5_intro K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x3 x2 x5) (CHead e1 k0 
u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 k0 w))))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s (Bind b) x1) (s k0 (S n0))) v u w)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Bind b) x1) (s k0 (S n0))) v e1 e2)))))) x2 x3 x4 x5 x6 
(refl_equal C (CHead x3 x2 x5)) (drop_drop (Bind b) n0 x0 (CHead x4 x2 x6) 
H15 t) (eq_ind_r nat (S (s x2 n0)) (\lambda (n1: nat).(subst0 (minus (s (Bind 
b) x1) n1) v x5 x6)) H16 (s x2 (S n0)) (s_S x2 n0)) (eq_ind_r nat (S (s x2 
n0)) (\lambda (n1: nat).(csubst0 (minus (s (Bind b) x1) n1) v x3 x4)) H17 (s 
x2 (S n0)) (s_S x2 n0)))) e H14)))))))))) H13)) H12)))))) (\lambda (f: 
F).(\lambda (H9: (drop (r (Flat f) n0) O c e)).(\lambda (H10: ((\forall (c3: 
C).(\forall (v0: T).((csubst0 (s (Flat f) x1) v0 c c3) \to (\forall (e0: 
C).((drop (S n0) O c e0) \to (or4 (drop (S n0) O c3 e0) (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (u: T).(\lambda (_: T).(eq C e0 
(CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c3 (CHead e1 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) 
x1) (s k0 (S n0))) v0 u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e0 (CHead e1 k0 u)))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c3 
(CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s (Flat f) x1) (s k0 (S n0))) v0 e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e0 (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c3 (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) 
x1) (s k0 (S n0))) v0 u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) x1) (s k0 
(S n0))) v0 e1 e2))))))))))))))).(\lambda (_: (lt (S n0) (s (Flat f) 
x1))).(let H12 \def (H10 x0 v H6 e H9) in (or4_ind (drop (S n0) O x0 e) 
(ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O x0 (CHead e0 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus x1 (s k0 (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O x0 (CHead e2 k0 
u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus x1 (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O x0 (CHead e2 k0 w))))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus x1 (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus x1 
(s k0 (S n0))) v e1 e2))))))) (or4 (drop (S n0) O (CHead x0 (Flat f) t) e) 
(ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e0 k0 
w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) x1) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 k0 u)))))) 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Flat f) x1) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x1) (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) x1) (s k0 (S n0))) v e1 
e2)))))))) (\lambda (H13: (drop (S n0) O x0 e)).(or4_intro0 (drop (S n0) O 
(CHead x0 (Flat f) t) e) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 
(Flat f) t) (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x1) (s k0 (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s (Flat f) x1) (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) x1) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s 
(Flat f) x1) (s k0 (S n0))) v e1 e2))))))) (drop_drop (Flat f) n0 x0 e H13 
t))) (\lambda (H13: (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O x0 (CHead e0 k0 
w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus x1 (s k0 (S n0))) v u w))))))).(ex3_4_ind K C T T (\lambda 
(k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k0 
u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O x0 (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus x1 (s k0 (S n0))) v u 
w))))) (or4 (drop (S n0) O (CHead x0 (Flat f) t) e) (ex3_4 K C T T (\lambda 
(k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k0 
u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e0 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) 
x1) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 
(Flat f) t) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) x1) (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) x1) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s 
(Flat f) x1) (s k0 (S n0))) v e1 e2)))))))) (\lambda (x2: K).(\lambda (x3: 
C).(\lambda (x4: T).(\lambda (x5: T).(\lambda (H14: (eq C e (CHead x3 x2 
x4))).(\lambda (H15: (drop (S n0) O x0 (CHead x3 x2 x5))).(\lambda (H16: 
(subst0 (minus x1 (s x2 (S n0))) v x4 x5)).(eq_ind_r C (CHead x3 x2 x4) 
(\lambda (c0: C).(or4 (drop (S n0) O (CHead x0 (Flat f) t) c0) (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) x1) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 
k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) x1) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x1) (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) x1) (s k0 (S n0))) v e1 
e2))))))))) (or4_intro1 (drop (S n0) O (CHead x0 (Flat f) t) (CHead x3 x2 
x4)) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead x3 x2 x4) (CHead e0 k0 u)))))) (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 
(Flat f) t) (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x1) (s k0 (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C (CHead x3 x2 x4) (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 
(Flat f) t) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) x1) (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x3 x2 x4) (CHead e1 k0 
u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 k0 w))))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) x1) (s k0 (S n0))) v u w)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Flat f) x1) (s k0 (S n0))) v e1 e2))))))) (ex3_4_intro K C T T 
(\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead x3 x2 x4) (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Flat f) x1) (s k0 (S n0))) v u w))))) 
x2 x3 x4 x5 (refl_equal C (CHead x3 x2 x4)) (drop_drop (Flat f) n0 x0 (CHead 
x3 x2 x5) H15 t) H16)) e H14)))))))) H13)) (\lambda (H13: (ex3_4 K C C T 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O x0 (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus x1 (s k0 
(S n0))) v e1 e2))))))).(ex3_4_ind K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O x0 (CHead 
e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus x1 (s k0 (S n0))) v e1 e2))))) (or4 (drop (S n0) O (CHead 
x0 (Flat f) t) e) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Flat f) x1) (s k0 (S n0))) v u w)))))) 
(ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 k0 
u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s (Flat f) x1) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C 
T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead 
x0 (Flat f) t) (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) 
x1) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) x1) (s k0 
(S n0))) v e1 e2)))))))) (\lambda (x2: K).(\lambda (x3: C).(\lambda (x4: 
C).(\lambda (x5: T).(\lambda (H14: (eq C e (CHead x3 x2 x5))).(\lambda (H15: 
(drop (S n0) O x0 (CHead x4 x2 x5))).(\lambda (H16: (csubst0 (minus x1 (s x2 
(S n0))) v x3 x4)).(eq_ind_r C (CHead x3 x2 x5) (\lambda (c0: C).(or4 (drop 
(S n0) O (CHead x0 (Flat f) t) c0) (ex3_4 K C T T (\lambda (k0: K).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e0 k0 u)))))) 
(\lambda (k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x0 (Flat f) t) (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x1) (s k0 
(S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 k0 u)))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O 
(CHead x0 (Flat f) t) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) x1) (s k0 (S 
n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e1 k0 
u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 k0 w))))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) x1) (s k0 (S n0))) v u w)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Flat f) x1) (s k0 (S n0))) v e1 e2))))))))) (or4_intro2 (drop (S 
n0) O (CHead x0 (Flat f) t) (CHead x3 x2 x5)) (ex3_4 K C T T (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x3 x2 x5) 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) x1) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x3 x2 
x5) (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 k0 u)))))) 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Flat f) x1) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq 
C (CHead x3 x2 x5) (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 
(Flat f) t) (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x1) (s k0 
(S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) x1) (s k0 (S 
n0))) v e1 e2))))))) (ex3_4_intro K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x3 x2 x5) (CHead e1 k0 
u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) x1) (s k0 (S n0))) v e1 e2))))) x2 x3 x4 x5 (refl_equal C (CHead x3 x2 
x5)) (drop_drop (Flat f) n0 x0 (CHead x4 x2 x5) H15 t) H16)) e H14)))))))) 
H13)) (\lambda (H13: (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 
u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O x0 (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus x1 (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus x1 (s k0 
(S n0))) v e1 e2)))))))).(ex4_5_ind K C C T T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 
u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O x0 (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus x1 (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus x1 (s k0 
(S n0))) v e1 e2)))))) (or4 (drop (S n0) O (CHead x0 (Flat f) t) e) (ex3_4 K 
C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) x1) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 
u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) x1) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x1) (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) x1) (s k0 (S n0))) v e1 
e2)))))))) (\lambda (x2: K).(\lambda (x3: C).(\lambda (x4: C).(\lambda (x5: 
T).(\lambda (x6: T).(\lambda (H14: (eq C e (CHead x3 x2 x5))).(\lambda (H15: 
(drop (S n0) O x0 (CHead x4 x2 x6))).(\lambda (H16: (subst0 (minus x1 (s x2 
(S n0))) v x5 x6)).(\lambda (H17: (csubst0 (minus x1 (s x2 (S n0))) v x3 
x4)).(eq_ind_r C (CHead x3 x2 x5) (\lambda (c0: C).(or4 (drop (S n0) O (CHead 
x0 (Flat f) t) c0) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C c0 (CHead e0 k0 u)))))) (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 
(Flat f) t) (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x1) (s k0 (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s (Flat f) x1) (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) x1) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s 
(Flat f) x1) (s k0 (S n0))) v e1 e2))))))))) (or4_intro3 (drop (S n0) O 
(CHead x0 (Flat f) t) (CHead x3 x2 x5)) (ex3_4 K C T T (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x3 x2 x5) 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) x1) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x3 x2 
x5) (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 k0 u)))))) 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Flat f) x1) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq 
C (CHead x3 x2 x5) (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 
(Flat f) t) (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x1) (s k0 
(S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) x1) (s k0 (S 
n0))) v e1 e2))))))) (ex4_5_intro K C C T T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x3 x2 x5) 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x1) (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) x1) (s k0 (S n0))) v e1 
e2)))))) x2 x3 x4 x5 x6 (refl_equal C (CHead x3 x2 x5)) (drop_drop (Flat f) 
n0 x0 (CHead x4 x2 x6) H15 t) H16 H17)) e H14)))))))))) H13)) H12)))))) k 
(drop_gen_drop k c e t n0 H2) H7 H8) i H4))) c2 H5)))))) H3)) (\lambda (H3: 
(ex4_3 T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat i (s 
k j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead 
c3 k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t 
u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c 
c3)))))).(ex4_3_ind T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat i (s k j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda 
(j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c c3)))) (or4 (drop (S n0) O c2 e) (ex3_4 K C T T (\lambda 
(k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k0 
u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c2 (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k0 (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k0 u)))))) 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus i (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k0 w))))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (s k0 
(S n0))) v e1 e2)))))))) (\lambda (x0: T).(\lambda (x1: C).(\lambda (x2: 
nat).(\lambda (H4: (eq nat i (s k x2))).(\lambda (H5: (eq C c2 (CHead x1 k 
x0))).(\lambda (_: (subst0 x2 v t x0)).(\lambda (H7: (csubst0 x2 v c 
x1)).(eq_ind_r C (CHead x1 k x0) (\lambda (c0: C).(or4 (drop (S n0) O c0 e) 
(ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead e0 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k0 (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c0 (CHead e2 k0 
u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus i (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead e2 k0 w))))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (s k0 
(S n0))) v e1 e2))))))))) (let H8 \def (eq_ind nat i (\lambda (n1: 
nat).(\forall (c3: C).(\forall (v0: T).((csubst0 n1 v0 c c3) \to (\forall 
(e0: C).((drop (S n0) O c e0) \to (or4 (drop (S n0) O c3 e0) (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (u: T).(\lambda (_: T).(eq C e0 
(CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c3 (CHead e1 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus n1 (s k0 (S 
n0))) v0 u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C e0 (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c3 (CHead 
e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus n1 (s k0 (S n0))) v0 e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e0 (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c3 (CHead e2 k0 w))))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus n1 (s k0 (S n0))) v0 u w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus n1 
(s k0 (S n0))) v0 e1 e2)))))))))))))) H0 (s k x2) H4) in (let H9 \def (eq_ind 
nat i (\lambda (n1: nat).(lt (S n0) n1)) H (s k x2) H4) in (eq_ind_r nat (s k 
x2) (\lambda (n1: nat).(or4 (drop (S n0) O (CHead x1 k x0) e) (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 k x0) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus n1 (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O 
(CHead x1 k x0) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus n1 (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x1 k x0) (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus n1 (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus n1 (s k0 
(S n0))) v e1 e2))))))))) (K_ind (\lambda (k0: K).((drop (r k0 n0) O c e) \to 
(((\forall (c3: C).(\forall (v0: T).((csubst0 (s k0 x2) v0 c c3) \to (\forall 
(e0: C).((drop (S n0) O c e0) \to (or4 (drop (S n0) O c3 e0) (ex3_4 K C T T 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (u: T).(\lambda (_: T).(eq C e0 
(CHead e1 k1 u)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c3 (CHead e1 k1 w)))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k0 x2) 
(s k1 (S n0))) v0 u w)))))) (ex3_4 K C C T (\lambda (k1: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e0 (CHead e1 k1 u)))))) (\lambda 
(k1: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c3 
(CHead e2 k1 u)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s k0 x2) (s k1 (S n0))) v0 e1 e2)))))) 
(ex4_5 K C C T T (\lambda (k1: K).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e0 (CHead e1 k1 u))))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O c3 (CHead e2 k1 w))))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k0 x2) (s k1 (S n0))) v0 
u w)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus (s k0 x2) (s k1 (S n0))) v0 e1 
e2)))))))))))))) \to ((lt (S n0) (s k0 x2)) \to (or4 (drop (S n0) O (CHead x1 
k0 x0) e) (ex3_4 K C T T (\lambda (k1: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 k1 u)))))) (\lambda (k1: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 k0 x0) 
(CHead e0 k1 w)))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s k0 x2) (s k1 (S n0))) v u w)))))) (ex3_4 
K C C T (\lambda (k1: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq 
C e (CHead e1 k1 u)))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x1 k0 x0) (CHead e2 k1 u)))))) 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s k0 x2) (s k1 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k1: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k1 u))))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 k0 x0) (CHead e2 
k1 w))))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s k0 x2) (s k1 (S n0))) v u w)))))) 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus (s k0 x2) (s k1 (S n0))) v e1 e2)))))))))))) (\lambda 
(b: B).(\lambda (H10: (drop (r (Bind b) n0) O c e)).(\lambda (_: ((\forall 
(c3: C).(\forall (v0: T).((csubst0 (s (Bind b) x2) v0 c c3) \to (\forall (e0: 
C).((drop (S n0) O c e0) \to (or4 (drop (S n0) O c3 e0) (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (u: T).(\lambda (_: T).(eq C e0 
(CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c3 (CHead e1 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
x2) (s k0 (S n0))) v0 u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e0 (CHead e1 k0 u)))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c3 
(CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s (Bind b) x2) (s k0 (S n0))) v0 e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e0 (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c3 (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
x2) (s k0 (S n0))) v0 u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x2) (s k0 
(S n0))) v0 e1 e2))))))))))))))).(\lambda (H12: (lt (S n0) (s (Bind b) 
x2))).(let H13 \def (IHn x2 (le_S_n (S n0) x2 H12) c x1 v H7 e H10) in 
(or4_ind (drop n0 O x1 e) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O x1 (CHead e0 
k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus x2 (s k0 n0)) v u w)))))) (ex3_4 K C C T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 
u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop n0 O x1 (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus x2 (s k0 n0)) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop n0 O x1 (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus x2 (s k0 
n0)) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus x2 (s k0 n0)) v e1 e2))))))) (or4 
(drop (S n0) O (CHead x1 (Bind b) x0) e) (ex3_4 K C T T (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k0 
u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e0 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
x2) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 
(Bind b) x0) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) x2) (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) x2) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s 
(Bind b) x2) (s k0 (S n0))) v e1 e2)))))))) (\lambda (H14: (drop n0 O x1 
e)).(or4_intro0 (drop (S n0) O (CHead x1 (Bind b) x0) e) (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) x2) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 
u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) x2) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x2) (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x2) (s k0 (S n0))) v e1 
e2))))))) (drop_drop (Bind b) n0 x1 e H14 x0))) (\lambda (H14: (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop n0 O x1 (CHead e0 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus x2 (s k0 
n0)) v u w))))))).(ex3_4_ind K C T T (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O x1 (CHead e0 
k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus x2 (s k0 n0)) v u w))))) (or4 (drop (S n0) O (CHead x1 
(Bind b) x0) e) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) 
(CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Bind b) x2) (s k0 (S n0))) v u w)))))) 
(ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 k0 
u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s (Bind b) x2) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C 
T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead 
x1 (Bind b) x0) (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
x2) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x2) (s k0 
(S n0))) v e1 e2)))))))) (\lambda (x3: K).(\lambda (x4: C).(\lambda (x5: 
T).(\lambda (x6: T).(\lambda (H15: (eq C e (CHead x4 x3 x5))).(\lambda (H16: 
(drop n0 O x1 (CHead x4 x3 x6))).(\lambda (H17: (subst0 (minus x2 (s x3 n0)) 
v x5 x6)).(eq_ind_r C (CHead x4 x3 x5) (\lambda (c0: C).(or4 (drop (S n0) O 
(CHead x1 (Bind b) x0) c0) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e0 k0 u)))))) (\lambda 
(k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O 
(CHead x1 (Bind b) x0) (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x2) (s k0 (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C c0 (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 
(Bind b) x0) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) x2) (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) x2) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s 
(Bind b) x2) (s k0 (S n0))) v e1 e2))))))))) (or4_intro1 (drop (S n0) O 
(CHead x1 (Bind b) x0) (CHead x4 x3 x5)) (ex3_4 K C T T (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x4 x3 x5) 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) x2) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x4 x3 
x5) (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 k0 u)))))) 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Bind b) x2) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq 
C (CHead x4 x3 x5) (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 
(Bind b) x0) (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x2) (s k0 
(S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x2) (s k0 (S 
n0))) v e1 e2))))))) (ex3_4_intro K C T T (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x4 x3 x5) (CHead e0 k0 
u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e0 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
x2) (s k0 (S n0))) v u w))))) x3 x4 x5 x6 (refl_equal C (CHead x4 x3 x5)) 
(drop_drop (Bind b) n0 x1 (CHead x4 x3 x6) H16 x0) (eq_ind_r nat (S (s x3 
n0)) (\lambda (n1: nat).(subst0 (minus (s (Bind b) x2) n1) v x5 x6)) H17 (s 
x3 (S n0)) (s_S x3 n0)))) e H15)))))))) H14)) (\lambda (H14: (ex3_4 K C C T 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop n0 O x1 (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus x2 (s k0 
n0)) v e1 e2))))))).(ex3_4_ind K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop n0 O x1 (CHead e2 
k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus x2 (s k0 n0)) v e1 e2))))) (or4 (drop (S n0) O (CHead x1 
(Bind b) x0) e) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) 
(CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Bind b) x2) (s k0 (S n0))) v u w)))))) 
(ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 k0 
u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s (Bind b) x2) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C 
T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead 
x1 (Bind b) x0) (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
x2) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x2) (s k0 
(S n0))) v e1 e2)))))))) (\lambda (x3: K).(\lambda (x4: C).(\lambda (x5: 
C).(\lambda (x6: T).(\lambda (H15: (eq C e (CHead x4 x3 x6))).(\lambda (H16: 
(drop n0 O x1 (CHead x5 x3 x6))).(\lambda (H17: (csubst0 (minus x2 (s x3 n0)) 
v x4 x5)).(eq_ind_r C (CHead x4 x3 x6) (\lambda (c0: C).(or4 (drop (S n0) O 
(CHead x1 (Bind b) x0) c0) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e0 k0 u)))))) (\lambda 
(k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O 
(CHead x1 (Bind b) x0) (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x2) (s k0 (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C c0 (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 
(Bind b) x0) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) x2) (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) x2) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s 
(Bind b) x2) (s k0 (S n0))) v e1 e2))))))))) (or4_intro2 (drop (S n0) O 
(CHead x1 (Bind b) x0) (CHead x4 x3 x6)) (ex3_4 K C T T (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x4 x3 x6) 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) x2) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x4 x3 
x6) (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 k0 u)))))) 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Bind b) x2) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq 
C (CHead x4 x3 x6) (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 
(Bind b) x0) (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x2) (s k0 
(S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x2) (s k0 (S 
n0))) v e1 e2))))))) (ex3_4_intro K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x4 x3 x6) (CHead e1 k0 
u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) x2) (s k0 (S n0))) v e1 e2))))) x3 x4 x5 x6 (refl_equal C (CHead x4 x3 
x6)) (drop_drop (Bind b) n0 x1 (CHead x5 x3 x6) H16 x0) (eq_ind_r nat (S (s 
x3 n0)) (\lambda (n1: nat).(csubst0 (minus (s (Bind b) x2) n1) v x4 x5)) H17 
(s x3 (S n0)) (s_S x3 n0)))) e H15)))))))) H14)) (\lambda (H14: (ex4_5 K C C 
T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O x1 (CHead 
e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus x2 (s k0 n0)) v u w)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus x2 (s k0 n0)) v e1 e2)))))))).(ex4_5_ind K C C T T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop n0 O x1 (CHead e2 k0 w))))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus x2 (s k0 n0)) v u w)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus x2 (s k0 
n0)) v e1 e2)))))) (or4 (drop (S n0) O (CHead x1 (Bind b) x0) e) (ex3_4 K C T 
T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) x2) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 
u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) x2) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x2) (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x2) (s k0 (S n0))) v e1 
e2)))))))) (\lambda (x3: K).(\lambda (x4: C).(\lambda (x5: C).(\lambda (x6: 
T).(\lambda (x7: T).(\lambda (H15: (eq C e (CHead x4 x3 x6))).(\lambda (H16: 
(drop n0 O x1 (CHead x5 x3 x7))).(\lambda (H17: (subst0 (minus x2 (s x3 n0)) 
v x6 x7)).(\lambda (H18: (csubst0 (minus x2 (s x3 n0)) v x4 x5)).(eq_ind_r C 
(CHead x4 x3 x6) (\lambda (c0: C).(or4 (drop (S n0) O (CHead x1 (Bind b) x0) 
c0) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda 
(_: T).(eq C c0 (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) 
(CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Bind b) x2) (s k0 (S n0))) v u w)))))) 
(ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 k0 
u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s (Bind b) x2) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C 
T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C c0 (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead 
x1 (Bind b) x0) (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
x2) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x2) (s k0 
(S n0))) v e1 e2))))))))) (or4_intro3 (drop (S n0) O (CHead x1 (Bind b) x0) 
(CHead x4 x3 x6)) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C (CHead x4 x3 x6) (CHead e0 k0 u)))))) (\lambda 
(k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O 
(CHead x1 (Bind b) x0) (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x2) (s k0 (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C (CHead x4 x3 x6) (CHead e1 k0 u)))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O 
(CHead x1 (Bind b) x0) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) x2) (s k0 (S 
n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x4 x3 x6) 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) x2) (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) x2) (s k0 (S n0))) v e1 
e2))))))) (ex4_5_intro K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x4 x3 x6) (CHead e1 k0 
u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 k0 
w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Bind b) x2) (s k0 (S n0))) v u w)))))) 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus (s (Bind b) x2) (s k0 (S n0))) v e1 e2)))))) x3 x4 x5 
x6 x7 (refl_equal C (CHead x4 x3 x6)) (drop_drop (Bind b) n0 x1 (CHead x5 x3 
x7) H16 x0) (eq_ind_r nat (S (s x3 n0)) (\lambda (n1: nat).(subst0 (minus (s 
(Bind b) x2) n1) v x6 x7)) H17 (s x3 (S n0)) (s_S x3 n0)) (eq_ind_r nat (S (s 
x3 n0)) (\lambda (n1: nat).(csubst0 (minus (s (Bind b) x2) n1) v x4 x5)) H18 
(s x3 (S n0)) (s_S x3 n0)))) e H15)))))))))) H14)) H13)))))) (\lambda (f: 
F).(\lambda (H10: (drop (r (Flat f) n0) O c e)).(\lambda (H11: ((\forall (c3: 
C).(\forall (v0: T).((csubst0 (s (Flat f) x2) v0 c c3) \to (\forall (e0: 
C).((drop (S n0) O c e0) \to (or4 (drop (S n0) O c3 e0) (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (u: T).(\lambda (_: T).(eq C e0 
(CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c3 (CHead e1 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) 
x2) (s k0 (S n0))) v0 u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e0 (CHead e1 k0 u)))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c3 
(CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v0 e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e0 (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c3 (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) 
x2) (s k0 (S n0))) v0 u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) x2) (s k0 
(S n0))) v0 e1 e2))))))))))))))).(\lambda (_: (lt (S n0) (s (Flat f) 
x2))).(let H13 \def (H11 x1 v H7 e H10) in (or4_ind (drop (S n0) O x1 e) 
(ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O x1 (CHead e0 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus x2 (s k0 (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O x1 (CHead e2 k0 
u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus x2 (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O x1 (CHead e2 k0 w))))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus x2 (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus x2 
(s k0 (S n0))) v e1 e2))))))) (or4 (drop (S n0) O (CHead x1 (Flat f) x0) e) 
(ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e0 k0 
w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) x2) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 k0 u)))))) 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Flat f) x2) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x2) (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v e1 
e2)))))))) (\lambda (H14: (drop (S n0) O x1 e)).(or4_intro0 (drop (S n0) O 
(CHead x1 (Flat f) x0) e) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 
(Flat f) x0) (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x2) (s k0 (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Flat f) x0) 
(CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) x2) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s 
(Flat f) x2) (s k0 (S n0))) v e1 e2))))))) (drop_drop (Flat f) n0 x1 e H14 
x0))) (\lambda (H14: (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O x1 (CHead 
e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus x2 (s k0 (S n0))) v u w))))))).(ex3_4_ind K C T T (\lambda 
(k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k0 
u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O x1 (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus x2 (s k0 (S n0))) v u 
w))))) (or4 (drop (S n0) O (CHead x1 (Flat f) x0) e) (ex3_4 K C T T (\lambda 
(k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k0 
u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e0 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) 
x2) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 
(Flat f) x0) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) x2) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s 
(Flat f) x2) (s k0 (S n0))) v e1 e2)))))))) (\lambda (x3: K).(\lambda (x4: 
C).(\lambda (x5: T).(\lambda (x6: T).(\lambda (H15: (eq C e (CHead x4 x3 
x5))).(\lambda (H16: (drop (S n0) O x1 (CHead x4 x3 x6))).(\lambda (H17: 
(subst0 (minus x2 (s x3 (S n0))) v x5 x6)).(eq_ind_r C (CHead x4 x3 x5) 
(\lambda (c0: C).(or4 (drop (S n0) O (CHead x1 (Flat f) x0) c0) (ex3_4 K C T 
T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 
(CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) x2) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 
k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) x2) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x2) (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v e1 
e2))))))))) (or4_intro1 (drop (S n0) O (CHead x1 (Flat f) x0) (CHead x4 x3 
x5)) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead x4 x3 x5) (CHead e0 k0 u)))))) (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 
(Flat f) x0) (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x2) (s k0 (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C (CHead x4 x3 x5) (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 
(Flat f) x0) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x4 x3 x5) (CHead e1 k0 
u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 k0 
w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Flat f) x2) (s k0 (S n0))) v u w)))))) 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v e1 e2))))))) 
(ex3_4_intro K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead x4 x3 x5) (CHead e0 k0 u)))))) (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 
(Flat f) x0) (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x2) (s k0 (S n0))) v u 
w))))) x3 x4 x5 x6 (refl_equal C (CHead x4 x3 x5)) (drop_drop (Flat f) n0 x1 
(CHead x4 x3 x6) H16 x0) H17)) e H15)))))))) H14)) (\lambda (H14: (ex3_4 K C 
C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O x1 (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus x2 (s k0 
(S n0))) v e1 e2))))))).(ex3_4_ind K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O x1 (CHead 
e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus x2 (s k0 (S n0))) v e1 e2))))) (or4 (drop (S n0) O (CHead 
x1 (Flat f) x0) e) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) 
(CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Flat f) x2) (s k0 (S n0))) v u w)))))) 
(ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 k0 
u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C 
T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead 
x1 (Flat f) x0) (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) 
x2) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) x2) (s k0 
(S n0))) v e1 e2)))))))) (\lambda (x3: K).(\lambda (x4: C).(\lambda (x5: 
C).(\lambda (x6: T).(\lambda (H15: (eq C e (CHead x4 x3 x6))).(\lambda (H16: 
(drop (S n0) O x1 (CHead x5 x3 x6))).(\lambda (H17: (csubst0 (minus x2 (s x3 
(S n0))) v x4 x5)).(eq_ind_r C (CHead x4 x3 x6) (\lambda (c0: C).(or4 (drop 
(S n0) O (CHead x1 (Flat f) x0) c0) (ex3_4 K C T T (\lambda (k0: K).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e0 k0 u)))))) 
(\lambda (k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x1 (Flat f) x0) (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x2) (s k0 
(S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 k0 u)))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O 
(CHead x1 (Flat f) x0) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S 
n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e1 k0 
u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 k0 
w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Flat f) x2) (s k0 (S n0))) v u w)))))) 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v e1 e2))))))))) 
(or4_intro2 (drop (S n0) O (CHead x1 (Flat f) x0) (CHead x4 x3 x6)) (ex3_4 K 
C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead x4 x3 x6) (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) 
(CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Flat f) x2) (s k0 (S n0))) v u w)))))) 
(ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C (CHead x4 x3 x6) (CHead e1 k0 u)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Flat f) x0) 
(CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x4 x3 x6) (CHead e1 k0 
u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 k0 
w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Flat f) x2) (s k0 (S n0))) v u w)))))) 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v e1 e2))))))) 
(ex3_4_intro K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C (CHead x4 x3 x6) (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 
(Flat f) x0) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v e1 
e2))))) x3 x4 x5 x6 (refl_equal C (CHead x4 x3 x6)) (drop_drop (Flat f) n0 x1 
(CHead x5 x3 x6) H16 x0) H17)) e H15)))))))) H14)) (\lambda (H14: (ex4_5 K C 
C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O x1 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus x2 (s k0 (S n0))) v u 
w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus x2 (s k0 (S n0))) v e1 
e2)))))))).(ex4_5_ind K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O x1 (CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus x2 (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus x2 (s k0 (S n0))) v e1 e2)))))) (or4 
(drop (S n0) O (CHead x1 (Flat f) x0) e) (ex3_4 K C T T (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k0 
u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e0 k0 w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) 
x2) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 
(Flat f) x0) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k0 u))))))) (\lambda 
(k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 k0 w))))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) x2) (s k0 (S n0))) v u w)))))) (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s 
(Flat f) x2) (s k0 (S n0))) v e1 e2)))))))) (\lambda (x3: K).(\lambda (x4: 
C).(\lambda (x5: C).(\lambda (x6: T).(\lambda (x7: T).(\lambda (H15: (eq C e 
(CHead x4 x3 x6))).(\lambda (H16: (drop (S n0) O x1 (CHead x5 x3 
x7))).(\lambda (H17: (subst0 (minus x2 (s x3 (S n0))) v x6 x7)).(\lambda 
(H18: (csubst0 (minus x2 (s x3 (S n0))) v x4 x5)).(eq_ind_r C (CHead x4 x3 
x6) (\lambda (c0: C).(or4 (drop (S n0) O (CHead x1 (Flat f) x0) c0) (ex3_4 K 
C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
c0 (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e0 k0 w)))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) x2) (s k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 
k0 u)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 k0 u)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) x2) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 
(CHead e1 k0 u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) 
(CHead e2 k0 w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x2) (s k0 (S 
n0))) v u w)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v e1 
e2))))))))) (or4_intro3 (drop (S n0) O (CHead x1 (Flat f) x0) (CHead x4 x3 
x6)) (ex3_4 K C T T (\lambda (k0: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead x4 x3 x6) (CHead e0 k0 u)))))) (\lambda (k0: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 
(Flat f) x0) (CHead e0 k0 w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) x2) (s k0 (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C (CHead x4 x3 x6) (CHead e1 k0 u)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 
(Flat f) x0) (CHead e2 k0 u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x4 x3 x6) (CHead e1 k0 
u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 k0 
w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Flat f) x2) (s k0 (S n0))) v u w)))))) 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v e1 e2))))))) 
(ex4_5_intro K C C T T (\lambda (k0: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x4 x3 x6) (CHead e1 k0 
u))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 k0 
w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Flat f) x2) (s k0 (S n0))) v u w)))))) 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus (s (Flat f) x2) (s k0 (S n0))) v e1 e2)))))) x3 x4 x5 
x6 x7 (refl_equal C (CHead x4 x3 x6)) (drop_drop (Flat f) n0 x1 (CHead x5 x3 
x7) H16 x0) H17 H18)) e H15)))))))))) H14)) H13)))))) k (drop_gen_drop k c e 
t n0 H2) H8 H9) i H4))) c2 H5)))))))) H3)) (csubst0_gen_head k c c2 t v i 
H1))))))))))) c1)))))) n).
(* COMMENTS
Initial nodes: 39886
END *)

theorem csubst0_drop_eq:
 \forall (n: nat).(\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 
n v c1 c2) \to (\forall (e: C).((drop n O c1 e) \to (or4 (drop n O c2 e) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop n O c2 (CHead e0 (Flat f) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u 
w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop n O c2 (CHead e2 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 
(Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop n O c2 (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2))))))))))))))
\def
 \lambda (n: nat).(nat_ind (\lambda (n0: nat).(\forall (c1: C).(\forall (c2: 
C).(\forall (v: T).((csubst0 n0 v c1 c2) \to (\forall (e: C).((drop n0 O c1 
e) \to (or4 (drop n0 O c2 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O 
c2 (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop n0 O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O c2 (CHead e2 
(Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (v: T).(\lambda 
(H: (csubst0 O v c1 c2)).(\lambda (e: C).(\lambda (H0: (drop O O c1 
e)).(eq_ind C c1 (\lambda (c: C).(or4 (drop O O c2 c) (ex3_4 F C T T (\lambda 
(f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e0 
(Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop O O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop O O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C c (CHead e1 (Flat f) u))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop O O 
c2 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))))) (insert_eq nat O (\lambda (n0: nat).(csubst0 n0 v c1 c2)) 
(\lambda (n0: nat).(or4 (drop n0 n0 c2 c1) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c1 (CHead e0 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop n0 n0 c2 (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 n0 v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c1 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop n0 n0 c2 (CHead e2 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 n0 v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c1 (CHead e1 (Flat f) u))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop n0 n0 c2 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 n0 v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 n0 v e1 e2))))))))) (\lambda (y: nat).(\lambda (H1: (csubst0 
y v c1 c2)).(csubst0_ind (\lambda (n0: nat).(\lambda (t: T).(\lambda (c: 
C).(\lambda (c0: C).((eq nat n0 O) \to (or4 (drop n0 n0 c0 c) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c 
(CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop n0 n0 c0 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 n0 t u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop n0 n0 c0 (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 n0 
t e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 (Flat f) u))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop n0 n0 c0 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 n0 t u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 n0 t e1 e2))))))))))))) (\lambda (k: K).(K_ind (\lambda (k0: 
K).(\forall (i: nat).(\forall (v0: T).(\forall (u1: T).(\forall (u2: 
T).((subst0 i v0 u1 u2) \to (\forall (c: C).((eq nat (s k0 i) O) \to (or4 
(drop (s k0 i) (s k0 i) (CHead c k0 u2) (CHead c k0 u1)) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead 
c k0 u1) (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (s k0 i) (s k0 i) (CHead c k0 u2) (CHead e0 
(Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (s k0 i) v0 u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead c k0 u1) (CHead e1 (Flat f) 
u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (s k0 i) (s k0 i) (CHead c k0 u2) (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (s 
k0 i) v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c k0 u1) 
(CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s k0 i) (s k0 i) (CHead c k0 u2) 
(CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (s k0 i) v0 u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(s k0 i) v0 e1 e2)))))))))))))))) (\lambda (b: B).(\lambda (i: nat).(\lambda 
(v0: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (subst0 i v0 u1 
u2)).(\lambda (c: C).(\lambda (H3: (eq nat (S i) O)).(let H4 \def (eq_ind nat 
(S i) (\lambda (ee: nat).(match ee in nat return (\lambda (_: nat).Prop) with 
[O \Rightarrow False | (S _) \Rightarrow True])) I O H3) in (False_ind (or4 
(drop (S i) (S i) (CHead c (Bind b) u2) (CHead c (Bind b) u1)) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead 
c (Bind b) u1) (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S i) (S i) (CHead c (Bind b) u2) 
(CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (S i) v0 u w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead c (Bind b) 
u1) (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S i) (S i) (CHead c (Bind b) u2) (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (S i) v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c (Bind 
b) u1) (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S i) (S i) (CHead c (Bind b) 
u2) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (S i) v0 u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(S i) v0 e1 e2)))))))) H4)))))))))) (\lambda (f: F).(\lambda (i: 
nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H2: (subst0 
i v0 u1 u2)).(\lambda (c: C).(\lambda (H3: (eq nat i O)).(let H4 \def (eq_ind 
nat i (\lambda (n0: nat).(subst0 n0 v0 u1 u2)) H2 O H3) in (eq_ind_r nat O 
(\lambda (n0: nat).(or4 (drop n0 n0 (CHead c (Flat f) u2) (CHead c (Flat f) 
u1)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead c (Flat f) u1) (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 n0 
(CHead c (Flat f) u2) (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 n0 v0 u w)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C 
(CHead c (Flat f) u1) (CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u: T).(drop n0 n0 (CHead c (Flat f) u2) 
(CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 n0 v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead c (Flat f) u1) (CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop n0 n0 (CHead c 
(Flat f) u2) (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 n0 v0 u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 n0 v0 e1 e2))))))))) (or4_intro1 (drop O O (CHead c (Flat f) 
u2) (CHead c (Flat f) u1)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c (Flat f) u1) (CHead e0 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop O O (CHead c (Flat f) u2) (CHead e0 (Flat f0) w)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v0 u w)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C (CHead c (Flat f) u1) (CHead e1 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop O O (CHead c (Flat 
f) u2) (CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq 
C (CHead c (Flat f) u1) (CHead e1 (Flat f0) u))))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop O O 
(CHead c (Flat f) u2) (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v0 u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v0 e1 e2))))))) (ex3_4_intro F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c (Flat f) 
u1) (CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop O O (CHead c (Flat f) u2) (CHead e0 (Flat f0) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v0 u w))))) f c u1 u2 (refl_equal C (CHead c (Flat f) u1)) 
(drop_refl (CHead c (Flat f) u2)) H4)) i H3)))))))))) k)) (\lambda (k: 
K).(K_ind (\lambda (k0: K).(\forall (i: nat).(\forall (c3: C).(\forall (c4: 
C).(\forall (v0: T).((csubst0 i v0 c3 c4) \to ((((eq nat i O) \to (or4 (drop 
i i c4 c3) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C c3 (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop i i c4 (CHead e0 
(Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 i v0 u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c3 (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop i i c4 
(CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 
(CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop i i c4 (CHead e2 (Flat f) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 i v0 u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v0 e1 e2)))))))))) \to (\forall 
(u: T).((eq nat (s k0 i) O) \to (or4 (drop (s k0 i) (s k0 i) (CHead c4 k0 u) 
(CHead c3 k0 u)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C (CHead c3 k0 u) (CHead e0 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s k0 
i) (s k0 i) (CHead c4 k0 u) (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 (s k0 i) v0 u0 
w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(eq C (CHead c3 k0 u) (CHead e1 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (s k0 
i) (s k0 i) (CHead c4 k0 u) (CHead e2 (Flat f) u0)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (s k0 i) v0 e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead c3 k0 u) (CHead e1 (Flat f) 
u0))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s k0 i) (s k0 i) (CHead c4 k0 u) (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 (s k0 i) v0 u0 w)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (s k0 i) v0 
e1 e2))))))))))))))))) (\lambda (b: B).(\lambda (i: nat).(\lambda (c3: 
C).(\lambda (c4: C).(\lambda (v0: T).(\lambda (_: (csubst0 i v0 c3 
c4)).(\lambda (_: (((eq nat i O) \to (or4 (drop i i c4 c3) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 
(CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop i i c4 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 i v0 u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c3 (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop i i c4 (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e1 (Flat f) u))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop i i c4 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 i v0 u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 i v0 e1 e2))))))))))).(\lambda (u: T).(\lambda (H4: (eq nat 
(S i) O)).(let H5 \def (eq_ind nat (S i) (\lambda (ee: nat).(match ee in nat 
return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow 
True])) I O H4) in (False_ind (or4 (drop (S i) (S i) (CHead c4 (Bind b) u) 
(CHead c3 (Bind b) u)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead c3 (Bind b) u) (CHead e0 
(Flat f) u0)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S i) (S i) (CHead c4 (Bind b) u) (CHead e0 (Flat f) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 (S 
i) v0 u0 w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(eq C (CHead c3 (Bind b) u) (CHead e1 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (S i) 
(S i) (CHead c4 (Bind b) u) (CHead e2 (Flat f) u0)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (S i) v0 e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead c3 (Bind b) u) (CHead e1 
(Flat f) u0))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S i) (S i) (CHead c4 (Bind b) u) (CHead e2 
(Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (w: T).(subst0 (S i) v0 u0 w)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (S i) v0 e1 
e2)))))))) H5))))))))))) (\lambda (f: F).(\lambda (i: nat).(\lambda (c3: 
C).(\lambda (c4: C).(\lambda (v0: T).(\lambda (H2: (csubst0 i v0 c3 
c4)).(\lambda (H3: (((eq nat i O) \to (or4 (drop i i c4 c3) (ex3_4 F C T T 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 
(CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop i i c4 (CHead e0 (Flat f0) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 i v0 u w)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c3 (CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop i i c4 (CHead e2 (Flat f0) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e1 (Flat f0) u))))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(drop i i c4 (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 i v0 u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 i v0 e1 e2))))))))))).(\lambda (u: T).(\lambda (H4: (eq nat i 
O)).(let H5 \def (eq_ind nat i (\lambda (n0: nat).((eq nat n0 O) \to (or4 
(drop n0 n0 c4 c3) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C c3 (CHead e0 (Flat f0) u0)))))) (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 n0 c4 (CHead e0 
(Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda 
(w: T).(subst0 n0 v0 u0 w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(eq C c3 (CHead e1 (Flat f0) u0)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop n0 
n0 c4 (CHead e2 (Flat f0) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 n0 v0 e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C c3 (CHead e1 (Flat f0) u0))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop n0 n0 c4 (CHead e2 (Flat f0) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 n0 v0 u0 w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 n0 v0 e1 
e2)))))))))) H3 O H4) in (let H6 \def (eq_ind nat i (\lambda (n0: 
nat).(csubst0 n0 v0 c3 c4)) H2 O H4) in (eq_ind_r nat O (\lambda (n0: 
nat).(or4 (drop n0 n0 (CHead c4 (Flat f) u) (CHead c3 (Flat f) u)) (ex3_4 F C 
T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C 
(CHead c3 (Flat f) u) (CHead e0 (Flat f0) u0)))))) (\lambda (f0: F).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 n0 (CHead c4 (Flat f) u) 
(CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 n0 v0 u0 w)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C (CHead c3 (Flat f) 
u) (CHead e1 (Flat f0) u0)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u0: T).(drop n0 n0 (CHead c4 (Flat f) u) (CHead e2 (Flat 
f0) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 n0 v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead c3 (Flat f) 
u) (CHead e1 (Flat f0) u0))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop n0 n0 (CHead c4 (Flat f) u) 
(CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 n0 v0 u0 w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
n0 v0 e1 e2))))))))) (or4_intro2 (drop O O (CHead c4 (Flat f) u) (CHead c3 
(Flat f) u)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C (CHead c3 (Flat f) u) (CHead e0 (Flat f0) u0)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop O O 
(CHead c4 (Flat f) u) (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v0 u0 w)))))) (ex3_4 F C C 
T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C 
(CHead c3 (Flat f) u) (CHead e1 (Flat f0) u0)))))) (\lambda (f0: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u0: T).(drop O O (CHead c4 (Flat f) u) 
(CHead e2 (Flat f0) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C 
(CHead c3 (Flat f) u) (CHead e1 (Flat f0) u0))))))) (\lambda (f0: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop O O (CHead c4 
(Flat f) u) (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v0 u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v0 e1 e2))))))) (ex3_4_intro F C C T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C (CHead c3 (Flat f) 
u) (CHead e1 (Flat f0) u0)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u0: T).(drop O O (CHead c4 (Flat f) u) (CHead e2 (Flat f0) 
u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v0 e1 e2))))) f c3 c4 u (refl_equal C (CHead c3 (Flat f) u)) 
(drop_refl (CHead c4 (Flat f) u)) H6)) i H4)))))))))))) k)) (\lambda (k: 
K).(K_ind (\lambda (k0: K).(\forall (i: nat).(\forall (v0: T).(\forall (u1: 
T).(\forall (u2: T).((subst0 i v0 u1 u2) \to (\forall (c3: C).(\forall (c4: 
C).((csubst0 i v0 c3 c4) \to ((((eq nat i O) \to (or4 (drop i i c4 c3) (ex3_4 
F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq 
C c3 (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop i i c4 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 i v0 u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c3 (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop i i c4 (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e1 (Flat f) u))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop i i c4 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 i v0 u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 i v0 e1 e2)))))))))) \to ((eq nat (s k0 i) O) \to (or4 (drop 
(s k0 i) (s k0 i) (CHead c4 k0 u2) (CHead c3 k0 u1)) (ex3_4 F C T T (\lambda 
(f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c3 k0 
u1) (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s k0 i) (s k0 i) (CHead c4 k0 u2) (CHead e0 (Flat 
f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (s k0 i) v0 u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead c3 k0 u1) (CHead e1 (Flat f) 
u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (s k0 i) (s k0 i) (CHead c4 k0 u2) (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (s 
k0 i) v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c3 k0 u1) 
(CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s k0 i) (s k0 i) (CHead c4 k0 u2) 
(CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (s k0 i) v0 u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(s k0 i) v0 e1 e2))))))))))))))))))) (\lambda (b: B).(\lambda (i: 
nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (subst0 
i v0 u1 u2)).(\lambda (c3: C).(\lambda (c4: C).(\lambda (_: (csubst0 i v0 c3 
c4)).(\lambda (_: (((eq nat i O) \to (or4 (drop i i c4 c3) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 
(CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop i i c4 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 i v0 u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c3 (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop i i c4 (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e1 (Flat f) u))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop i i c4 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 i v0 u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 i v0 e1 e2))))))))))).(\lambda (H5: (eq nat (S i) O)).(let H6 
\def (eq_ind nat (S i) (\lambda (ee: nat).(match ee in nat return (\lambda 
(_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) I O H5) 
in (False_ind (or4 (drop (S i) (S i) (CHead c4 (Bind b) u2) (CHead c3 (Bind 
b) u1)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead c3 (Bind b) u1) (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S i) 
(S i) (CHead c4 (Bind b) u2) (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (S i) v0 u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C (CHead c3 (Bind b) u1) (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S i) (S i) (CHead 
c4 (Bind b) u2) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (S i) v0 e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead c3 (Bind b) u1) (CHead e1 (Flat f) u))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S i) (S i) (CHead c4 (Bind b) u2) (CHead e2 (Flat f) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (S i) v0 u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (S i) v0 e1 e2)))))))) 
H6))))))))))))) (\lambda (f: F).(\lambda (i: nat).(\lambda (v0: T).(\lambda 
(u1: T).(\lambda (u2: T).(\lambda (H2: (subst0 i v0 u1 u2)).(\lambda (c3: 
C).(\lambda (c4: C).(\lambda (H3: (csubst0 i v0 c3 c4)).(\lambda (H4: (((eq 
nat i O) \to (or4 (drop i i c4 c3) (ex3_4 F C T T (\lambda (f0: F).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop i i 
c4 (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 i v0 u w)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c3 (CHead e1 (Flat 
f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop i i c4 (CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i v0 e1 e2)))))) (ex4_5 F C C T 
T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C c3 (CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop i i c4 (CHead e2 
(Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 i v0 u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v0 e1 
e2))))))))))).(\lambda (H5: (eq nat i O)).(let H6 \def (eq_ind nat i (\lambda 
(n0: nat).((eq nat n0 O) \to (or4 (drop n0 n0 c4 c3) (ex3_4 F C T T (\lambda 
(f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e0 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop n0 n0 c4 (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 n0 v0 u w)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c3 
(CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop n0 n0 c4 (CHead e2 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 n0 v0 e1 
e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e1 (Flat f0) u))))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(drop n0 n0 c4 (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 n0 v0 u 
w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 n0 v0 e1 e2)))))))))) H4 O H5) in (let H7 \def 
(eq_ind nat i (\lambda (n0: nat).(csubst0 n0 v0 c3 c4)) H3 O H5) in (let H8 
\def (eq_ind nat i (\lambda (n0: nat).(subst0 n0 v0 u1 u2)) H2 O H5) in 
(eq_ind_r nat O (\lambda (n0: nat).(or4 (drop n0 n0 (CHead c4 (Flat f) u2) 
(CHead c3 (Flat f) u1)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c3 (Flat f) u1) (CHead e0 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop n0 n0 (CHead c4 (Flat f) u2) (CHead e0 (Flat f0) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 n0 v0 
u w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C (CHead c3 (Flat f) u1) (CHead e1 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop n0 n0 
(CHead c4 (Flat f) u2) (CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 n0 v0 e1 e2)))))) (ex4_5 F 
C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead c3 (Flat f) u1) (CHead e1 (Flat f0) u))))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(drop n0 n0 (CHead c4 (Flat f) u2) (CHead e2 (Flat f0) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 n0 v0 u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 n0 v0 e1 e2))))))))) (or4_intro3 
(drop O O (CHead c4 (Flat f) u2) (CHead c3 (Flat f) u1)) (ex3_4 F C T T 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead c3 (Flat f) u1) (CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop O O (CHead c4 (Flat f) u2) 
(CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v0 u w)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead c3 (Flat f) 
u1) (CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(drop O O (CHead c4 (Flat f) u2) (CHead e2 (Flat f0) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c3 (Flat f) 
u1) (CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop O O (CHead c4 (Flat f) u2) 
(CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v0 u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v0 e1 e2))))))) (ex4_5_intro F C C T T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c3 (Flat f) 
u1) (CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop O O (CHead c4 (Flat f) u2) 
(CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v0 u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v0 e1 e2)))))) f c3 c4 u1 u2 (refl_equal C (CHead c3 (Flat f) u1)) 
(drop_refl (CHead c4 (Flat f) u2)) H8 H7)) i H5))))))))))))))) k)) y v c1 c2 
H1))) H) e (drop_gen_refl c1 e H0)))))))) (\lambda (n0: nat).(\lambda (IHn: 
((\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 n0 v c1 c2) \to 
(\forall (e: C).((drop n0 O c1 e) \to (or4 (drop n0 O c2 e) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop n0 O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop n0 O c2 (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop n0 O c2 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))))))))))))).(\lambda (c1: C).(C_ind (\lambda 
(c: C).(\forall (c2: C).(\forall (v: T).((csubst0 (S n0) v c c2) \to (\forall 
(e: C).((drop (S n0) O c e) \to (or4 (drop (S n0) O c2 e) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))))))))))) (\lambda (n1: 
nat).(\lambda (c2: C).(\lambda (v: T).(\lambda (_: (csubst0 (S n0) v (CSort 
n1) c2)).(\lambda (e: C).(\lambda (H0: (drop (S n0) O (CSort n1) 
e)).(and3_ind (eq C e (CSort n1)) (eq nat (S n0) O) (eq nat O O) (or4 (drop 
(S n0) O c2 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead 
e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) 
O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (H1: (eq C e (CSort n1))).(\lambda (H2: (eq nat (S n0) 
O)).(\lambda (_: (eq nat O O)).(eq_ind_r C (CSort n1) (\lambda (c: C).(or4 
(drop (S n0) O c2 c) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C c (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead 
e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) 
O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
c (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (let H4 \def (eq_ind nat (S n0) (\lambda (ee: nat).(match ee in 
nat return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) 
\Rightarrow True])) I O H2) in (False_ind (or4 (drop (S n0) O c2 (CSort n1)) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C (CSort n1) (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 (Flat f) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CSort n1) (CHead e1 (Flat f) 
u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C (CSort n1) (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead 
e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) H4)) e H1)))) (drop_gen_sort n1 (S n0) O e H0)))))))) (\lambda (c: 
C).(\lambda (H: ((\forall (c2: C).(\forall (v: T).((csubst0 (S n0) v c c2) 
\to (\forall (e: C).((drop (S n0) O c e) \to (or4 (drop (S n0) O c2 e) (ex3_4 
F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2))))))))))))))).(\lambda (k: K).(\lambda 
(t: T).(\lambda (c2: C).(\lambda (v: T).(\lambda (H0: (csubst0 (S n0) v 
(CHead c k t) c2)).(\lambda (e: C).(\lambda (H1: (drop (S n0) O (CHead c k t) 
e)).(or3_ind (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (S n0) (s 
k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) 
(\lambda (u2: T).(\lambda (j: nat).(subst0 j v t u2)))) (ex3_2 C nat (\lambda 
(_: C).(\lambda (j: nat).(eq nat (S n0) (s k j)))) (\lambda (c3: C).(\lambda 
(_: nat).(eq C c2 (CHead c3 k t)))) (\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c c3)))) (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat (S n0) (s k j))))) (\lambda (u2: T).(\lambda 
(c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: 
T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3))))) (or4 (drop (S 
n0) O c2 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead 
e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) 
O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (H2: (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq 
nat (S n0) (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead c k 
u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v t u2))))).(ex3_2_ind T 
nat (\lambda (_: T).(\lambda (j: nat).(eq nat (S n0) (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v t u2))) (or4 (drop (S n0) O c2 e) (ex3_4 F C T T (\lambda 
(f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 
(Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O c2 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2)))))))) (\lambda (x0: T).(\lambda (x1: nat).(\lambda (H3: (eq nat 
(S n0) (s k x1))).(\lambda (H4: (eq C c2 (CHead c k x0))).(\lambda (H5: 
(subst0 x1 v t x0)).(eq_ind_r C (CHead c k x0) (\lambda (c0: C).(or4 (drop (S 
n0) O c0 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead 
e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) 
O c0 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (K_ind (\lambda (k0: K).((drop (r k0 n0) O c e) \to ((eq nat (S 
n0) (s k0 x1)) \to (or4 (drop (S n0) O (CHead c k0 x0) e) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c k0 x0) (CHead e0 (Flat f) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u 
w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c 
k0 x0) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c k0 x0) (CHead e2 
(Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))))) (\lambda (b: B).(\lambda (H6: (drop (r (Bind b) n0) O c 
e)).(\lambda (H7: (eq nat (S n0) (s (Bind b) x1))).(let H8 \def (f_equal nat 
nat (\lambda (e0: nat).(match e0 in nat return (\lambda (_: nat).nat) with [O 
\Rightarrow n0 | (S n1) \Rightarrow n1])) (S n0) (S x1) H7) in (let H9 \def 
(eq_ind_r nat x1 (\lambda (n1: nat).(subst0 n1 v t x0)) H5 n0 H8) in 
(or4_intro0 (drop (S n0) O (CHead c (Bind b) x0) e) (ex3_4 F C T T (\lambda 
(f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 
(Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O (CHead c (Bind b) x0) (CHead e0 (Flat f) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u 
w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c 
(Bind b) x0) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c 
(Bind b) x0) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (drop_drop (Bind b) n0 c e H6 x0))))))) 
(\lambda (f: F).(\lambda (H6: (drop (r (Flat f) n0) O c e)).(\lambda (H7: (eq 
nat (S n0) (s (Flat f) x1))).(let H8 \def (f_equal nat nat (\lambda (e0: 
nat).e0) (S n0) (s (Flat f) x1) H7) in (let H9 \def (eq_ind_r nat x1 (\lambda 
(n1: nat).(subst0 n1 v t x0)) H5 (S n0) H8) in (or4_intro0 (drop (S n0) O 
(CHead c (Flat f) x0) e) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c (Flat f) x0) (CHead e0 (Flat f0) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c (Flat f) x0) 
(CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c (Flat f) x0) 
(CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))) (drop_drop (Flat f) n0 c e H6 x0))))))) k (drop_gen_drop k c 
e t n0 H1) H3) c2 H4)))))) H2)) (\lambda (H2: (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat (S n0) (s k j)))) (\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j 
v c c3))))).(ex3_2_ind C nat (\lambda (_: C).(\lambda (j: nat).(eq nat (S n0) 
(s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) 
(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3))) (or4 (drop (S n0) O 
c2 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead 
e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) 
O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (x0: C).(\lambda (x1: nat).(\lambda (H3: (eq nat (S n0) 
(s k x1))).(\lambda (H4: (eq C c2 (CHead x0 k t))).(\lambda (H5: (csubst0 x1 
v c x0)).(eq_ind_r C (CHead x0 k t) (\lambda (c0: C).(or4 (drop (S n0) O c0 
e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead e0 (Flat f) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) 
O c0 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (K_ind (\lambda (k0: K).((drop (r k0 n0) O c e) \to ((eq nat (S 
n0) (s k0 x1)) \to (or4 (drop (S n0) O (CHead x0 k0 t) e) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 k0 t) (CHead e0 (Flat f) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u 
w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 
k0 t) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 k0 t) (CHead e2 
(Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))))) (\lambda (b: B).(\lambda (H6: (drop (r (Bind b) n0) O c 
e)).(\lambda (H7: (eq nat (S n0) (s (Bind b) x1))).(let H8 \def (f_equal nat 
nat (\lambda (e0: nat).(match e0 in nat return (\lambda (_: nat).nat) with [O 
\Rightarrow n0 | (S n1) \Rightarrow n1])) (S n0) (S x1) H7) in (let H9 \def 
(eq_ind_r nat x1 (\lambda (n1: nat).(csubst0 n1 v c x0)) H5 n0 H8) in (let 
H10 \def (IHn c x0 v H9 e H6) in (or4_ind (drop n0 O x0 e) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop n0 O x0 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop n0 O x0 (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop n0 O x0 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (or4 (drop (S n0) O (CHead x0 (Bind b) t) e) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) 
(CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat f) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat f) w))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda (H11: 
(drop n0 O x0 e)).(or4_intro0 (drop (S n0) O (CHead x0 (Bind b) t) e) (ex3_4 
F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e0 (Flat f) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) 
O (CHead x0 (Bind b) t) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (drop_drop (Bind b) n0 x0 e H11 
t))) (\lambda (H11: (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O x0 (CHead e0 
(Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w))))))).(ex3_4_ind F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O 
x0 (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w))))) (or4 (drop (S n0) O (CHead x0 (Bind 
b) t) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 
(Bind b) t) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (x2: F).(\lambda (x3: C).(\lambda (x4: T).(\lambda (x5: 
T).(\lambda (H12: (eq C e (CHead x3 (Flat x2) x4))).(\lambda (H13: (drop n0 O 
x0 (CHead x3 (Flat x2) x5))).(\lambda (H14: (subst0 O v x4 x5)).(eq_ind_r C 
(CHead x3 (Flat x2) x4) (\lambda (c0: C).(or4 (drop (S n0) O (CHead x0 (Bind 
b) t) c0) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C c0 (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 
(Bind b) t) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e1 (Flat 
f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (or4_intro1 (drop (S n0) O (CHead x0 (Bind b) t) (CHead x3 (Flat 
x2) x4)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead x3 (Flat x2) x4) (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) 
O (CHead x0 (Bind b) t) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead 
x3 (Flat x2) x4) (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Bind b) t) 
(CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead x3 (Flat x2) x4) (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead 
x0 (Bind b) t) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (ex3_4_intro F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x3 (Flat x2) 
x4) (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e0 (Flat f) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w))))) x2 x3 x4 x5 (refl_equal C (CHead x3 (Flat x2) x4)) 
(drop_drop (Bind b) n0 x0 (CHead x3 (Flat x2) x5) H13 t) H14)) e H12)))))))) 
H11)) (\lambda (H11: (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop n0 O x0 (CHead e2 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2))))))).(ex3_4_ind F C C T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop n0 O 
x0 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2))))) (or4 (drop (S n0) O (CHead x0 
(Bind b) t) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 
(Bind b) t) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (x2: F).(\lambda (x3: C).(\lambda (x4: C).(\lambda (x5: 
T).(\lambda (H12: (eq C e (CHead x3 (Flat x2) x5))).(\lambda (H13: (drop n0 O 
x0 (CHead x4 (Flat x2) x5))).(\lambda (H14: (csubst0 O v x3 x4)).(eq_ind_r C 
(CHead x3 (Flat x2) x5) (\lambda (c0: C).(or4 (drop (S n0) O (CHead x0 (Bind 
b) t) c0) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C c0 (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 
(Bind b) t) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e1 (Flat 
f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (or4_intro2 (drop (S n0) O (CHead x0 (Bind b) t) (CHead x3 (Flat 
x2) x5)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead x3 (Flat x2) x5) (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) 
O (CHead x0 (Bind b) t) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead 
x3 (Flat x2) x5) (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Bind b) t) 
(CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead x3 (Flat x2) x5) (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead 
x0 (Bind b) t) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (ex3_4_intro F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x3 (Flat x2) 
x5) (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2))))) x2 x3 x4 x5 (refl_equal C (CHead x3 (Flat x2) x5)) 
(drop_drop (Bind b) n0 x0 (CHead x4 (Flat x2) x5) H13 t) H14)) e H12)))))))) 
H11)) (\lambda (H11: (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop n0 O x0 (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))))).(ex4_5_ind F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop n0 O x0 (CHead e2 (Flat f) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))) (or4 (drop (S n0) 
O (CHead x0 (Bind b) t) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) 
O (CHead x0 (Bind b) t) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (x2: F).(\lambda (x3: C).(\lambda (x4: C).(\lambda (x5: 
T).(\lambda (x6: T).(\lambda (H12: (eq C e (CHead x3 (Flat x2) x5))).(\lambda 
(H13: (drop n0 O x0 (CHead x4 (Flat x2) x6))).(\lambda (H14: (subst0 O v x5 
x6)).(\lambda (H15: (csubst0 O v x3 x4)).(eq_ind_r C (CHead x3 (Flat x2) x5) 
(\lambda (c0: C).(or4 (drop (S n0) O (CHead x0 (Bind b) t) c0) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 
(CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e0 (Flat f) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) 
O (CHead x0 (Bind b) t) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C c0 (CHead e1 (Flat f) u))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2))))))))) (or4_intro3 (drop (S n0) O 
(CHead x0 (Bind b) t) (CHead x3 (Flat x2) x5)) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x3 (Flat x2) 
x5) (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e0 (Flat f) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x3 (Flat x2) x5) (CHead e1 
(Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x3 (Flat x2) x5) (CHead e1 
(Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat 
f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) 
(ex4_5_intro F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x3 (Flat x2) x5) (CHead e1 
(Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Bind b) t) (CHead e2 (Flat 
f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
x2 x3 x4 x5 x6 (refl_equal C (CHead x3 (Flat x2) x5)) (drop_drop (Bind b) n0 
x0 (CHead x4 (Flat x2) x6) H13 t) H14 H15)) e H12)))))))))) H11)) H10))))))) 
(\lambda (f: F).(\lambda (H6: (drop (r (Flat f) n0) O c e)).(\lambda (H7: (eq 
nat (S n0) (s (Flat f) x1))).(let H8 \def (f_equal nat nat (\lambda (e0: 
nat).e0) (S n0) (s (Flat f) x1) H7) in (let H9 \def (eq_ind_r nat x1 (\lambda 
(n1: nat).(csubst0 n1 v c x0)) H5 (S n0) H8) in (let H10 \def (H x0 v H9 e 
H6) in (or4_ind (drop (S n0) O x0 e) (ex3_4 F C T T (\lambda (f0: F).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O x0 (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat 
f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O x0 (CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u))))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O x0 (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (or4 (drop (S n0) O (CHead x0 (Flat f) t) e) 
(ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat 
f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 (Flat f0) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u))))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 (Flat f0) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda (H11: 
(drop (S n0) O x0 e)).(or4_intro0 (drop (S n0) O (CHead x0 (Flat f) t) e) 
(ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat 
f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 (Flat f0) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u))))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 (Flat f0) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (drop_drop (Flat 
f) n0 x0 e H11 t))) (\lambda (H11: (ex3_4 F C T T (\lambda (f0: F).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O x0 (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v u w))))))).(ex3_4_ind F C T T (\lambda 
(f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O x0 (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w))))) (or4 (drop (S n0) 
O (CHead x0 (Flat f) t) e) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x0 (Flat f) t) (CHead e0 (Flat f0) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2)))))))) (\lambda (x2: F).(\lambda (x3: C).(\lambda (x4: T).(\lambda 
(x5: T).(\lambda (H12: (eq C e (CHead x3 (Flat x2) x4))).(\lambda (H13: (drop 
(S n0) O x0 (CHead x3 (Flat x2) x5))).(\lambda (H14: (subst0 O v x4 
x5)).(eq_ind_r C (CHead x3 (Flat x2) x4) (\lambda (c0: C).(or4 (drop (S n0) O 
(CHead x0 (Flat f) t) c0) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x0 (Flat f) t) (CHead e0 (Flat f0) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))))) (or4_intro1 (drop (S n0) O (CHead x0 (Flat f) t) (CHead x3 
(Flat x2) x4)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead x3 (Flat x2) x4) (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x0 (Flat f) t) (CHead e0 (Flat f0) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C (CHead x3 (Flat x2) x4) (CHead e1 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 
(Flat f) t) (CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C (CHead x3 (Flat x2) x4) (CHead e1 (Flat f0) u))))))) (\lambda 
(f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 (Flat f0) w))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (ex3_4_intro F C 
T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead x3 (Flat x2) x4) (CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w))))) x2 x3 x4 x5 (refl_equal C (CHead x3 
(Flat x2) x4)) (drop_drop (Flat f) n0 x0 (CHead x3 (Flat x2) x5) H13 t) H14)) 
e H12)))))))) H11)) (\lambda (H11: (ex3_4 F C C T (\lambda (f0: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S 
n0) O x0 (CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))))).(ex3_4_ind F C 
C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O x0 (CHead e2 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))) 
(or4 (drop (S n0) O (CHead x0 (Flat f) t) e) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat 
f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e0 (Flat f0) w)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2)))))))) (\lambda (x2: F).(\lambda (x3: C).(\lambda (x4: C).(\lambda 
(x5: T).(\lambda (H12: (eq C e (CHead x3 (Flat x2) x5))).(\lambda (H13: (drop 
(S n0) O x0 (CHead x4 (Flat x2) x5))).(\lambda (H14: (csubst0 O v x3 
x4)).(eq_ind_r C (CHead x3 (Flat x2) x5) (\lambda (c0: C).(or4 (drop (S n0) O 
(CHead x0 (Flat f) t) c0) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x0 (Flat f) t) (CHead e0 (Flat f0) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))))) (or4_intro2 (drop (S n0) O (CHead x0 (Flat f) t) (CHead x3 
(Flat x2) x5)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead x3 (Flat x2) x5) (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x0 (Flat f) t) (CHead e0 (Flat f0) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C (CHead x3 (Flat x2) x5) (CHead e1 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 
(Flat f) t) (CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C (CHead x3 (Flat x2) x5) (CHead e1 (Flat f0) u))))))) (\lambda 
(f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 (Flat f0) w))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (ex3_4_intro F C 
C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C 
(CHead x3 (Flat x2) x5) (CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Flat f) t) 
(CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2))))) x2 x3 x4 x5 (refl_equal C (CHead 
x3 (Flat x2) x5)) (drop_drop (Flat f) n0 x0 (CHead x4 (Flat x2) x5) H13 t) 
H14)) e H12)))))))) H11)) (\lambda (H11: (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O x0 (CHead e2 (Flat f0) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))).(ex4_5_ind F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u))))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O x0 (CHead e2 (Flat f0) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))) (or4 (drop (S n0) O (CHead x0 
(Flat f) t) e) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 
(Flat f) t) (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 (Flat f0) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat 
f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 (Flat f0) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (x2: F).(\lambda (x3: C).(\lambda (x4: C).(\lambda (x5: 
T).(\lambda (x6: T).(\lambda (H12: (eq C e (CHead x3 (Flat x2) x5))).(\lambda 
(H13: (drop (S n0) O x0 (CHead x4 (Flat x2) x6))).(\lambda (H14: (subst0 O v 
x5 x6)).(\lambda (H15: (csubst0 O v x3 x4)).(eq_ind_r C (CHead x3 (Flat x2) 
x5) (\lambda (c0: C).(or4 (drop (S n0) O (CHead x0 (Flat f) t) c0) (ex3_4 F C 
T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
c0 (CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e0 (Flat f0) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S 
n0) O (CHead x0 (Flat f) t) (CHead e2 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C c0 (CHead e1 (Flat f0) u))))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x0 (Flat f) t) (CHead e2 (Flat f0) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2))))))))) (or4_intro3 (drop (S n0) O 
(CHead x0 (Flat f) t) (CHead x3 (Flat x2) x5)) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x3 (Flat x2) 
x5) (CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e0 (Flat 
f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x3 (Flat x2) x5) (CHead e1 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 (Flat f0) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x3 (Flat x2) x5) (CHead e1 
(Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 (Flat 
f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) 
(ex4_5_intro F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x3 (Flat x2) x5) (CHead e1 
(Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O (CHead x0 (Flat f) t) (CHead e2 (Flat 
f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
x2 x3 x4 x5 x6 (refl_equal C (CHead x3 (Flat x2) x5)) (drop_drop (Flat f) n0 
x0 (CHead x4 (Flat x2) x6) H13 t) H14 H15)) e H12)))))))))) H11)) H10))))))) 
k (drop_gen_drop k c e t n0 H1) H3) c2 H4)))))) H2)) (\lambda (H2: (ex4_3 T C 
nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (S n0) (s k 
j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 
k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t 
u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c 
c3)))))).(ex4_3_ind T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat (S n0) (s k j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda 
(_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda (_: 
C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c c3)))) (or4 (drop (S n0) O c2 e) (ex3_4 F 
C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda (x0: T).(\lambda (x1: 
C).(\lambda (x2: nat).(\lambda (H3: (eq nat (S n0) (s k x2))).(\lambda (H4: 
(eq C c2 (CHead x1 k x0))).(\lambda (H5: (subst0 x2 v t x0)).(\lambda (H6: 
(csubst0 x2 v c x1)).(eq_ind_r C (CHead x1 k x0) (\lambda (c0: C).(or4 (drop 
(S n0) O c0 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead 
e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) 
O c0 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (K_ind (\lambda (k0: K).((drop (r k0 n0) O c e) \to ((eq nat (S 
n0) (s k0 x2)) \to (or4 (drop (S n0) O (CHead x1 k0 x0) e) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 k0 x0) (CHead e0 (Flat f) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u 
w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 
k0 x0) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 k0 x0) (CHead e2 
(Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))))) (\lambda (b: B).(\lambda (H7: (drop (r (Bind b) n0) O c 
e)).(\lambda (H8: (eq nat (S n0) (s (Bind b) x2))).(let H9 \def (f_equal nat 
nat (\lambda (e0: nat).(match e0 in nat return (\lambda (_: nat).nat) with [O 
\Rightarrow n0 | (S n1) \Rightarrow n1])) (S n0) (S x2) H8) in (let H10 \def 
(eq_ind_r nat x2 (\lambda (n1: nat).(csubst0 n1 v c x1)) H6 n0 H9) in (let 
H11 \def (eq_ind_r nat x2 (\lambda (n1: nat).(subst0 n1 v t x0)) H5 n0 H9) in 
(let H12 \def (IHn c x1 v H10 e H7) in (or4_ind (drop n0 O x1 e) (ex3_4 F C T 
T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop n0 O x1 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop n0 O x1 (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop n0 O x1 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (or4 (drop (S n0) O (CHead x1 (Bind b) x0) 
e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) 
(CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) w))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda (H13: 
(drop n0 O x1 e)).(or4_intro0 (drop (S n0) O (CHead x1 (Bind b) x0) e) (ex3_4 
F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e0 (Flat f) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) 
O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (drop_drop (Bind b) n0 x1 e H13 
x0))) (\lambda (H13: (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O x1 (CHead e0 
(Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w))))))).(ex3_4_ind F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O 
x1 (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w))))) (or4 (drop (S n0) O (CHead x1 (Bind 
b) x0) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 
(Bind b) x0) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (x3: F).(\lambda (x4: C).(\lambda (x5: T).(\lambda (x6: 
T).(\lambda (H14: (eq C e (CHead x4 (Flat x3) x5))).(\lambda (H15: (drop n0 O 
x1 (CHead x4 (Flat x3) x6))).(\lambda (H16: (subst0 O v x5 x6)).(eq_ind_r C 
(CHead x4 (Flat x3) x5) (\lambda (c0: C).(or4 (drop (S n0) O (CHead x1 (Bind 
b) x0) c0) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C c0 (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 
(Bind b) x0) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e1 (Flat 
f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (or4_intro1 (drop (S n0) O (CHead x1 (Bind b) x0) (CHead x4 (Flat 
x3) x5)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead x4 (Flat x3) x5) (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) 
O (CHead x1 (Bind b) x0) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead 
x4 (Flat x3) x5) (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Bind b) x0) 
(CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead x4 (Flat x3) x5) (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead 
x1 (Bind b) x0) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (ex3_4_intro F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x4 (Flat x3) 
x5) (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e0 (Flat f) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w))))) x3 x4 x5 x6 (refl_equal C (CHead x4 (Flat x3) x5)) 
(drop_drop (Bind b) n0 x1 (CHead x4 (Flat x3) x6) H15 x0) H16)) e H14)))))))) 
H13)) (\lambda (H13: (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop n0 O x1 (CHead e2 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2))))))).(ex3_4_ind F C C T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop n0 O 
x1 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2))))) (or4 (drop (S n0) O (CHead x1 
(Bind b) x0) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 
(Bind b) x0) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (x3: F).(\lambda (x4: C).(\lambda (x5: C).(\lambda (x6: 
T).(\lambda (H14: (eq C e (CHead x4 (Flat x3) x6))).(\lambda (H15: (drop n0 O 
x1 (CHead x5 (Flat x3) x6))).(\lambda (H16: (csubst0 O v x4 x5)).(eq_ind_r C 
(CHead x4 (Flat x3) x6) (\lambda (c0: C).(or4 (drop (S n0) O (CHead x1 (Bind 
b) x0) c0) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C c0 (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 
(Bind b) x0) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e1 (Flat 
f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (or4_intro2 (drop (S n0) O (CHead x1 (Bind b) x0) (CHead x4 (Flat 
x3) x6)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead x4 (Flat x3) x6) (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) 
O (CHead x1 (Bind b) x0) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead 
x4 (Flat x3) x6) (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Bind b) x0) 
(CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead x4 (Flat x3) x6) (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead 
x1 (Bind b) x0) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (ex3_4_intro F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x4 (Flat x3) 
x6) (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2))))) x3 x4 x5 x6 (refl_equal C (CHead x4 (Flat x3) x6)) 
(drop_drop (Bind b) n0 x1 (CHead x5 (Flat x3) x6) H15 x0) H16)) e H14)))))))) 
H13)) (\lambda (H13: (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop n0 O x1 (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))))).(ex4_5_ind F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop n0 O x1 (CHead e2 (Flat f) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))) (or4 (drop (S n0) 
O (CHead x1 (Bind b) x0) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) 
O (CHead x1 (Bind b) x0) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (x3: F).(\lambda (x4: C).(\lambda (x5: C).(\lambda (x6: 
T).(\lambda (x7: T).(\lambda (H14: (eq C e (CHead x4 (Flat x3) x6))).(\lambda 
(H15: (drop n0 O x1 (CHead x5 (Flat x3) x7))).(\lambda (H16: (subst0 O v x6 
x7)).(\lambda (H17: (csubst0 O v x4 x5)).(eq_ind_r C (CHead x4 (Flat x3) x6) 
(\lambda (c0: C).(or4 (drop (S n0) O (CHead x1 (Bind b) x0) c0) (ex3_4 F C T 
T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 
(CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e0 (Flat f) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c0 (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) 
O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C c0 (CHead e1 (Flat f) u))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2))))))))) (or4_intro3 (drop (S n0) O 
(CHead x1 (Bind b) x0) (CHead x4 (Flat x3) x6)) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x4 (Flat x3) 
x6) (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e0 (Flat f) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x4 (Flat x3) x6) (CHead e1 
(Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x4 (Flat x3) x6) (CHead e1 
(Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat 
f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) 
(ex4_5_intro F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x4 (Flat x3) x6) (CHead e1 
(Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Bind b) x0) (CHead e2 (Flat 
f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
x3 x4 x5 x6 x7 (refl_equal C (CHead x4 (Flat x3) x6)) (drop_drop (Bind b) n0 
x1 (CHead x5 (Flat x3) x7) H15 x0) H16 H17)) e H14)))))))))) H13)) 
H12)))))))) (\lambda (f: F).(\lambda (H7: (drop (r (Flat f) n0) O c 
e)).(\lambda (H8: (eq nat (S n0) (s (Flat f) x2))).(let H9 \def (f_equal nat 
nat (\lambda (e0: nat).e0) (S n0) (s (Flat f) x2) H8) in (let H10 \def 
(eq_ind_r nat x2 (\lambda (n1: nat).(csubst0 n1 v c x1)) H6 (S n0) H9) in 
(let H11 \def (eq_ind_r nat x2 (\lambda (n1: nat).(subst0 n1 v t x0)) H5 (S 
n0) H9) in (let H12 \def (H x1 v H10 e H7) in (or4_ind (drop (S n0) O x1 e) 
(ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O x1 (CHead e0 (Flat f0) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S 
n0) O x1 (CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O x1 (CHead 
e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))) (or4 (drop (S n0) O (CHead x1 (Flat f) x0) e) (ex3_4 F C T T 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e0 (Flat f0) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S 
n0) O (CHead x1 (Flat f) x0) (CHead e2 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u))))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x1 (Flat f) x0) (CHead e2 (Flat f0) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda (H13: (drop (S n0) O 
x1 e)).(or4_intro0 (drop (S n0) O (CHead x1 (Flat f) x0) e) (ex3_4 F C T T 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e0 (Flat f0) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S 
n0) O (CHead x1 (Flat f) x0) (CHead e2 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u))))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x1 (Flat f) x0) (CHead e2 (Flat f0) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (drop_drop (Flat f) n0 x1 e H13 
x0))) (\lambda (H13: (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O x1 (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v u w))))))).(ex3_4_ind F C T T (\lambda 
(f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O x1 (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w))))) (or4 (drop (S n0) 
O (CHead x1 (Flat f) x0) e) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x1 (Flat f) x0) (CHead e0 (Flat f0) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Flat f) x0) 
(CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) 
(CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2)))))))) (\lambda (x3: F).(\lambda (x4: C).(\lambda (x5: T).(\lambda 
(x6: T).(\lambda (H14: (eq C e (CHead x4 (Flat x3) x5))).(\lambda (H15: (drop 
(S n0) O x1 (CHead x4 (Flat x3) x6))).(\lambda (H16: (subst0 O v x5 
x6)).(eq_ind_r C (CHead x4 (Flat x3) x5) (\lambda (c0: C).(or4 (drop (S n0) O 
(CHead x1 (Flat f) x0) c0) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x1 (Flat f) x0) (CHead e0 (Flat f0) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c0 (CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Flat f) x0) 
(CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 
(CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) 
(CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))))) (or4_intro1 (drop (S n0) O (CHead x1 (Flat f) x0) (CHead 
x4 (Flat x3) x5)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C (CHead x4 (Flat x3) x5) (CHead e0 (Flat f0) 
u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e0 (Flat f0) w)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C (CHead x4 (Flat x3) x5) (CHead e1 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 
(Flat f) x0) (CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C (CHead x4 (Flat x3) x5) (CHead e1 (Flat f0) u))))))) (\lambda 
(f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 (Flat f0) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (ex3_4_intro F C 
T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead x4 (Flat x3) x5) (CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) 
(CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w))))) x3 x4 x5 x6 (refl_equal C (CHead x4 
(Flat x3) x5)) (drop_drop (Flat f) n0 x1 (CHead x4 (Flat x3) x6) H15 x0) 
H16)) e H14)))))))) H13)) (\lambda (H13: (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat 
f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O x1 (CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))))).(ex3_4_ind 
F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq 
C e (CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(drop (S n0) O x1 (CHead e2 (Flat f0) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2))))) (or4 (drop (S n0) O (CHead x1 (Flat f) x0) e) (ex3_4 F C T T 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e0 (Flat f0) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S 
n0) O (CHead x1 (Flat f) x0) (CHead e2 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u))))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x1 (Flat f) x0) (CHead e2 (Flat f0) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda (x3: F).(\lambda (x4: 
C).(\lambda (x5: C).(\lambda (x6: T).(\lambda (H14: (eq C e (CHead x4 (Flat 
x3) x6))).(\lambda (H15: (drop (S n0) O x1 (CHead x5 (Flat x3) x6))).(\lambda 
(H16: (csubst0 O v x4 x5)).(eq_ind_r C (CHead x4 (Flat x3) x6) (\lambda (c0: 
C).(or4 (drop (S n0) O (CHead x1 (Flat f) x0) c0) (ex3_4 F C T T (\lambda 
(f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e0 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e0 (Flat f0) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u 
w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c0 (CHead e1 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 
(Flat f) x0) (CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C c0 (CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 
(Flat f) x0) (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))) (or4_intro2 (drop (S n0) O (CHead x1 (Flat 
f) x0) (CHead x4 (Flat x3) x6)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x4 (Flat x3) x6) (CHead e0 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e0 (Flat f0) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u 
w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C (CHead x4 (Flat x3) x6) (CHead e1 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S 
n0) O (CHead x1 (Flat f) x0) (CHead e2 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C (CHead x4 (Flat x3) x6) (CHead e1 (Flat f0) 
u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 (Flat f0) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) 
(ex3_4_intro F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C (CHead x4 (Flat x3) x6) (CHead e1 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S 
n0) O (CHead x1 (Flat f) x0) (CHead e2 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))) 
x3 x4 x5 x6 (refl_equal C (CHead x4 (Flat x3) x6)) (drop_drop (Flat f) n0 x1 
(CHead x5 (Flat x3) x6) H15 x0) H16)) e H14)))))))) H13)) (\lambda (H13: 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u))))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O x1 (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))))).(ex4_5_ind F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O x1 (CHead e2 (Flat f0) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(or4 (drop (S n0) O (CHead x1 (Flat f) x0) e) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat 
f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e0 (Flat f0) w)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Flat f) x0) 
(CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) 
(CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2)))))))) (\lambda (x3: F).(\lambda (x4: C).(\lambda (x5: C).(\lambda 
(x6: T).(\lambda (x7: T).(\lambda (H14: (eq C e (CHead x4 (Flat x3) 
x6))).(\lambda (H15: (drop (S n0) O x1 (CHead x5 (Flat x3) x7))).(\lambda 
(H16: (subst0 O v x6 x7)).(\lambda (H17: (csubst0 O v x4 x5)).(eq_ind_r C 
(CHead x4 (Flat x3) x6) (\lambda (c0: C).(or4 (drop (S n0) O (CHead x1 (Flat 
f) x0) c0) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C c0 (CHead e0 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead x1 
(Flat f) x0) (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c0 
(CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 (Flat f0) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c0 (CHead e1 (Flat 
f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 (Flat f0) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (or4_intro3 (drop (S n0) O (CHead x1 (Flat f) x0) (CHead x4 (Flat 
x3) x6)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead x4 (Flat x3) x6) (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead x1 (Flat f) x0) (CHead e0 (Flat f0) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C (CHead x4 (Flat x3) x6) (CHead e1 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead x1 
(Flat f) x0) (CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C (CHead x4 (Flat x3) x6) (CHead e1 (Flat f0) u))))))) (\lambda 
(f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 (Flat f0) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (ex4_5_intro F C 
C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead x4 (Flat x3) x6) (CHead e1 (Flat f0) u))))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O (CHead x1 (Flat f) x0) (CHead e2 (Flat f0) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))) x3 x4 x5 x6 x7 
(refl_equal C (CHead x4 (Flat x3) x6)) (drop_drop (Flat f) n0 x1 (CHead x5 
(Flat x3) x7) H15 x0) H16 H17)) e H14)))))))))) H13)) H12)))))))) k 
(drop_gen_drop k c e t n0 H1) H3) c2 H4)))))))) H2)) (csubst0_gen_head k c c2 
t v (S n0) H0))))))))))) c1)))) n).
(* COMMENTS
Initial nodes: 36162
END *)

theorem csubst0_drop_eq_back:
 \forall (n: nat).(\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 
n v c1 c2) \to (\forall (e: C).((drop n O c2 e) \to (or4 (drop n O c1 e) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: 
T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop n O c1 (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v 
u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop n O c1 (CHead e1 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat 
f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop n O c1 (CHead e1 (Flat f) u1))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))))))))))
\def
 \lambda (n: nat).(nat_ind (\lambda (n0: nat).(\forall (c1: C).(\forall (c2: 
C).(\forall (v: T).((csubst0 n0 v c1 c2) \to (\forall (e: C).((drop n0 O c2 
e) \to (or4 (drop n0 O c1 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop n0 O 
c1 (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop n0 O c1 (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop n0 O c1 (CHead e1 
(Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))))))))) (\lambda (c1: C).(\lambda (c2: C).(\lambda (v: T).(\lambda 
(H: (csubst0 O v c1 c2)).(\lambda (e: C).(\lambda (H0: (drop O O c2 
e)).(eq_ind C c2 (\lambda (c: C).(or4 (drop O O c1 c) (ex3_4 F C T T (\lambda 
(f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c (CHead e0 
(Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda 
(_: T).(drop O O c1 (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C c 
(CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop O O c1 (CHead e1 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C c (CHead e2 (Flat f) u2))))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop O 
O c1 (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))))) (insert_eq nat O (\lambda (n0: nat).(csubst0 n0 v c1 c2)) 
(\lambda (n0: nat).(or4 (drop n0 n0 c1 c2) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c2 (CHead e0 (Flat 
f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop n0 n0 c1 (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 n0 v u1 u2)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C c2 
(CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop n0 n0 c1 (CHead e1 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 n0 v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C c2 (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop n0 n0 c1 (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 n0 v u1 
u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 n0 v e1 e2))))))))) (\lambda (y: nat).(\lambda 
(H1: (csubst0 y v c1 c2)).(csubst0_ind (\lambda (n0: nat).(\lambda (t: 
T).(\lambda (c: C).(\lambda (c0: C).((eq nat n0 O) \to (or4 (drop n0 n0 c c0) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: 
T).(eq C c0 (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop n0 n0 c (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 n0 
t u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C c0 (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop n0 n0 c (CHead e1 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 n0 t e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 (CHead e2 
(Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(drop n0 n0 c (CHead e1 (Flat f) u1))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 n0 t u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 n0 t e1 e2))))))))))))) (\lambda 
(k: K).(K_ind (\lambda (k0: K).(\forall (i: nat).(\forall (v0: T).(\forall 
(u1: T).(\forall (u2: T).((subst0 i v0 u1 u2) \to (\forall (c: C).((eq nat (s 
k0 i) O) \to (or4 (drop (s k0 i) (s k0 i) (CHead c k0 u1) (CHead c k0 u2)) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u4: 
T).(eq C (CHead c k0 u2) (CHead e0 (Flat f) u4)))))) (\lambda (f: F).(\lambda 
(e0: C).(\lambda (u3: T).(\lambda (_: T).(drop (s k0 i) (s k0 i) (CHead c k0 
u1) (CHead e0 (Flat f) u3)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u3: 
T).(\lambda (u4: T).(subst0 (s k0 i) v0 u3 u4)))))) (ex3_4 F C C T (\lambda 
(f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C (CHead c k0 u2) 
(CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop (s k0 i) (s k0 i) (CHead c k0 u1) (CHead e1 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (s k0 i) v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u4: T).(eq C (CHead c k0 
u2) (CHead e2 (Flat f) u4))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u3: T).(\lambda (_: T).(drop (s k0 i) (s k0 i) (CHead c k0 
u1) (CHead e1 (Flat f) u3))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u3: T).(\lambda (u4: T).(subst0 (s k0 i) v0 u3 u4)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: 
T).(csubst0 (s k0 i) v0 e1 e2)))))))))))))))) (\lambda (b: B).(\lambda (i: 
nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (subst0 
i v0 u1 u2)).(\lambda (c: C).(\lambda (H3: (eq nat (S i) O)).(let H4 \def 
(eq_ind nat (S i) (\lambda (ee: nat).(match ee in nat return (\lambda (_: 
nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) I O H3) in 
(False_ind (or4 (drop (S i) (S i) (CHead c (Bind b) u1) (CHead c (Bind b) 
u2)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(u4: T).(eq C (CHead c (Bind b) u2) (CHead e0 (Flat f) u4)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u3: T).(\lambda (_: T).(drop (S i) (S i) (CHead 
c (Bind b) u1) (CHead e0 (Flat f) u3)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u3: T).(\lambda (u4: T).(subst0 (S i) v0 u3 u4)))))) (ex3_4 F C 
C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C 
(CHead c (Bind b) u2) (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S i) (S i) (CHead c (Bind b) 
u1) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (S i) v0 e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u4: T).(eq 
C (CHead c (Bind b) u2) (CHead e2 (Flat f) u4))))))) (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u3: T).(\lambda (_: T).(drop (S i) (S i) 
(CHead c (Bind b) u1) (CHead e1 (Flat f) u3))))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: T).(subst0 (S i) v0 u3 
u4)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (S i) v0 e1 e2)))))))) H4)))))))))) (\lambda (f: 
F).(\lambda (i: nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (H2: (subst0 i v0 u1 u2)).(\lambda (c: C).(\lambda (H3: (eq nat i 
O)).(let H4 \def (eq_ind nat i (\lambda (n0: nat).(subst0 n0 v0 u1 u2)) H2 O 
H3) in (eq_ind_r nat O (\lambda (n0: nat).(or4 (drop n0 n0 (CHead c (Flat f) 
u1) (CHead c (Flat f) u2)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u4: T).(eq C (CHead c (Flat f) u2) (CHead e0 
(Flat f0) u4)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u3: 
T).(\lambda (_: T).(drop n0 n0 (CHead c (Flat f) u1) (CHead e0 (Flat f0) 
u3)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: 
T).(subst0 n0 v0 u3 u4)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C (CHead c (Flat f) u2) (CHead e2 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(drop n0 n0 (CHead c (Flat f) u1) (CHead e1 (Flat f0) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 n0 v0 e1 
e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u4: T).(eq C (CHead c (Flat f) u2) (CHead e2 
(Flat f0) u4))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u3: T).(\lambda (_: T).(drop n0 n0 (CHead c (Flat f) u1) (CHead 
e1 (Flat f0) u3))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u3: T).(\lambda (u4: T).(subst0 n0 v0 u3 u4)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
n0 v0 e1 e2))))))))) (or4_intro1 (drop O O (CHead c (Flat f) u1) (CHead c 
(Flat f) u2)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u4: T).(eq C (CHead c (Flat f) u2) (CHead e0 (Flat f0) u4)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (u3: T).(\lambda (_: T).(drop O O 
(CHead c (Flat f) u1) (CHead e0 (Flat f0) u3)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u3: T).(\lambda (u4: T).(subst0 O v0 u3 u4)))))) (ex3_4 F C 
C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C 
(CHead c (Flat f) u2) (CHead e2 (Flat f0) u)))))) (\lambda (f0: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(drop O O (CHead c (Flat f) u1) 
(CHead e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u4: T).(eq C 
(CHead c (Flat f) u2) (CHead e2 (Flat f0) u4))))))) (\lambda (f0: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u3: T).(\lambda (_: T).(drop O O (CHead c 
(Flat f) u1) (CHead e1 (Flat f0) u3))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: T).(subst0 O v0 u3 u4)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v0 e1 e2))))))) (ex3_4_intro F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u4: T).(eq C (CHead c (Flat f) 
u2) (CHead e0 (Flat f0) u4)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda 
(u3: T).(\lambda (_: T).(drop O O (CHead c (Flat f) u1) (CHead e0 (Flat f0) 
u3)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: 
T).(subst0 O v0 u3 u4))))) f c u1 u2 (refl_equal C (CHead c (Flat f) u2)) 
(drop_refl (CHead c (Flat f) u1)) H4)) i H3)))))))))) k)) (\lambda (k: 
K).(K_ind (\lambda (k0: K).(\forall (i: nat).(\forall (c3: C).(\forall (c4: 
C).(\forall (v0: T).((csubst0 i v0 c3 c4) \to ((((eq nat i O) \to (or4 (drop 
i i c3 c4) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C c4 (CHead e0 (Flat f) u2)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop i i c3 (CHead e0 
(Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 i v0 u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C c4 (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop i i c3 
(CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 i v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C c4 
(CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop i i c3 (CHead e1 (Flat f) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 i v0 u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v0 e1 e2)))))))))) \to 
(\forall (u: T).((eq nat (s k0 i) O) \to (or4 (drop (s k0 i) (s k0 i) (CHead 
c3 k0 u) (CHead c4 k0 u)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead c4 k0 u) (CHead e0 (Flat f) 
u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (s k0 i) (s k0 i) (CHead c3 k0 u) (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 (s 
k0 i) v0 u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u0: T).(eq C (CHead c4 k0 u) (CHead e2 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(drop (s k0 
i) (s k0 i) (CHead c3 k0 u) (CHead e1 (Flat f) u0)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (s k0 i) v0 e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead c4 k0 u) (CHead e2 (Flat f) 
u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (s k0 i) (s k0 i) (CHead c3 k0 u) (CHead e1 (Flat f) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 (s k0 i) v0 u1 u2)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (s k0 i) v0 
e1 e2))))))))))))))))) (\lambda (b: B).(\lambda (i: nat).(\lambda (c3: 
C).(\lambda (c4: C).(\lambda (v0: T).(\lambda (_: (csubst0 i v0 c3 
c4)).(\lambda (_: (((eq nat i O) \to (or4 (drop i i c3 c4) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c4 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop i i c3 (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v0 u1 u2)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C c4 (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop i i c3 (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C c4 (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop i i c3 (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i v0 u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 i v0 e1 e2))))))))))).(\lambda (u: T).(\lambda (H4: (eq nat 
(S i) O)).(let H5 \def (eq_ind nat (S i) (\lambda (ee: nat).(match ee in nat 
return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow 
True])) I O H4) in (False_ind (or4 (drop (S i) (S i) (CHead c3 (Bind b) u) 
(CHead c4 (Bind b) u)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead c4 (Bind b) u) (CHead e0 
(Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S i) (S i) (CHead c3 (Bind b) u) (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 (S 
i) v0 u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u0: T).(eq C (CHead c4 (Bind b) u) (CHead e2 (Flat f) 
u0)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: 
T).(drop (S i) (S i) (CHead c3 (Bind b) u) (CHead e1 (Flat f) u0)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (S 
i) v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead c4 (Bind b) u) (CHead 
e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S i) (S i) (CHead c3 (Bind b) u) 
(CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 (S i) v0 u1 u2)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: 
T).(csubst0 (S i) v0 e1 e2)))))))) H5))))))))))) (\lambda (f: F).(\lambda (i: 
nat).(\lambda (c3: C).(\lambda (c4: C).(\lambda (v0: T).(\lambda (H2: 
(csubst0 i v0 c3 c4)).(\lambda (H3: (((eq nat i O) \to (or4 (drop i i c3 c4) 
(ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C c4 (CHead e0 (Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop i i c3 (CHead e0 (Flat f0) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 i 
v0 u1 u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C c4 (CHead e2 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop i i c3 (CHead e1 
(Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 i v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C c4 (CHead e2 
(Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop i i c3 (CHead e1 (Flat f0) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 i v0 u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 i v0 e1 
e2))))))))))).(\lambda (u: T).(\lambda (H4: (eq nat i O)).(let H5 \def 
(eq_ind nat i (\lambda (n0: nat).((eq nat n0 O) \to (or4 (drop n0 n0 c3 c4) 
(ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C c4 (CHead e0 (Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop n0 n0 c3 (CHead e0 (Flat f0) 
u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 n0 v0 u1 u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u0: T).(eq C c4 (CHead e2 (Flat f0) u0)))))) 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(drop n0 
n0 c3 (CHead e1 (Flat f0) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 n0 v0 e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq 
C c4 (CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (_: T).(drop n0 n0 c3 (CHead e1 (Flat f0) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 n0 v0 u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 n0 v0 e1 
e2)))))))))) H3 O H4) in (let H6 \def (eq_ind nat i (\lambda (n0: 
nat).(csubst0 n0 v0 c3 c4)) H2 O H4) in (eq_ind_r nat O (\lambda (n0: 
nat).(or4 (drop n0 n0 (CHead c3 (Flat f) u) (CHead c4 (Flat f) u)) (ex3_4 F C 
T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C 
(CHead c4 (Flat f) u) (CHead e0 (Flat f0) u2)))))) (\lambda (f0: F).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(drop n0 n0 (CHead c3 (Flat f) u) 
(CHead e0 (Flat f0) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 n0 v0 u1 u2)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(eq C (CHead c4 (Flat f) 
u) (CHead e2 (Flat f0) u0)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u0: T).(drop n0 n0 (CHead c3 (Flat f) u) (CHead e1 (Flat f0) 
u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 n0 v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead c4 (Flat f) 
u) (CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (_: T).(drop n0 n0 (CHead c3 (Flat f) u) 
(CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 n0 v0 u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
n0 v0 e1 e2))))))))) (or4_intro2 (drop O O (CHead c3 (Flat f) u) (CHead c4 
(Flat f) u)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C (CHead c4 (Flat f) u) (CHead e0 (Flat f0) u2)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop O O 
(CHead c3 (Flat f) u) (CHead e0 (Flat f0) u1)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v0 u1 u2)))))) (ex3_4 F C 
C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(eq C 
(CHead c4 (Flat f) u) (CHead e2 (Flat f0) u0)))))) (\lambda (f0: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(drop O O (CHead c3 (Flat f) u) 
(CHead e1 (Flat f0) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C 
(CHead c4 (Flat f) u) (CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop O O (CHead c3 
(Flat f) u) (CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v0 u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v0 e1 e2))))))) (ex3_4_intro F C C T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(eq C (CHead c4 (Flat f) 
u) (CHead e2 (Flat f0) u0)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u0: T).(drop O O (CHead c3 (Flat f) u) (CHead e1 (Flat f0) 
u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v0 e1 e2))))) f c3 c4 u (refl_equal C (CHead c4 (Flat f) u)) 
(drop_refl (CHead c3 (Flat f) u)) H6)) i H4)))))))))))) k)) (\lambda (k: 
K).(K_ind (\lambda (k0: K).(\forall (i: nat).(\forall (v0: T).(\forall (u1: 
T).(\forall (u2: T).((subst0 i v0 u1 u2) \to (\forall (c3: C).(\forall (c4: 
C).((csubst0 i v0 c3 c4) \to ((((eq nat i O) \to (or4 (drop i i c3 c4) (ex3_4 
F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u4: T).(eq 
C c4 (CHead e0 (Flat f) u4)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda 
(u3: T).(\lambda (_: T).(drop i i c3 (CHead e0 (Flat f) u3)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: T).(subst0 i v0 u3 u4)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C c4 (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop i i c3 (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u4: T).(eq C c4 (CHead e2 (Flat f) u4))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u3: T).(\lambda 
(_: T).(drop i i c3 (CHead e1 (Flat f) u3))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: T).(subst0 i v0 u3 u4)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 i v0 e1 e2)))))))))) \to ((eq nat (s k0 i) O) \to (or4 (drop 
(s k0 i) (s k0 i) (CHead c3 k0 u1) (CHead c4 k0 u2)) (ex3_4 F C T T (\lambda 
(f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u4: T).(eq C (CHead c4 k0 
u2) (CHead e0 (Flat f) u4)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda 
(u3: T).(\lambda (_: T).(drop (s k0 i) (s k0 i) (CHead c3 k0 u1) (CHead e0 
(Flat f) u3)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u3: T).(\lambda 
(u4: T).(subst0 (s k0 i) v0 u3 u4)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C (CHead c4 k0 u2) 
(CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop (s k0 i) (s k0 i) (CHead c3 k0 u1) (CHead e1 (Flat 
f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (s k0 i) v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u4: T).(eq C (CHead c4 k0 
u2) (CHead e2 (Flat f) u4))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u3: T).(\lambda (_: T).(drop (s k0 i) (s k0 i) (CHead c3 k0 
u1) (CHead e1 (Flat f) u3))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u3: T).(\lambda (u4: T).(subst0 (s k0 i) v0 u3 u4)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: 
T).(csubst0 (s k0 i) v0 e1 e2))))))))))))))))))) (\lambda (b: B).(\lambda (i: 
nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (subst0 
i v0 u1 u2)).(\lambda (c3: C).(\lambda (c4: C).(\lambda (_: (csubst0 i v0 c3 
c4)).(\lambda (_: (((eq nat i O) \to (or4 (drop i i c3 c4) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u4: T).(eq C c4 
(CHead e0 (Flat f) u4)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u3: 
T).(\lambda (_: T).(drop i i c3 (CHead e0 (Flat f) u3)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: T).(subst0 i v0 u3 u4)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C c4 (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop i i c3 (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u4: T).(eq C c4 (CHead e2 (Flat f) u4))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u3: T).(\lambda 
(_: T).(drop i i c3 (CHead e1 (Flat f) u3))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: T).(subst0 i v0 u3 u4)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 i v0 e1 e2))))))))))).(\lambda (H5: (eq nat (S i) O)).(let H6 
\def (eq_ind nat (S i) (\lambda (ee: nat).(match ee in nat return (\lambda 
(_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) I O H5) 
in (False_ind (or4 (drop (S i) (S i) (CHead c3 (Bind b) u1) (CHead c4 (Bind 
b) u2)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u4: T).(eq C (CHead c4 (Bind b) u2) (CHead e0 (Flat f) u4)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u3: T).(\lambda (_: T).(drop (S i) 
(S i) (CHead c3 (Bind b) u1) (CHead e0 (Flat f) u3)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: T).(subst0 (S i) v0 u3 
u4)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C (CHead c4 (Bind b) u2) (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S i) 
(S i) (CHead c3 (Bind b) u1) (CHead e1 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (S i) v0 e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u4: T).(eq C (CHead c4 (Bind b) u2) (CHead e2 
(Flat f) u4))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u3: T).(\lambda (_: T).(drop (S i) (S i) (CHead c3 (Bind b) u1) (CHead e1 
(Flat f) u3))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u3: T).(\lambda (u4: T).(subst0 (S i) v0 u3 u4)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(S i) v0 e1 e2)))))))) H6))))))))))))) (\lambda (f: F).(\lambda (i: 
nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H2: (subst0 
i v0 u1 u2)).(\lambda (c3: C).(\lambda (c4: C).(\lambda (H3: (csubst0 i v0 c3 
c4)).(\lambda (H4: (((eq nat i O) \to (or4 (drop i i c3 c4) (ex3_4 F C T T 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u4: T).(eq C c4 
(CHead e0 (Flat f0) u4)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u3: 
T).(\lambda (_: T).(drop i i c3 (CHead e0 (Flat f0) u3)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: T).(subst0 i v0 u3 u4)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C c4 (CHead e2 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop i i c3 (CHead e1 (Flat f0) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 i 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (u4: T).(eq C c4 (CHead e2 (Flat f0) 
u4))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u3: 
T).(\lambda (_: T).(drop i i c3 (CHead e1 (Flat f0) u3))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: T).(subst0 
i v0 u3 u4)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 i v0 e1 e2))))))))))).(\lambda (H5: (eq nat i 
O)).(let H6 \def (eq_ind nat i (\lambda (n0: nat).((eq nat n0 O) \to (or4 
(drop n0 n0 c3 c4) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (u4: T).(eq C c4 (CHead e0 (Flat f0) u4)))))) (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (u3: T).(\lambda (_: T).(drop n0 n0 c3 (CHead e0 
(Flat f0) u3)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u3: T).(\lambda 
(u4: T).(subst0 n0 v0 u3 u4)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u: T).(eq C c4 (CHead e2 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop n0 n0 
c3 (CHead e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 n0 v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u4: T).(eq C c4 
(CHead e2 (Flat f0) u4))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u3: T).(\lambda (_: T).(drop n0 n0 c3 (CHead e1 (Flat f0) 
u3))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u3: 
T).(\lambda (u4: T).(subst0 n0 v0 u3 u4)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 n0 v0 e1 
e2)))))))))) H4 O H5) in (let H7 \def (eq_ind nat i (\lambda (n0: 
nat).(csubst0 n0 v0 c3 c4)) H3 O H5) in (let H8 \def (eq_ind nat i (\lambda 
(n0: nat).(subst0 n0 v0 u1 u2)) H2 O H5) in (eq_ind_r nat O (\lambda (n0: 
nat).(or4 (drop n0 n0 (CHead c3 (Flat f) u1) (CHead c4 (Flat f) u2)) (ex3_4 F 
C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u4: T).(eq 
C (CHead c4 (Flat f) u2) (CHead e0 (Flat f0) u4)))))) (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (u3: T).(\lambda (_: T).(drop n0 n0 (CHead c3 
(Flat f) u1) (CHead e0 (Flat f0) u3)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u3: T).(\lambda (u4: T).(subst0 n0 v0 u3 u4)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C 
(CHead c4 (Flat f) u2) (CHead e2 (Flat f0) u)))))) (\lambda (f0: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(drop n0 n0 (CHead c3 (Flat f) u1) 
(CHead e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 n0 v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u4: T).(eq C 
(CHead c4 (Flat f) u2) (CHead e2 (Flat f0) u4))))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u3: T).(\lambda (_: T).(drop n0 
n0 (CHead c3 (Flat f) u1) (CHead e1 (Flat f0) u3))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: T).(subst0 
n0 v0 u3 u4)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 n0 v0 e1 e2))))))))) (or4_intro3 (drop O O 
(CHead c3 (Flat f) u1) (CHead c4 (Flat f) u2)) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u4: T).(eq C (CHead c4 (Flat f) 
u2) (CHead e0 (Flat f0) u4)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda 
(u3: T).(\lambda (_: T).(drop O O (CHead c3 (Flat f) u1) (CHead e0 (Flat f0) 
u3)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: 
T).(subst0 O v0 u3 u4)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C (CHead c4 (Flat f) u2) (CHead e2 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(drop O O (CHead c3 (Flat f) u1) (CHead e1 (Flat f0) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v0 e1 
e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u4: T).(eq C (CHead c4 (Flat f) u2) (CHead e2 
(Flat f0) u4))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u3: T).(\lambda (_: T).(drop O O (CHead c3 (Flat f) u1) (CHead 
e1 (Flat f0) u3))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u3: T).(\lambda (u4: T).(subst0 O v0 u3 u4)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v0 e1 e2))))))) (ex4_5_intro F C C T T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u4: T).(eq C (CHead c4 (Flat f) 
u2) (CHead e2 (Flat f0) u4))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u3: T).(\lambda (_: T).(drop O O (CHead c3 (Flat f) u1) 
(CHead e1 (Flat f0) u3))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u3: T).(\lambda (u4: T).(subst0 O v0 u3 u4)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v0 e1 e2)))))) f c3 c4 u1 u2 (refl_equal C (CHead c4 (Flat f) u2)) 
(drop_refl (CHead c3 (Flat f) u1)) H8 H7)) i H5))))))))))))))) k)) y v c1 c2 
H1))) H) e (drop_gen_refl c2 e H0)))))))) (\lambda (n0: nat).(\lambda (IHn: 
((\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 n0 v c1 c2) \to 
(\forall (e: C).((drop n0 O c2 e) \to (or4 (drop n0 O c1 e) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop n0 O c1 (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop n0 O c1 (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop n0 O c1 (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))))))))))))).(\lambda (c1: C).(C_ind 
(\lambda (c: C).(\forall (c2: C).(\forall (v: T).((csubst0 (S n0) v c c2) \to 
(\forall (e: C).((drop (S n0) O c2 e) \to (or4 (drop (S n0) O c e) (ex3_4 F C 
T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O c (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O c (CHead e1 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat 
f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O c (CHead e1 (Flat f) u1))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))))))))) (\lambda (n1: 
nat).(\lambda (c2: C).(\lambda (v: T).(\lambda (H: (csubst0 (S n0) v (CSort 
n1) c2)).(\lambda (e: C).(\lambda (_: (drop (S n0) O c2 e)).(csubst0_gen_sort 
c2 v (S n0) n1 H (or4 (drop (S n0) O (CSort n1) e) (ex3_4 F C T T (\lambda 
(f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 
(Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CSort n1) (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CSort n1) (CHead e1 (Flat 
f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat 
f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CSort n1) (CHead e1 (Flat f) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))))))))))) 
(\lambda (c: C).(\lambda (H: ((\forall (c2: C).(\forall (v: T).((csubst0 (S 
n0) v c c2) \to (\forall (e: C).((drop (S n0) O c2 e) \to (or4 (drop (S n0) O 
c e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O c (CHead e0 (Flat f) 
u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) 
O c (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O c (CHead e1 (Flat f) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c2: C).(\lambda 
(v: T).(\lambda (H0: (csubst0 (S n0) v (CHead c k t) c2)).(\lambda (e: 
C).(\lambda (H1: (drop (S n0) O c2 e)).(or3_ind (ex3_2 T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat (S n0) (s k j)))) (\lambda (u2: T).(\lambda (_: 
nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j 
v t u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat (S n0) (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c c3)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat (S n0) (s k j))))) (\lambda (u2: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3))))) (or4 (drop (S 
n0) O (CHead c k t) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c k t) (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e 
(CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop (S n0) O (CHead c k t) (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c k t) (CHead e1 (Flat f) u1))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda (H2: (ex3_2 T nat 
(\lambda (_: T).(\lambda (j: nat).(eq nat (S n0) (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v t u2))))).(ex3_2_ind T nat (\lambda (_: T).(\lambda (j: 
nat).(eq nat (S n0) (s k j)))) (\lambda (u2: T).(\lambda (_: nat).(eq C c2 
(CHead c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j v t u2))) (or4 
(drop (S n0) O (CHead c k t) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c k t) (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e 
(CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop (S n0) O (CHead c k t) (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c k t) (CHead e1 (Flat f) u1))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda (x0: T).(\lambda 
(x1: nat).(\lambda (H3: (eq nat (S n0) (s k x1))).(\lambda (H4: (eq C c2 
(CHead c k x0))).(\lambda (H5: (subst0 x1 v t x0)).(let H6 \def (eq_ind C c2 
(\lambda (c0: C).(drop (S n0) O c0 e)) H1 (CHead c k x0) H4) in (K_ind 
(\lambda (k0: K).((eq nat (S n0) (s k0 x1)) \to ((drop (r k0 n0) O c e) \to 
(or4 (drop (S n0) O (CHead c k0 t) e) (ex3_4 F C T T (\lambda (f: F).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c k0 t) (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e 
(CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop (S n0) O (CHead c k0 t) (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c k0 t) (CHead e1 (Flat f) u1))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))))))) (\lambda (b: 
B).(\lambda (H7: (eq nat (S n0) (s (Bind b) x1))).(\lambda (H8: (drop (r 
(Bind b) n0) O c e)).(let H9 \def (f_equal nat nat (\lambda (e0: nat).(match 
e0 in nat return (\lambda (_: nat).nat) with [O \Rightarrow n0 | (S n1) 
\Rightarrow n1])) (S n0) (S x1) H7) in (let H10 \def (eq_ind_r nat x1 
(\lambda (n1: nat).(subst0 n1 v t x0)) H5 n0 H9) in (or4_intro0 (drop (S n0) 
O (CHead c (Bind b) t) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c (Bind b) t) (CHead 
e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) 
(CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))) (drop_drop (Bind b) n0 c e H8 t))))))) (\lambda (f: 
F).(\lambda (H7: (eq nat (S n0) (s (Flat f) x1))).(\lambda (H8: (drop (r 
(Flat f) n0) O c e)).(let H9 \def (f_equal nat nat (\lambda (e0: nat).e0) (S 
n0) x1 H7) in (let H10 \def (eq_ind_r nat x1 (\lambda (n1: nat).(subst0 n1 v 
t x0)) H5 (S n0) H9) in (or4_intro0 (drop (S n0) O (CHead c (Flat f) t) e) 
(ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e0 (Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) 
(CHead e0 (Flat f0) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f0) u2))))))) 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (drop_drop 
(Flat f) n0 c e H8 t))))))) k H3 (drop_gen_drop k c e x0 n0 H6)))))))) H2)) 
(\lambda (H2: (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat (S n0) 
(s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) 
(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3))))).(ex3_2_ind C nat 
(\lambda (_: C).(\lambda (j: nat).(eq nat (S n0) (s k j)))) (\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c c3))) (or4 (drop (S n0) O (CHead c k t) e) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c k t) (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v 
u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c k 
t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c k t) (CHead e1 
(Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (x0: C).(\lambda (x1: nat).(\lambda (H3: (eq nat (S n0) 
(s k x1))).(\lambda (H4: (eq C c2 (CHead x0 k t))).(\lambda (H5: (csubst0 x1 
v c x0)).(let H6 \def (eq_ind C c2 (\lambda (c0: C).(drop (S n0) O c0 e)) H1 
(CHead x0 k t) H4) in (K_ind (\lambda (k0: K).((eq nat (S n0) (s k0 x1)) \to 
((drop (r k0 n0) O x0 e) \to (or4 (drop (S n0) O (CHead c k0 t) e) (ex3_4 F C 
T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c k0 t) (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v 
u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c 
k0 t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq 
C e (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c k0 t) (CHead 
e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))))))) (\lambda (b: B).(\lambda (H7: (eq nat (S n0) (s (Bind b) 
x1))).(\lambda (H8: (drop (r (Bind b) n0) O x0 e)).(let H9 \def (f_equal nat 
nat (\lambda (e0: nat).(match e0 in nat return (\lambda (_: nat).nat) with [O 
\Rightarrow n0 | (S n1) \Rightarrow n1])) (S n0) (S x1) H7) in (let H10 \def 
(eq_ind_r nat x1 (\lambda (n1: nat).(csubst0 n1 v c x0)) H5 n0 H9) in (let 
H11 \def (IHn c x0 v H10 e H8) in (or4_ind (drop n0 O c e) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop n0 O c (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop n0 O c (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop n0 O c (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (or4 (drop (S n0) O (CHead c (Bind b) t) e) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: 
T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) 
(CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda 
(H12: (drop n0 O c e)).(or4_intro0 (drop (S n0) O (CHead c (Bind b) t) e) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: 
T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) 
(CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (drop_drop 
(Bind b) n0 c e H12 t))) (\lambda (H12: (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat 
f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop n0 O c (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2))))))).(ex3_4_ind F C 
T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop n0 O c (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2))))) 
(or4 (drop (S n0) O (CHead c (Bind b) t) e) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat 
f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))))) (\lambda (x2: F).(\lambda (x3: C).(\lambda 
(x4: T).(\lambda (x5: T).(\lambda (H13: (eq C e (CHead x3 (Flat x2) 
x5))).(\lambda (H14: (drop n0 O c (CHead x3 (Flat x2) x4))).(\lambda (H15: 
(subst0 O v x4 x5)).(eq_ind_r C (CHead x3 (Flat x2) x5) (\lambda (c0: C).(or4 
(drop (S n0) O (CHead c (Bind b) t) c0) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 (CHead e0 (Flat 
f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C c0 (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C c0 (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))) (or4_intro1 (drop (S n0) O (CHead c (Bind 
b) t) (CHead x3 (Flat x2) x5)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x3 (Flat x2) x5) (CHead e0 
(Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v 
u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C (CHead x3 (Flat x2) x5) (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) 
O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C (CHead x3 (Flat x2) x5) (CHead e2 (Flat f) 
u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) 
(ex3_4_intro F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C (CHead x3 (Flat x2) x5) (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2))))) 
x2 x3 x4 x5 (refl_equal C (CHead x3 (Flat x2) x5)) (drop_drop (Bind b) n0 c 
(CHead x3 (Flat x2) x4) H14 t) H15)) e H13)))))))) H12)) (\lambda (H12: 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop n0 O c (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2))))))).(ex3_4_ind F C C T (\lambda (f: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop n0 O c (CHead e1 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2))))) (or4 (drop (S n0) O (CHead c (Bind b) t) e) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: 
T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) 
(CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda 
(x2: F).(\lambda (x3: C).(\lambda (x4: C).(\lambda (x5: T).(\lambda (H13: (eq 
C e (CHead x4 (Flat x2) x5))).(\lambda (H14: (drop n0 O c (CHead x3 (Flat x2) 
x5))).(\lambda (H15: (csubst0 O v x3 x4)).(eq_ind_r C (CHead x4 (Flat x2) x5) 
(\lambda (c0: C).(or4 (drop (S n0) O (CHead c (Bind b) t) c0) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) 
u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C c0 (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) 
O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C c0 (CHead e2 (Flat f) u2))))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u1))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))))) (or4_intro2 (drop (S n0) O 
(CHead c (Bind b) t) (CHead x4 (Flat x2) x5)) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x4 (Flat 
x2) x5) (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda 
(u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat 
f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C (CHead x4 (Flat x2) x5) (CHead e2 
(Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x4 (Flat x2) x5) (CHead e2 
(Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat 
f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) 
(ex3_4_intro F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C (CHead x4 (Flat x2) x5) (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) 
O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))) x2 x3 x4 x5 
(refl_equal C (CHead x4 (Flat x2) x5)) (drop_drop (Bind b) n0 c (CHead x3 
(Flat x2) x5) H14 t) H15)) e H13)))))))) H12)) (\lambda (H12: (ex4_5 F C C T 
T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop n0 O c (CHead e1 
(Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))).(ex4_5_ind F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop n0 O c (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (or4 (drop (S n0) O (CHead c (Bind b) t) e) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: 
T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) 
(CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda 
(x2: F).(\lambda (x3: C).(\lambda (x4: C).(\lambda (x5: T).(\lambda (x6: 
T).(\lambda (H13: (eq C e (CHead x4 (Flat x2) x6))).(\lambda (H14: (drop n0 O 
c (CHead x3 (Flat x2) x5))).(\lambda (H15: (subst0 O v x5 x6)).(\lambda (H16: 
(csubst0 O v x3 x4)).(eq_ind_r C (CHead x4 (Flat x2) x6) (\lambda (c0: 
C).(or4 (drop (S n0) O (CHead c (Bind b) t) c0) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 (CHead e0 (Flat 
f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C c0 (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C c0 (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))) (or4_intro3 (drop (S n0) O (CHead c (Bind 
b) t) (CHead x4 (Flat x2) x6)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x4 (Flat x2) x6) (CHead e0 
(Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v 
u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C (CHead x4 (Flat x2) x6) (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) 
O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C (CHead x4 (Flat x2) x6) (CHead e2 (Flat f) 
u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) 
(ex4_5_intro F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x4 (Flat x2) x6) (CHead e2 
(Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat 
f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
x2 x3 x4 x5 x6 (refl_equal C (CHead x4 (Flat x2) x6)) (drop_drop (Bind b) n0 
c (CHead x3 (Flat x2) x5) H14 t) H15 H16)) e H13)))))))))) H12)) H11))))))) 
(\lambda (f: F).(\lambda (H7: (eq nat (S n0) (s (Flat f) x1))).(\lambda (H8: 
(drop (r (Flat f) n0) O x0 e)).(let H9 \def (f_equal nat nat (\lambda (e0: 
nat).e0) (S n0) x1 H7) in (let H10 \def (eq_ind_r nat x1 (\lambda (n1: 
nat).(csubst0 n1 v c x0)) H5 (S n0) H9) in (let H11 \def (H x0 v H10 e H8) in 
(or4_ind (drop (S n0) O c e) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f0) u2)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O c (CHead e0 (Flat f0) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O c (CHead e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O c (CHead 
e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))) (or4 (drop (S n0) O (CHead c (Flat f) t) e) (ex3_4 F C T T 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e0 (Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) 
u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S 
n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f0) u2))))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u1))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda (H12: (drop (S n0) 
O c e)).(or4_intro0 (drop (S n0) O (CHead c (Flat f) t) e) (ex3_4 F C T T 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e0 (Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) 
u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S 
n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f0) u2))))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u1))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (drop_drop (Flat f) n0 c e 
H12 t))) (\lambda (H12: (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f0) u2)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O c (CHead e0 (Flat f0) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 O v u1 u2))))))).(ex3_4_ind F C T T (\lambda 
(f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 
(Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O c (CHead e0 (Flat f0) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2))))) 
(or4 (drop (S n0) O (CHead c (Flat f) t) e) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat 
f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) u1)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C e (CHead e2 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c 
(Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Flat f) t) (CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))))) (\lambda (x2: F).(\lambda (x3: C).(\lambda 
(x4: T).(\lambda (x5: T).(\lambda (H13: (eq C e (CHead x3 (Flat x2) 
x5))).(\lambda (H14: (drop (S n0) O c (CHead x3 (Flat x2) x4))).(\lambda 
(H15: (subst0 O v x4 x5)).(eq_ind_r C (CHead x3 (Flat x2) x5) (\lambda (c0: 
C).(or4 (drop (S n0) O (CHead c (Flat f) t) c0) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 (CHead e0 (Flat 
f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) u1)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C c0 (CHead e2 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c 
(Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C c0 (CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Flat f) t) (CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))) (or4_intro1 (drop (S n0) O (CHead c (Flat 
f) t) (CHead x3 (Flat x2) x5)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x3 (Flat x2) x5) (CHead e0 
(Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) 
u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C (CHead x3 (Flat x2) x5) (CHead e2 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x3 (Flat x2) x5) (CHead e2 
(Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) 
(CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))) (ex3_4_intro F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x3 (Flat x2) x5) (CHead e0 
(Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) 
u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2))))) x2 x3 x4 x5 (refl_equal C (CHead x3 (Flat x2) x5)) 
(drop_drop (Flat f) n0 c (CHead x3 (Flat x2) x4) H14 t) H15)) e H13)))))))) 
H12)) (\lambda (H12: (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O c (CHead 
e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2))))))).(ex3_4_ind F C C T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O c (CHead e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))) (or4 (drop (S n0) 
O (CHead c (Flat f) t) e) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f0) u2)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C e (CHead e2 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c (Flat f) t) (CHead 
e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) 
(CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2)))))))) (\lambda (x2: F).(\lambda (x3: C).(\lambda (x4: C).(\lambda 
(x5: T).(\lambda (H13: (eq C e (CHead x4 (Flat x2) x5))).(\lambda (H14: (drop 
(S n0) O c (CHead x3 (Flat x2) x5))).(\lambda (H15: (csubst0 O v x3 
x4)).(eq_ind_r C (CHead x4 (Flat x2) x5) (\lambda (c0: C).(or4 (drop (S n0) O 
(CHead c (Flat f) t) c0) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 (CHead e0 (Flat f0) u2)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C c0 (CHead e2 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c (Flat f) t) (CHead 
e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 
(CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) 
(CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))))) (or4_intro2 (drop (S n0) O (CHead c (Flat f) t) (CHead x4 
(Flat x2) x5)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C (CHead x4 (Flat x2) x5) (CHead e0 (Flat f0) 
u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) u1)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C (CHead x4 (Flat x2) x5) (CHead e2 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S 
n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C (CHead x4 (Flat x2) x5) (CHead e2 (Flat f0) 
u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) 
(ex3_4_intro F C C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C (CHead x4 (Flat x2) x5) (CHead e2 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S 
n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))) 
x2 x3 x4 x5 (refl_equal C (CHead x4 (Flat x2) x5)) (drop_drop (Flat f) n0 c 
(CHead x3 (Flat x2) x5) H14 t) H15)) e H13)))))))) H12)) (\lambda (H12: 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f0) u2))))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O c (CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))))).(ex4_5_ind F C C T T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O c (CHead e1 (Flat f0) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(or4 (drop (S n0) O (CHead c (Flat f) t) e) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat 
f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) u1)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C e (CHead e2 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c 
(Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Flat f) t) (CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))))) (\lambda (x2: F).(\lambda (x3: C).(\lambda 
(x4: C).(\lambda (x5: T).(\lambda (x6: T).(\lambda (H13: (eq C e (CHead x4 
(Flat x2) x6))).(\lambda (H14: (drop (S n0) O c (CHead x3 (Flat x2) 
x5))).(\lambda (H15: (subst0 O v x5 x6)).(\lambda (H16: (csubst0 O v x3 
x4)).(eq_ind_r C (CHead x4 (Flat x2) x6) (\lambda (c0: C).(or4 (drop (S n0) O 
(CHead c (Flat f) t) c0) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 (CHead e0 (Flat f0) u2)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C c0 (CHead e2 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c (Flat f) t) (CHead 
e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 
(CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) 
(CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))))) (or4_intro3 (drop (S n0) O (CHead c (Flat f) t) (CHead x4 
(Flat x2) x6)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C (CHead x4 (Flat x2) x6) (CHead e0 (Flat f0) 
u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) u1)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C (CHead x4 (Flat x2) x6) (CHead e2 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S 
n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C (CHead x4 (Flat x2) x6) (CHead e2 (Flat f0) 
u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) 
(ex4_5_intro F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x4 (Flat x2) x6) (CHead e2 
(Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) 
(CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2)))))) x2 x3 x4 x5 x6 (refl_equal C (CHead x4 (Flat x2) x6)) 
(drop_drop (Flat f) n0 c (CHead x3 (Flat x2) x5) H14 t) H15 H16)) e 
H13)))))))))) H12)) H11))))))) k H3 (drop_gen_drop k x0 e t n0 H6)))))))) 
H2)) (\lambda (H2: (ex4_3 T C nat (\lambda (_: T).(\lambda (_: C).(\lambda 
(j: nat).(eq nat (S n0) (s k j))))) (\lambda (u2: T).(\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda 
(_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c c3)))))).(ex4_3_ind T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat (S n0) (s k j))))) (\lambda (u2: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3)))) (or4 (drop (S n0) 
O (CHead c k t) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
k t) (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O (CHead c k t) (CHead e1 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c k t) (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))))) (\lambda (x0: T).(\lambda (x1: C).(\lambda 
(x2: nat).(\lambda (H3: (eq nat (S n0) (s k x2))).(\lambda (H4: (eq C c2 
(CHead x1 k x0))).(\lambda (H5: (subst0 x2 v t x0)).(\lambda (H6: (csubst0 x2 
v c x1)).(let H7 \def (eq_ind C c2 (\lambda (c0: C).(drop (S n0) O c0 e)) H1 
(CHead x1 k x0) H4) in (K_ind (\lambda (k0: K).((eq nat (S n0) (s k0 x2)) \to 
((drop (r k0 n0) O x1 e) \to (or4 (drop (S n0) O (CHead c k0 t) e) (ex3_4 F C 
T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c k0 t) (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v 
u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c 
k0 t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq 
C e (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c k0 t) (CHead 
e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))))))) (\lambda (b: B).(\lambda (H8: (eq nat (S n0) (s (Bind b) 
x2))).(\lambda (H9: (drop (r (Bind b) n0) O x1 e)).(let H10 \def (f_equal nat 
nat (\lambda (e0: nat).(match e0 in nat return (\lambda (_: nat).nat) with [O 
\Rightarrow n0 | (S n1) \Rightarrow n1])) (S n0) (S x2) H8) in (let H11 \def 
(eq_ind_r nat x2 (\lambda (n1: nat).(csubst0 n1 v c x1)) H6 n0 H10) in (let 
H12 \def (eq_ind_r nat x2 (\lambda (n1: nat).(subst0 n1 v t x0)) H5 n0 H10) 
in (let H13 \def (IHn c x1 v H11 e H9) in (or4_ind (drop n0 O c e) (ex3_4 F C 
T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop n0 O c (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop n0 O c (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop n0 O c (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (or4 (drop (S n0) O (CHead c (Bind b) t) e) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: 
T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) 
(CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda 
(H14: (drop n0 O c e)).(or4_intro0 (drop (S n0) O (CHead c (Bind b) t) e) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: 
T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) 
(CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (drop_drop 
(Bind b) n0 c e H14 t))) (\lambda (H14: (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat 
f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop n0 O c (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2))))))).(ex3_4_ind F C 
T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop n0 O c (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2))))) 
(or4 (drop (S n0) O (CHead c (Bind b) t) e) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat 
f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))))) (\lambda (x3: F).(\lambda (x4: C).(\lambda 
(x5: T).(\lambda (x6: T).(\lambda (H15: (eq C e (CHead x4 (Flat x3) 
x6))).(\lambda (H16: (drop n0 O c (CHead x4 (Flat x3) x5))).(\lambda (H17: 
(subst0 O v x5 x6)).(eq_ind_r C (CHead x4 (Flat x3) x6) (\lambda (c0: C).(or4 
(drop (S n0) O (CHead c (Bind b) t) c0) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 (CHead e0 (Flat 
f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C c0 (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C c0 (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))) (or4_intro1 (drop (S n0) O (CHead c (Bind 
b) t) (CHead x4 (Flat x3) x6)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x4 (Flat x3) x6) (CHead e0 
(Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v 
u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C (CHead x4 (Flat x3) x6) (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) 
O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C (CHead x4 (Flat x3) x6) (CHead e2 (Flat f) 
u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) 
(ex3_4_intro F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C (CHead x4 (Flat x3) x6) (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2))))) 
x3 x4 x5 x6 (refl_equal C (CHead x4 (Flat x3) x6)) (drop_drop (Bind b) n0 c 
(CHead x4 (Flat x3) x5) H16 t) H17)) e H15)))))))) H14)) (\lambda (H14: 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop n0 O c (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2))))))).(ex3_4_ind F C C T (\lambda (f: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop n0 O c (CHead e1 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2))))) (or4 (drop (S n0) O (CHead c (Bind b) t) e) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: 
T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) 
(CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda 
(x3: F).(\lambda (x4: C).(\lambda (x5: C).(\lambda (x6: T).(\lambda (H15: (eq 
C e (CHead x5 (Flat x3) x6))).(\lambda (H16: (drop n0 O c (CHead x4 (Flat x3) 
x6))).(\lambda (H17: (csubst0 O v x4 x5)).(eq_ind_r C (CHead x5 (Flat x3) x6) 
(\lambda (c0: C).(or4 (drop (S n0) O (CHead c (Bind b) t) c0) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) 
u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C c0 (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) 
O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C c0 (CHead e2 (Flat f) u2))))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u1))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))))) (or4_intro2 (drop (S n0) O 
(CHead c (Bind b) t) (CHead x5 (Flat x3) x6)) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x5 (Flat 
x3) x6) (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda 
(u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat 
f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C (CHead x5 (Flat x3) x6) (CHead e2 
(Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x5 (Flat x3) x6) (CHead e2 
(Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat 
f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) 
(ex3_4_intro F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C (CHead x5 (Flat x3) x6) (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) 
O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))) x3 x4 x5 x6 
(refl_equal C (CHead x5 (Flat x3) x6)) (drop_drop (Bind b) n0 c (CHead x4 
(Flat x3) x6) H16 t) H17)) e H15)))))))) H14)) (\lambda (H14: (ex4_5 F C C T 
T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop n0 O c (CHead e1 
(Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))).(ex4_5_ind F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop n0 O c (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (or4 (drop (S n0) O (CHead c (Bind b) t) e) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: 
T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) 
(CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda 
(x3: F).(\lambda (x4: C).(\lambda (x5: C).(\lambda (x6: T).(\lambda (x7: 
T).(\lambda (H15: (eq C e (CHead x5 (Flat x3) x7))).(\lambda (H16: (drop n0 O 
c (CHead x4 (Flat x3) x6))).(\lambda (H17: (subst0 O v x6 x7)).(\lambda (H18: 
(csubst0 O v x4 x5)).(eq_ind_r C (CHead x5 (Flat x3) x7) (\lambda (c0: 
C).(or4 (drop (S n0) O (CHead c (Bind b) t) c0) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 (CHead e0 (Flat 
f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C c0 (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C c0 (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))) (or4_intro3 (drop (S n0) O (CHead c (Bind 
b) t) (CHead x5 (Flat x3) x7)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x5 (Flat x3) x7) (CHead e0 
(Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v 
u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C (CHead x5 (Flat x3) x7) (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) 
O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C (CHead x5 (Flat x3) x7) (CHead e2 (Flat f) 
u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) 
(ex4_5_intro F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x5 (Flat x3) x7) (CHead e2 
(Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat 
f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
x3 x4 x5 x6 x7 (refl_equal C (CHead x5 (Flat x3) x7)) (drop_drop (Bind b) n0 
c (CHead x4 (Flat x3) x6) H16 t) H17 H18)) e H15)))))))))) H14)) H13)))))))) 
(\lambda (f: F).(\lambda (H8: (eq nat (S n0) (s (Flat f) x2))).(\lambda (H9: 
(drop (r (Flat f) n0) O x1 e)).(let H10 \def (f_equal nat nat (\lambda (e0: 
nat).e0) (S n0) x2 H8) in (let H11 \def (eq_ind_r nat x2 (\lambda (n1: 
nat).(csubst0 n1 v c x1)) H6 (S n0) H10) in (let H12 \def (eq_ind_r nat x2 
(\lambda (n1: nat).(subst0 n1 v t x0)) H5 (S n0) H10) in (let H13 \def (H x1 
v H11 e H9) in (or4_ind (drop (S n0) O c e) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat 
f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O c (CHead e0 (Flat f0) u1)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e 
(CHead e2 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop (S n0) O c (CHead e1 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f0) u2))))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O c (CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (or4 (drop (S n0) O (CHead c (Flat f) t) e) 
(ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e0 (Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) 
(CHead e0 (Flat f0) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f0) u2))))))) 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda 
(H14: (drop (S n0) O c e)).(or4_intro0 (drop (S n0) O (CHead c (Flat f) t) e) 
(ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e0 (Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) 
(CHead e0 (Flat f0) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f0) u2))))))) 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (drop_drop 
(Flat f) n0 c e H14 t))) (\lambda (H14: (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat 
f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O c (CHead e0 (Flat f0) u1)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2))))))).(ex3_4_ind F C 
T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C 
e (CHead e0 (Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda 
(u1: T).(\lambda (_: T).(drop (S n0) O c (CHead e0 (Flat f0) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v 
u1 u2))))) (or4 (drop (S n0) O (CHead c (Flat f) t) e) (ex3_4 F C T T 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e0 (Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) 
u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S 
n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f0) u2))))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u1))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda (x3: F).(\lambda 
(x4: C).(\lambda (x5: T).(\lambda (x6: T).(\lambda (H15: (eq C e (CHead x4 
(Flat x3) x6))).(\lambda (H16: (drop (S n0) O c (CHead x4 (Flat x3) 
x5))).(\lambda (H17: (subst0 O v x5 x6)).(eq_ind_r C (CHead x4 (Flat x3) x6) 
(\lambda (c0: C).(or4 (drop (S n0) O (CHead c (Flat f) t) c0) (ex3_4 F C T T 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 
(CHead e0 (Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) 
u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C c0 (CHead e2 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S 
n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C c0 (CHead e2 (Flat f0) u2))))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u1))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))))) (or4_intro1 (drop (S n0) O 
(CHead c (Flat f) t) (CHead x4 (Flat x3) x6)) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x4 (Flat 
x3) x6) (CHead e0 (Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) 
(CHead e0 (Flat f0) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C (CHead x4 (Flat x3) 
x6) (CHead e2 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat 
f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x4 (Flat 
x3) x6) (CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Flat f) t) (CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (ex3_4_intro F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x4 (Flat 
x3) x6) (CHead e0 (Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) 
(CHead e0 (Flat f0) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2))))) x3 x4 x5 x6 (refl_equal C (CHead 
x4 (Flat x3) x6)) (drop_drop (Flat f) n0 c (CHead x4 (Flat x3) x5) H16 t) 
H17)) e H15)))))))) H14)) (\lambda (H14: (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O c (CHead e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))))).(ex3_4_ind F C 
C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e 
(CHead e2 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop (S n0) O c (CHead e1 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))) 
(or4 (drop (S n0) O (CHead c (Flat f) t) e) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat 
f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) u1)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C e (CHead e2 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c 
(Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Flat f) t) (CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))))) (\lambda (x3: F).(\lambda (x4: C).(\lambda 
(x5: C).(\lambda (x6: T).(\lambda (H15: (eq C e (CHead x5 (Flat x3) 
x6))).(\lambda (H16: (drop (S n0) O c (CHead x4 (Flat x3) x6))).(\lambda 
(H17: (csubst0 O v x4 x5)).(eq_ind_r C (CHead x5 (Flat x3) x6) (\lambda (c0: 
C).(or4 (drop (S n0) O (CHead c (Flat f) t) c0) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 (CHead e0 (Flat 
f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) u1)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C c0 (CHead e2 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c 
(Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C c0 (CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Flat f) t) (CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))) (or4_intro2 (drop (S n0) O (CHead c (Flat 
f) t) (CHead x5 (Flat x3) x6)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x5 (Flat x3) x6) (CHead e0 
(Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) 
u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C (CHead x5 (Flat x3) x6) (CHead e2 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x5 (Flat x3) x6) (CHead e2 
(Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) 
(CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))) (ex3_4_intro F C C T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C (CHead x5 (Flat x3) x6) (CHead e2 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2))))) x3 x4 x5 x6 (refl_equal C (CHead x5 (Flat x3) x6)) (drop_drop 
(Flat f) n0 c (CHead x4 (Flat x3) x6) H16 t) H17)) e H15)))))))) H14)) 
(\lambda (H14: (ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f0) 
u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O c (CHead e1 (Flat f0) u1))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))).(ex4_5_ind F C 
C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f0) u2))))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O c (CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (or4 (drop (S n0) O (CHead c (Flat f) t) e) 
(ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e0 (Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) 
(CHead e0 (Flat f0) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 
e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f0) u2))))))) 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda 
(x3: F).(\lambda (x4: C).(\lambda (x5: C).(\lambda (x6: T).(\lambda (x7: 
T).(\lambda (H15: (eq C e (CHead x5 (Flat x3) x7))).(\lambda (H16: (drop (S 
n0) O c (CHead x4 (Flat x3) x6))).(\lambda (H17: (subst0 O v x6 x7)).(\lambda 
(H18: (csubst0 O v x4 x5)).(eq_ind_r C (CHead x5 (Flat x3) x7) (\lambda (c0: 
C).(or4 (drop (S n0) O (CHead c (Flat f) t) c0) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 (CHead e0 (Flat 
f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) u1)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C c0 (CHead e2 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c 
(Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C c0 (CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Flat f) t) (CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))) (or4_intro3 (drop (S n0) O (CHead c (Flat 
f) t) (CHead x5 (Flat x3) x7)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x5 (Flat x3) x7) (CHead e0 
(Flat f0) u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) 
u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C (CHead x5 (Flat x3) x7) (CHead e2 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x5 (Flat x3) x7) (CHead e2 
(Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) 
(CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))) (ex4_5_intro F C C T T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x5 (Flat 
x3) x7) (CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Flat f) t) (CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) x3 x4 x5 x6 x7 (refl_equal C (CHead x5 (Flat 
x3) x7)) (drop_drop (Flat f) n0 c (CHead x4 (Flat x3) x6) H16 t) H17 H18)) e 
H15)))))))))) H14)) H13)))))))) k H3 (drop_gen_drop k x1 e x0 n0 H7)))))))))) 
H2)) (csubst0_gen_head k c c2 t v (S n0) H0))))))))))) c1)))) n).
(* COMMENTS
Initial nodes: 34765
END *)

theorem csubst0_drop_lt_back:
 \forall (n: nat).(\forall (i: nat).((lt n i) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (e2: C).((drop n O 
c2 e2) \to (or (drop n O c1 e2) (ex2 C (\lambda (e1: C).(csubst0 (minus i n) 
v e1 e2)) (\lambda (e1: C).(drop n O c1 e1))))))))))))
\def
 \lambda (n: nat).(nat_ind (\lambda (n0: nat).(\forall (i: nat).((lt n0 i) 
\to (\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 c2) 
\to (\forall (e2: C).((drop n0 O c2 e2) \to (or (drop n0 O c1 e2) (ex2 C 
(\lambda (e1: C).(csubst0 (minus i n0) v e1 e2)) (\lambda (e1: C).(drop n0 O 
c1 e1))))))))))))) (\lambda (i: nat).(\lambda (_: (lt O i)).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (v: T).(\lambda (H0: (csubst0 i v c1 
c2)).(\lambda (e2: C).(\lambda (H1: (drop O O c2 e2)).(eq_ind C c2 (\lambda 
(c: C).(or (drop O O c1 c) (ex2 C (\lambda (e1: C).(csubst0 (minus i O) v e1 
c)) (\lambda (e1: C).(drop O O c1 e1))))) (eq_ind nat i (\lambda (n0: 
nat).(or (drop O O c1 c2) (ex2 C (\lambda (e1: C).(csubst0 n0 v e1 c2)) 
(\lambda (e1: C).(drop O O c1 e1))))) (or_intror (drop O O c1 c2) (ex2 C 
(\lambda (e1: C).(csubst0 i v e1 c2)) (\lambda (e1: C).(drop O O c1 e1))) 
(ex_intro2 C (\lambda (e1: C).(csubst0 i v e1 c2)) (\lambda (e1: C).(drop O O 
c1 e1)) c1 H0 (drop_refl c1))) (minus i O) (minus_n_O i)) e2 (drop_gen_refl 
c2 e2 H1)))))))))) (\lambda (n0: nat).(\lambda (IHn: ((\forall (i: nat).((lt 
n0 i) \to (\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 
c2) \to (\forall (e2: C).((drop n0 O c2 e2) \to (or (drop n0 O c1 e2) (ex2 C 
(\lambda (e1: C).(csubst0 (minus i n0) v e1 e2)) (\lambda (e1: C).(drop n0 O 
c1 e1)))))))))))))).(\lambda (i: nat).(\lambda (H: (lt (S n0) i)).(\lambda 
(c1: C).(C_ind (\lambda (c: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v 
c c2) \to (\forall (e2: C).((drop (S n0) O c2 e2) \to (or (drop (S n0) O c 
e2) (ex2 C (\lambda (e1: C).(csubst0 (minus i (S n0)) v e1 e2)) (\lambda (e1: 
C).(drop (S n0) O c e1)))))))))) (\lambda (n1: nat).(\lambda (c2: C).(\lambda 
(v: T).(\lambda (H0: (csubst0 i v (CSort n1) c2)).(\lambda (e2: C).(\lambda 
(_: (drop (S n0) O c2 e2)).(csubst0_gen_sort c2 v i n1 H0 (or (drop (S n0) O 
(CSort n1) e2) (ex2 C (\lambda (e1: C).(csubst0 (minus i (S n0)) v e1 e2)) 
(\lambda (e1: C).(drop (S n0) O (CSort n1) e1))))))))))) (\lambda (c: 
C).(\lambda (H0: ((\forall (c2: C).(\forall (v: T).((csubst0 i v c c2) \to 
(\forall (e2: C).((drop (S n0) O c2 e2) \to (or (drop (S n0) O c e2) (ex2 C 
(\lambda (e1: C).(csubst0 (minus i (S n0)) v e1 e2)) (\lambda (e1: C).(drop 
(S n0) O c e1))))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c2: 
C).(\lambda (v: T).(\lambda (H1: (csubst0 i v (CHead c k t) c2)).(\lambda 
(e2: C).(\lambda (H2: (drop (S n0) O c2 e2)).(or3_ind (ex3_2 T nat (\lambda 
(_: T).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (u2: T).(\lambda (_: 
nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j 
v t u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat i (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c c3)))) (ex4_3 T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat i (s k j))))) (\lambda (u2: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3))))) (or (drop (S n0) 
O (CHead c k t) e2) (ex2 C (\lambda (e1: C).(csubst0 (minus i (S n0)) v e1 
e2)) (\lambda (e1: C).(drop (S n0) O (CHead c k t) e1)))) (\lambda (H3: 
(ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda 
(u2: T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: 
T).(\lambda (j: nat).(subst0 j v t u2))))).(ex3_2_ind T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (u2: T).(\lambda (_: 
nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j 
v t u2))) (or (drop (S n0) O (CHead c k t) e2) (ex2 C (\lambda (e1: 
C).(csubst0 (minus i (S n0)) v e1 e2)) (\lambda (e1: C).(drop (S n0) O (CHead 
c k t) e1)))) (\lambda (x0: T).(\lambda (x1: nat).(\lambda (H4: (eq nat i (s 
k x1))).(\lambda (H5: (eq C c2 (CHead c k x0))).(\lambda (_: (subst0 x1 v t 
x0)).(let H7 \def (eq_ind C c2 (\lambda (c0: C).(drop (S n0) O c0 e2)) H2 
(CHead c k x0) H5) in (let H8 \def (eq_ind nat i (\lambda (n1: nat).(\forall 
(c3: C).(\forall (v0: T).((csubst0 n1 v0 c c3) \to (\forall (e3: C).((drop (S 
n0) O c3 e3) \to (or (drop (S n0) O c e3) (ex2 C (\lambda (e1: C).(csubst0 
(minus n1 (S n0)) v0 e1 e3)) (\lambda (e1: C).(drop (S n0) O c e1)))))))))) 
H0 (s k x1) H4) in (let H9 \def (eq_ind nat i (\lambda (n1: nat).(lt (S n0) 
n1)) H (s k x1) H4) in (eq_ind_r nat (s k x1) (\lambda (n1: nat).(or (drop (S 
n0) O (CHead c k t) e2) (ex2 C (\lambda (e1: C).(csubst0 (minus n1 (S n0)) v 
e1 e2)) (\lambda (e1: C).(drop (S n0) O (CHead c k t) e1))))) (K_ind (\lambda 
(k0: K).(((\forall (c3: C).(\forall (v0: T).((csubst0 (s k0 x1) v0 c c3) \to 
(\forall (e3: C).((drop (S n0) O c3 e3) \to (or (drop (S n0) O c e3) (ex2 C 
(\lambda (e1: C).(csubst0 (minus (s k0 x1) (S n0)) v0 e1 e3)) (\lambda (e1: 
C).(drop (S n0) O c e1)))))))))) \to ((lt (S n0) (s k0 x1)) \to ((drop (r k0 
n0) O c e2) \to (or (drop (S n0) O (CHead c k0 t) e2) (ex2 C (\lambda (e1: 
C).(csubst0 (minus (s k0 x1) (S n0)) v e1 e2)) (\lambda (e1: C).(drop (S n0) 
O (CHead c k0 t) e1)))))))) (\lambda (b: B).(\lambda (_: ((\forall (c3: 
C).(\forall (v0: T).((csubst0 (s (Bind b) x1) v0 c c3) \to (\forall (e3: 
C).((drop (S n0) O c3 e3) \to (or (drop (S n0) O c e3) (ex2 C (\lambda (e1: 
C).(csubst0 (minus (s (Bind b) x1) (S n0)) v0 e1 e3)) (\lambda (e1: C).(drop 
(S n0) O c e1))))))))))).(\lambda (_: (lt (S n0) (s (Bind b) x1))).(\lambda 
(H12: (drop (r (Bind b) n0) O c e2)).(or_introl (drop (S n0) O (CHead c (Bind 
b) t) e2) (ex2 C (\lambda (e1: C).(csubst0 (minus x1 n0) v e1 e2)) (\lambda 
(e1: C).(drop (S n0) O (CHead c (Bind b) t) e1))) (drop_drop (Bind b) n0 c e2 
H12 t)))))) (\lambda (f: F).(\lambda (_: ((\forall (c3: C).(\forall (v0: 
T).((csubst0 (s (Flat f) x1) v0 c c3) \to (\forall (e3: C).((drop (S n0) O c3 
e3) \to (or (drop (S n0) O c e3) (ex2 C (\lambda (e1: C).(csubst0 (minus (s 
(Flat f) x1) (S n0)) v0 e1 e3)) (\lambda (e1: C).(drop (S n0) O c 
e1))))))))))).(\lambda (_: (lt (S n0) (s (Flat f) x1))).(\lambda (H12: (drop 
(r (Flat f) n0) O c e2)).(or_introl (drop (S n0) O (CHead c (Flat f) t) e2) 
(ex2 C (\lambda (e1: C).(csubst0 (minus x1 (S n0)) v e1 e2)) (\lambda (e1: 
C).(drop (S n0) O (CHead c (Flat f) t) e1))) (drop_drop (Flat f) n0 c e2 H12 
t)))))) k H8 H9 (drop_gen_drop k c e2 x0 n0 H7)) i H4))))))))) H3)) (\lambda 
(H3: (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq nat i (s k j)))) 
(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c c3))))).(ex3_2_ind C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j 
v c c3))) (or (drop (S n0) O (CHead c k t) e2) (ex2 C (\lambda (e1: 
C).(csubst0 (minus i (S n0)) v e1 e2)) (\lambda (e1: C).(drop (S n0) O (CHead 
c k t) e1)))) (\lambda (x0: C).(\lambda (x1: nat).(\lambda (H4: (eq nat i (s 
k x1))).(\lambda (H5: (eq C c2 (CHead x0 k t))).(\lambda (H6: (csubst0 x1 v c 
x0)).(let H7 \def (eq_ind C c2 (\lambda (c0: C).(drop (S n0) O c0 e2)) H2 
(CHead x0 k t) H5) in (let H8 \def (eq_ind nat i (\lambda (n1: nat).(\forall 
(c3: C).(\forall (v0: T).((csubst0 n1 v0 c c3) \to (\forall (e3: C).((drop (S 
n0) O c3 e3) \to (or (drop (S n0) O c e3) (ex2 C (\lambda (e1: C).(csubst0 
(minus n1 (S n0)) v0 e1 e3)) (\lambda (e1: C).(drop (S n0) O c e1)))))))))) 
H0 (s k x1) H4) in (let H9 \def (eq_ind nat i (\lambda (n1: nat).(lt (S n0) 
n1)) H (s k x1) H4) in (eq_ind_r nat (s k x1) (\lambda (n1: nat).(or (drop (S 
n0) O (CHead c k t) e2) (ex2 C (\lambda (e1: C).(csubst0 (minus n1 (S n0)) v 
e1 e2)) (\lambda (e1: C).(drop (S n0) O (CHead c k t) e1))))) (K_ind (\lambda 
(k0: K).(((\forall (c3: C).(\forall (v0: T).((csubst0 (s k0 x1) v0 c c3) \to 
(\forall (e3: C).((drop (S n0) O c3 e3) \to (or (drop (S n0) O c e3) (ex2 C 
(\lambda (e1: C).(csubst0 (minus (s k0 x1) (S n0)) v0 e1 e3)) (\lambda (e1: 
C).(drop (S n0) O c e1)))))))))) \to ((lt (S n0) (s k0 x1)) \to ((drop (r k0 
n0) O x0 e2) \to (or (drop (S n0) O (CHead c k0 t) e2) (ex2 C (\lambda (e1: 
C).(csubst0 (minus (s k0 x1) (S n0)) v e1 e2)) (\lambda (e1: C).(drop (S n0) 
O (CHead c k0 t) e1)))))))) (\lambda (b: B).(\lambda (_: ((\forall (c3: 
C).(\forall (v0: T).((csubst0 (s (Bind b) x1) v0 c c3) \to (\forall (e3: 
C).((drop (S n0) O c3 e3) \to (or (drop (S n0) O c e3) (ex2 C (\lambda (e1: 
C).(csubst0 (minus (s (Bind b) x1) (S n0)) v0 e1 e3)) (\lambda (e1: C).(drop 
(S n0) O c e1))))))))))).(\lambda (H11: (lt (S n0) (s (Bind b) x1))).(\lambda 
(H12: (drop (r (Bind b) n0) O x0 e2)).(let H_x \def (IHn x1 (lt_S_n n0 x1 
H11) c x0 v H6 e2 H12) in (let H13 \def H_x in (or_ind (drop n0 O c e2) (ex2 
C (\lambda (e1: C).(csubst0 (minus x1 n0) v e1 e2)) (\lambda (e1: C).(drop n0 
O c e1))) (or (drop (S n0) O (CHead c (Bind b) t) e2) (ex2 C (\lambda (e1: 
C).(csubst0 (minus x1 n0) v e1 e2)) (\lambda (e1: C).(drop (S n0) O (CHead c 
(Bind b) t) e1)))) (\lambda (H14: (drop n0 O c e2)).(or_introl (drop (S n0) O 
(CHead c (Bind b) t) e2) (ex2 C (\lambda (e1: C).(csubst0 (minus x1 n0) v e1 
e2)) (\lambda (e1: C).(drop (S n0) O (CHead c (Bind b) t) e1))) (drop_drop 
(Bind b) n0 c e2 H14 t))) (\lambda (H14: (ex2 C (\lambda (e1: C).(csubst0 
(minus x1 n0) v e1 e2)) (\lambda (e1: C).(drop n0 O c e1)))).(ex2_ind C 
(\lambda (e1: C).(csubst0 (minus x1 n0) v e1 e2)) (\lambda (e1: C).(drop n0 O 
c e1)) (or (drop (S n0) O (CHead c (Bind b) t) e2) (ex2 C (\lambda (e1: 
C).(csubst0 (minus x1 n0) v e1 e2)) (\lambda (e1: C).(drop (S n0) O (CHead c 
(Bind b) t) e1)))) (\lambda (x: C).(\lambda (H15: (csubst0 (minus x1 n0) v x 
e2)).(\lambda (H16: (drop n0 O c x)).(or_intror (drop (S n0) O (CHead c (Bind 
b) t) e2) (ex2 C (\lambda (e1: C).(csubst0 (minus x1 n0) v e1 e2)) (\lambda 
(e1: C).(drop (S n0) O (CHead c (Bind b) t) e1))) (ex_intro2 C (\lambda (e1: 
C).(csubst0 (minus x1 n0) v e1 e2)) (\lambda (e1: C).(drop (S n0) O (CHead c 
(Bind b) t) e1)) x H15 (drop_drop (Bind b) n0 c x H16 t)))))) H14)) 
H13))))))) (\lambda (f: F).(\lambda (H10: ((\forall (c3: C).(\forall (v0: 
T).((csubst0 (s (Flat f) x1) v0 c c3) \to (\forall (e3: C).((drop (S n0) O c3 
e3) \to (or (drop (S n0) O c e3) (ex2 C (\lambda (e1: C).(csubst0 (minus (s 
(Flat f) x1) (S n0)) v0 e1 e3)) (\lambda (e1: C).(drop (S n0) O c 
e1))))))))))).(\lambda (_: (lt (S n0) (s (Flat f) x1))).(\lambda (H12: (drop 
(r (Flat f) n0) O x0 e2)).(let H_x \def (H10 x0 v H6 e2 H12) in (let H13 \def 
H_x in (or_ind (drop (S n0) O c e2) (ex2 C (\lambda (e1: C).(csubst0 (minus 
x1 (S n0)) v e1 e2)) (\lambda (e1: C).(drop (S n0) O c e1))) (or (drop (S n0) 
O (CHead c (Flat f) t) e2) (ex2 C (\lambda (e1: C).(csubst0 (minus x1 (S n0)) 
v e1 e2)) (\lambda (e1: C).(drop (S n0) O (CHead c (Flat f) t) e1)))) 
(\lambda (H14: (drop (S n0) O c e2)).(or_introl (drop (S n0) O (CHead c (Flat 
f) t) e2) (ex2 C (\lambda (e1: C).(csubst0 (minus x1 (S n0)) v e1 e2)) 
(\lambda (e1: C).(drop (S n0) O (CHead c (Flat f) t) e1))) (drop_drop (Flat 
f) n0 c e2 H14 t))) (\lambda (H14: (ex2 C (\lambda (e1: C).(csubst0 (minus x1 
(S n0)) v e1 e2)) (\lambda (e1: C).(drop (S n0) O c e1)))).(ex2_ind C 
(\lambda (e1: C).(csubst0 (minus x1 (S n0)) v e1 e2)) (\lambda (e1: C).(drop 
(S n0) O c e1)) (or (drop (S n0) O (CHead c (Flat f) t) e2) (ex2 C (\lambda 
(e1: C).(csubst0 (minus x1 (S n0)) v e1 e2)) (\lambda (e1: C).(drop (S n0) O 
(CHead c (Flat f) t) e1)))) (\lambda (x: C).(\lambda (H15: (csubst0 (minus x1 
(S n0)) v x e2)).(\lambda (H16: (drop (S n0) O c x)).(or_intror (drop (S n0) 
O (CHead c (Flat f) t) e2) (ex2 C (\lambda (e1: C).(csubst0 (minus x1 (S n0)) 
v e1 e2)) (\lambda (e1: C).(drop (S n0) O (CHead c (Flat f) t) e1))) 
(ex_intro2 C (\lambda (e1: C).(csubst0 (minus x1 (S n0)) v e1 e2)) (\lambda 
(e1: C).(drop (S n0) O (CHead c (Flat f) t) e1)) x H15 (drop_drop (Flat f) n0 
c x H16 t)))))) H14)) H13))))))) k H8 H9 (drop_gen_drop k x0 e2 t n0 H7)) i 
H4))))))))) H3)) (\lambda (H3: (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat i (s k j))))) (\lambda (u2: T).(\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda 
(_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: 
C).(\lambda (j: nat).(csubst0 j v c c3)))))).(ex4_3_ind T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat i (s k j))))) (\lambda (u2: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3)))) (or (drop (S n0) 
O (CHead c k t) e2) (ex2 C (\lambda (e1: C).(csubst0 (minus i (S n0)) v e1 
e2)) (\lambda (e1: C).(drop (S n0) O (CHead c k t) e1)))) (\lambda (x0: 
T).(\lambda (x1: C).(\lambda (x2: nat).(\lambda (H4: (eq nat i (s k 
x2))).(\lambda (H5: (eq C c2 (CHead x1 k x0))).(\lambda (_: (subst0 x2 v t 
x0)).(\lambda (H7: (csubst0 x2 v c x1)).(let H8 \def (eq_ind C c2 (\lambda 
(c0: C).(drop (S n0) O c0 e2)) H2 (CHead x1 k x0) H5) in (let H9 \def (eq_ind 
nat i (\lambda (n1: nat).(\forall (c3: C).(\forall (v0: T).((csubst0 n1 v0 c 
c3) \to (\forall (e3: C).((drop (S n0) O c3 e3) \to (or (drop (S n0) O c e3) 
(ex2 C (\lambda (e1: C).(csubst0 (minus n1 (S n0)) v0 e1 e3)) (\lambda (e1: 
C).(drop (S n0) O c e1)))))))))) H0 (s k x2) H4) in (let H10 \def (eq_ind nat 
i (\lambda (n1: nat).(lt (S n0) n1)) H (s k x2) H4) in (eq_ind_r nat (s k x2) 
(\lambda (n1: nat).(or (drop (S n0) O (CHead c k t) e2) (ex2 C (\lambda (e1: 
C).(csubst0 (minus n1 (S n0)) v e1 e2)) (\lambda (e1: C).(drop (S n0) O 
(CHead c k t) e1))))) (K_ind (\lambda (k0: K).(((\forall (c3: C).(\forall 
(v0: T).((csubst0 (s k0 x2) v0 c c3) \to (\forall (e3: C).((drop (S n0) O c3 
e3) \to (or (drop (S n0) O c e3) (ex2 C (\lambda (e1: C).(csubst0 (minus (s 
k0 x2) (S n0)) v0 e1 e3)) (\lambda (e1: C).(drop (S n0) O c e1)))))))))) \to 
((lt (S n0) (s k0 x2)) \to ((drop (r k0 n0) O x1 e2) \to (or (drop (S n0) O 
(CHead c k0 t) e2) (ex2 C (\lambda (e1: C).(csubst0 (minus (s k0 x2) (S n0)) 
v e1 e2)) (\lambda (e1: C).(drop (S n0) O (CHead c k0 t) e1)))))))) (\lambda 
(b: B).(\lambda (_: ((\forall (c3: C).(\forall (v0: T).((csubst0 (s (Bind b) 
x2) v0 c c3) \to (\forall (e3: C).((drop (S n0) O c3 e3) \to (or (drop (S n0) 
O c e3) (ex2 C (\lambda (e1: C).(csubst0 (minus (s (Bind b) x2) (S n0)) v0 e1 
e3)) (\lambda (e1: C).(drop (S n0) O c e1))))))))))).(\lambda (H12: (lt (S 
n0) (s (Bind b) x2))).(\lambda (H13: (drop (r (Bind b) n0) O x1 e2)).(let H_x 
\def (IHn x2 (lt_S_n n0 x2 H12) c x1 v H7 e2 H13) in (let H14 \def H_x in 
(or_ind (drop n0 O c e2) (ex2 C (\lambda (e1: C).(csubst0 (minus x2 n0) v e1 
e2)) (\lambda (e1: C).(drop n0 O c e1))) (or (drop (S n0) O (CHead c (Bind b) 
t) e2) (ex2 C (\lambda (e1: C).(csubst0 (minus x2 n0) v e1 e2)) (\lambda (e1: 
C).(drop (S n0) O (CHead c (Bind b) t) e1)))) (\lambda (H15: (drop n0 O c 
e2)).(or_introl (drop (S n0) O (CHead c (Bind b) t) e2) (ex2 C (\lambda (e1: 
C).(csubst0 (minus x2 n0) v e1 e2)) (\lambda (e1: C).(drop (S n0) O (CHead c 
(Bind b) t) e1))) (drop_drop (Bind b) n0 c e2 H15 t))) (\lambda (H15: (ex2 C 
(\lambda (e1: C).(csubst0 (minus x2 n0) v e1 e2)) (\lambda (e1: C).(drop n0 O 
c e1)))).(ex2_ind C (\lambda (e1: C).(csubst0 (minus x2 n0) v e1 e2)) 
(\lambda (e1: C).(drop n0 O c e1)) (or (drop (S n0) O (CHead c (Bind b) t) 
e2) (ex2 C (\lambda (e1: C).(csubst0 (minus x2 n0) v e1 e2)) (\lambda (e1: 
C).(drop (S n0) O (CHead c (Bind b) t) e1)))) (\lambda (x: C).(\lambda (H16: 
(csubst0 (minus x2 n0) v x e2)).(\lambda (H17: (drop n0 O c x)).(or_intror 
(drop (S n0) O (CHead c (Bind b) t) e2) (ex2 C (\lambda (e1: C).(csubst0 
(minus x2 n0) v e1 e2)) (\lambda (e1: C).(drop (S n0) O (CHead c (Bind b) t) 
e1))) (ex_intro2 C (\lambda (e1: C).(csubst0 (minus x2 n0) v e1 e2)) (\lambda 
(e1: C).(drop (S n0) O (CHead c (Bind b) t) e1)) x H16 (drop_drop (Bind b) n0 
c x H17 t)))))) H15)) H14))))))) (\lambda (f: F).(\lambda (H11: ((\forall 
(c3: C).(\forall (v0: T).((csubst0 (s (Flat f) x2) v0 c c3) \to (\forall (e3: 
C).((drop (S n0) O c3 e3) \to (or (drop (S n0) O c e3) (ex2 C (\lambda (e1: 
C).(csubst0 (minus (s (Flat f) x2) (S n0)) v0 e1 e3)) (\lambda (e1: C).(drop 
(S n0) O c e1))))))))))).(\lambda (_: (lt (S n0) (s (Flat f) x2))).(\lambda 
(H13: (drop (r (Flat f) n0) O x1 e2)).(let H_x \def (H11 x1 v H7 e2 H13) in 
(let H14 \def H_x in (or_ind (drop (S n0) O c e2) (ex2 C (\lambda (e1: 
C).(csubst0 (minus x2 (S n0)) v e1 e2)) (\lambda (e1: C).(drop (S n0) O c 
e1))) (or (drop (S n0) O (CHead c (Flat f) t) e2) (ex2 C (\lambda (e1: 
C).(csubst0 (minus x2 (S n0)) v e1 e2)) (\lambda (e1: C).(drop (S n0) O 
(CHead c (Flat f) t) e1)))) (\lambda (H15: (drop (S n0) O c e2)).(or_introl 
(drop (S n0) O (CHead c (Flat f) t) e2) (ex2 C (\lambda (e1: C).(csubst0 
(minus x2 (S n0)) v e1 e2)) (\lambda (e1: C).(drop (S n0) O (CHead c (Flat f) 
t) e1))) (drop_drop (Flat f) n0 c e2 H15 t))) (\lambda (H15: (ex2 C (\lambda 
(e1: C).(csubst0 (minus x2 (S n0)) v e1 e2)) (\lambda (e1: C).(drop (S n0) O 
c e1)))).(ex2_ind C (\lambda (e1: C).(csubst0 (minus x2 (S n0)) v e1 e2)) 
(\lambda (e1: C).(drop (S n0) O c e1)) (or (drop (S n0) O (CHead c (Flat f) 
t) e2) (ex2 C (\lambda (e1: C).(csubst0 (minus x2 (S n0)) v e1 e2)) (\lambda 
(e1: C).(drop (S n0) O (CHead c (Flat f) t) e1)))) (\lambda (x: C).(\lambda 
(H16: (csubst0 (minus x2 (S n0)) v x e2)).(\lambda (H17: (drop (S n0) O c 
x)).(or_intror (drop (S n0) O (CHead c (Flat f) t) e2) (ex2 C (\lambda (e1: 
C).(csubst0 (minus x2 (S n0)) v e1 e2)) (\lambda (e1: C).(drop (S n0) O 
(CHead c (Flat f) t) e1))) (ex_intro2 C (\lambda (e1: C).(csubst0 (minus x2 
(S n0)) v e1 e2)) (\lambda (e1: C).(drop (S n0) O (CHead c (Flat f) t) e1)) x 
H16 (drop_drop (Flat f) n0 c x H17 t)))))) H15)) H14))))))) k H9 H10 
(drop_gen_drop k x1 e2 x0 n0 H8)) i H4))))))))))) H3)) (csubst0_gen_head k c 
c2 t v i H1))))))))))) c1)))))) n).
(* COMMENTS
Initial nodes: 5939
END *)

