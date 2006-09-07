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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/LambdaDelta/csubst0/drop".

include "csubst0/fwd.ma".

include "drop/fwd.ma".

include "s/props.ma".

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
O c1 e)).(let H2 \def (match H in le return (\lambda (n: nat).(\lambda (_: 
(le ? n)).((eq nat n O) \to (drop O O c2 e)))) with [le_n \Rightarrow 
(\lambda (H2: (eq nat (S i) O)).(let H3 \def (eq_ind nat (S i) (\lambda (e0: 
nat).(match e0 in nat return (\lambda (_: nat).Prop) with [O \Rightarrow 
False | (S _) \Rightarrow True])) I O H2) in (False_ind (drop O O c2 e) H3))) 
| (le_S m H2) \Rightarrow (\lambda (H3: (eq nat (S m) O)).((let H4 \def 
(eq_ind nat (S m) (\lambda (e0: nat).(match e0 in nat return (\lambda (_: 
nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) I O H3) in 
(False_ind ((le (S i) m) \to (drop O O c2 e)) H4)) H2))]) in (H2 (refl_equal 
nat O))))))))))) (\lambda (n0: nat).(\lambda (H: ((\forall (i: nat).((lt i 
n0) \to (\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 
c2) \to (\forall (e: C).((drop n0 O c1 e) \to (drop n0 O c2 
e))))))))))).(\lambda (i: nat).(\lambda (H0: (lt i (S n0))).(\lambda (c1: 
C).(C_ind (\lambda (c: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c 
c2) \to (\forall (e: C).((drop (S n0) O c e) \to (drop (S n0) O c2 e))))))) 
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
H8 \def (eq_ind nat i (\lambda (n: nat).(\forall (c2: C).(\forall (v: 
T).((csubst0 n v c c2) \to (\forall (e: C).((drop (S n0) O c e) \to (drop (S 
n0) O c2 e))))))) H1 (s k x1) H5) in (let H9 \def (eq_ind nat i (\lambda (n: 
nat).(lt n (S n0))) H0 (s k x1) H5) in ((match k in K return (\lambda (k0: 
K).((drop (r k0 n0) O c e) \to (((\forall (c2: C).(\forall (v: T).((csubst0 
(s k0 x1) v c c2) \to (\forall (e: C).((drop (S n0) O c e) \to (drop (S n0) O 
c2 e))))))) \to ((lt (s k0 x1) (S n0)) \to (drop (S n0) O (CHead c k0 x0) 
e))))) with [(Bind b) \Rightarrow (\lambda (H10: (drop (r (Bind b) n0) O c 
e)).(\lambda (_: ((\forall (c2: C).(\forall (v: T).((csubst0 (s (Bind b) x1) 
v c c2) \to (\forall (e: C).((drop (S n0) O c e) \to (drop (S n0) O c2 
e)))))))).(\lambda (_: (lt (s (Bind b) x1) (S n0))).(drop_drop (Bind b) n0 c 
e H10 x0)))) | (Flat f) \Rightarrow (\lambda (H10: (drop (r (Flat f) n0) O c 
e)).(\lambda (_: ((\forall (c2: C).(\forall (v: T).((csubst0 (s (Flat f) x1) 
v c c2) \to (\forall (e: C).((drop (S n0) O c e) \to (drop (S n0) O c2 
e)))))))).(\lambda (H12: (lt (s (Flat f) x1) (S n0))).(or_ind (eq nat x1 O) 
(ex2 nat (\lambda (m: nat).(eq nat x1 (S m))) (\lambda (m: nat).(lt m n0))) 
(drop (S n0) O (CHead c (Flat f) x0) e) (\lambda (_: (eq nat x1 
O)).(drop_drop (Flat f) n0 c e H10 x0)) (\lambda (H13: (ex2 nat (\lambda (m: 
nat).(eq nat x1 (S m))) (\lambda (m: nat).(lt m n0)))).(ex2_ind nat (\lambda 
(m: nat).(eq nat x1 (S m))) (\lambda (m: nat).(lt m n0)) (drop (S n0) O 
(CHead c (Flat f) x0) e) (\lambda (x: nat).(\lambda (_: (eq nat x1 (S 
x))).(\lambda (_: (lt x n0)).(drop_drop (Flat f) n0 c e H10 x0)))) H13)) 
(lt_gen_xS x1 n0 H12)))))]) (drop_gen_drop k c e t n0 H3) H8 H9))) c2 
H6)))))) H4)) (\lambda (H4: (ex3_2 C nat (\lambda (_: C).(\lambda (j: 
nat).(eq nat i (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead 
c3 k t)))) (\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c 
c2))))).(ex3_2_ind C nat (\lambda (_: C).(\lambda (j: nat).(eq nat i (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c c3))) (drop (S n0) O c2 e) (\lambda 
(x0: C).(\lambda (x1: nat).(\lambda (H5: (eq nat i (s k x1))).(\lambda (H6: 
(eq C c2 (CHead x0 k t))).(\lambda (H7: (csubst0 x1 v c x0)).(eq_ind_r C 
(CHead x0 k t) (\lambda (c0: C).(drop (S n0) O c0 e)) (let H8 \def (eq_ind 
nat i (\lambda (n: nat).(\forall (c2: C).(\forall (v: T).((csubst0 n v c c2) 
\to (\forall (e: C).((drop (S n0) O c e) \to (drop (S n0) O c2 e))))))) H1 (s 
k x1) H5) in (let H9 \def (eq_ind nat i (\lambda (n: nat).(lt n (S n0))) H0 
(s k x1) H5) in ((match k in K return (\lambda (k0: K).((drop (r k0 n0) O c 
e) \to (((\forall (c2: C).(\forall (v: T).((csubst0 (s k0 x1) v c c2) \to 
(\forall (e: C).((drop (S n0) O c e) \to (drop (S n0) O c2 e))))))) \to ((lt 
(s k0 x1) (S n0)) \to (drop (S n0) O (CHead x0 k0 t) e))))) with [(Bind b) 
\Rightarrow (\lambda (H10: (drop (r (Bind b) n0) O c e)).(\lambda (_: 
((\forall (c2: C).(\forall (v: T).((csubst0 (s (Bind b) x1) v c c2) \to 
(\forall (e: C).((drop (S n0) O c e) \to (drop (S n0) O c2 e)))))))).(\lambda 
(H12: (lt (s (Bind b) x1) (S n0))).(drop_drop (Bind b) n0 x0 e (H x1 (lt_S_n 
x1 n0 H12) c x0 v H7 e H10) t)))) | (Flat f) \Rightarrow (\lambda (H10: (drop 
(r (Flat f) n0) O c e)).(\lambda (H11: ((\forall (c2: C).(\forall (v: 
T).((csubst0 (s (Flat f) x1) v c c2) \to (\forall (e: C).((drop (S n0) O c e) 
\to (drop (S n0) O c2 e)))))))).(\lambda (H12: (lt (s (Flat f) x1) (S 
n0))).(or_ind (eq nat x1 O) (ex2 nat (\lambda (m: nat).(eq nat x1 (S m))) 
(\lambda (m: nat).(lt m n0))) (drop (S n0) O (CHead x0 (Flat f) t) e) 
(\lambda (_: (eq nat x1 O)).(drop_drop (Flat f) n0 x0 e (H11 x0 v H7 e H10) 
t)) (\lambda (H13: (ex2 nat (\lambda (m: nat).(eq nat x1 (S m))) (\lambda (m: 
nat).(lt m n0)))).(ex2_ind nat (\lambda (m: nat).(eq nat x1 (S m))) (\lambda 
(m: nat).(lt m n0)) (drop (S n0) O (CHead x0 (Flat f) t) e) (\lambda (x: 
nat).(\lambda (_: (eq nat x1 (S x))).(\lambda (_: (lt x n0)).(drop_drop (Flat 
f) n0 x0 e (H11 x0 v H7 e H10) t)))) H13)) (lt_gen_xS x1 n0 H12)))))]) 
(drop_gen_drop k c e t n0 H3) H8 H9))) c2 H6)))))) H4)) (\lambda (H4: (ex4_3 
T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat i (s k 
j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 
k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t 
u2)))) (\lambda (_: T).(\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c 
c2)))))).(ex4_3_ind T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat i (s k j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda 
(j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: 
nat).(csubst0 j v c c3)))) (drop (S n0) O c2 e) (\lambda (x0: T).(\lambda 
(x1: C).(\lambda (x2: nat).(\lambda (H5: (eq nat i (s k x2))).(\lambda (H6: 
(eq C c2 (CHead x1 k x0))).(\lambda (_: (subst0 x2 v t x0)).(\lambda (H8: 
(csubst0 x2 v c x1)).(eq_ind_r C (CHead x1 k x0) (\lambda (c0: C).(drop (S 
n0) O c0 e)) (let H9 \def (eq_ind nat i (\lambda (n: nat).(\forall (c2: 
C).(\forall (v: T).((csubst0 n v c c2) \to (\forall (e: C).((drop (S n0) O c 
e) \to (drop (S n0) O c2 e))))))) H1 (s k x2) H5) in (let H10 \def (eq_ind 
nat i (\lambda (n: nat).(lt n (S n0))) H0 (s k x2) H5) in ((match k in K 
return (\lambda (k0: K).((drop (r k0 n0) O c e) \to (((\forall (c2: 
C).(\forall (v: T).((csubst0 (s k0 x2) v c c2) \to (\forall (e: C).((drop (S 
n0) O c e) \to (drop (S n0) O c2 e))))))) \to ((lt (s k0 x2) (S n0)) \to 
(drop (S n0) O (CHead x1 k0 x0) e))))) with [(Bind b) \Rightarrow (\lambda 
(H11: (drop (r (Bind b) n0) O c e)).(\lambda (_: ((\forall (c2: C).(\forall 
(v: T).((csubst0 (s (Bind b) x2) v c c2) \to (\forall (e: C).((drop (S n0) O 
c e) \to (drop (S n0) O c2 e)))))))).(\lambda (H13: (lt (s (Bind b) x2) (S 
n0))).(drop_drop (Bind b) n0 x1 e (H x2 (lt_S_n x2 n0 H13) c x1 v H8 e H11) 
x0)))) | (Flat f) \Rightarrow (\lambda (H11: (drop (r (Flat f) n0) O c 
e)).(\lambda (H12: ((\forall (c2: C).(\forall (v: T).((csubst0 (s (Flat f) 
x2) v c c2) \to (\forall (e: C).((drop (S n0) O c e) \to (drop (S n0) O c2 
e)))))))).(\lambda (H13: (lt (s (Flat f) x2) (S n0))).(or_ind (eq nat x2 O) 
(ex2 nat (\lambda (m: nat).(eq nat x2 (S m))) (\lambda (m: nat).(lt m n0))) 
(drop (S n0) O (CHead x1 (Flat f) x0) e) (\lambda (_: (eq nat x2 
O)).(drop_drop (Flat f) n0 x1 e (H12 x1 v H8 e H11) x0)) (\lambda (H14: (ex2 
nat (\lambda (m: nat).(eq nat x2 (S m))) (\lambda (m: nat).(lt m 
n0)))).(ex2_ind nat (\lambda (m: nat).(eq nat x2 (S m))) (\lambda (m: 
nat).(lt m n0)) (drop (S n0) O (CHead x1 (Flat f) x0) e) (\lambda (x: 
nat).(\lambda (_: (eq nat x2 (S x))).(\lambda (_: (lt x n0)).(drop_drop (Flat 
f) n0 x1 e (H12 x1 v H8 e H11) x0)))) H14)) (lt_gen_xS x2 n0 H13)))))]) 
(drop_gen_drop k c e t n0 H3) H9 H10))) c2 H6)))))))) H4)) (csubst0_gen_head 
k c c2 t v i H2))))))))))) c1)))))) n).

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
O c2 e)).(let H2 \def (match H in le return (\lambda (n: nat).(\lambda (_: 
(le ? n)).((eq nat n O) \to (drop O O c1 e)))) with [le_n \Rightarrow 
(\lambda (H2: (eq nat (S i) O)).(let H3 \def (eq_ind nat (S i) (\lambda (e0: 
nat).(match e0 in nat return (\lambda (_: nat).Prop) with [O \Rightarrow 
False | (S _) \Rightarrow True])) I O H2) in (False_ind (drop O O c1 e) H3))) 
| (le_S m H2) \Rightarrow (\lambda (H3: (eq nat (S m) O)).((let H4 \def 
(eq_ind nat (S m) (\lambda (e0: nat).(match e0 in nat return (\lambda (_: 
nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) I O H3) in 
(False_ind ((le (S i) m) \to (drop O O c1 e)) H4)) H2))]) in (H2 (refl_equal 
nat O))))))))))) (\lambda (n0: nat).(\lambda (H: ((\forall (i: nat).((lt i 
n0) \to (\forall (c1: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c1 
c2) \to (\forall (e: C).((drop n0 O c2 e) \to (drop n0 O c1 
e))))))))))).(\lambda (i: nat).(\lambda (H0: (lt i (S n0))).(\lambda (c1: 
C).(C_ind (\lambda (c: C).(\forall (c2: C).(\forall (v: T).((csubst0 i v c 
c2) \to (\forall (e: C).((drop (S n0) O c2 e) \to (drop (S n0) O c e))))))) 
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
x0))).(\lambda (_: (subst0 x1 v t x0)).(let H8 \def (eq_ind C c2 (\lambda (c: 
C).(drop (S n0) O c e)) H3 (CHead c k x0) H6) in (let H9 \def (eq_ind nat i 
(\lambda (n: nat).(\forall (c2: C).(\forall (v: T).((csubst0 n v c c2) \to 
(\forall (e: C).((drop (S n0) O c2 e) \to (drop (S n0) O c e))))))) H1 (s k 
x1) H5) in (let H10 \def (eq_ind nat i (\lambda (n: nat).(lt n (S n0))) H0 (s 
k x1) H5) in ((match k in K return (\lambda (k0: K).(((\forall (c2: 
C).(\forall (v: T).((csubst0 (s k0 x1) v c c2) \to (\forall (e: C).((drop (S 
n0) O c2 e) \to (drop (S n0) O c e))))))) \to ((lt (s k0 x1) (S n0)) \to 
((drop (r k0 n0) O c e) \to (drop (S n0) O (CHead c k0 t) e))))) with [(Bind 
b) \Rightarrow (\lambda (_: ((\forall (c2: C).(\forall (v: T).((csubst0 (s 
(Bind b) x1) v c c2) \to (\forall (e: C).((drop (S n0) O c2 e) \to (drop (S 
n0) O c e)))))))).(\lambda (_: (lt (s (Bind b) x1) (S n0))).(\lambda (H13: 
(drop (r (Bind b) n0) O c e)).(drop_drop (Bind b) n0 c e H13 t)))) | (Flat f) 
\Rightarrow (\lambda (_: ((\forall (c2: C).(\forall (v: T).((csubst0 (s (Flat 
f) x1) v c c2) \to (\forall (e: C).((drop (S n0) O c2 e) \to (drop (S n0) O c 
e)))))))).(\lambda (H12: (lt (s (Flat f) x1) (S n0))).(\lambda (H13: (drop (r 
(Flat f) n0) O c e)).(or_ind (eq nat x1 O) (ex2 nat (\lambda (m: nat).(eq nat 
x1 (S m))) (\lambda (m: nat).(lt m n0))) (drop (S n0) O (CHead c (Flat f) t) 
e) (\lambda (_: (eq nat x1 O)).(drop_drop (Flat f) n0 c e H13 t)) (\lambda 
(H14: (ex2 nat (\lambda (m: nat).(eq nat x1 (S m))) (\lambda (m: nat).(lt m 
n0)))).(ex2_ind nat (\lambda (m: nat).(eq nat x1 (S m))) (\lambda (m: 
nat).(lt m n0)) (drop (S n0) O (CHead c (Flat f) t) e) (\lambda (x: 
nat).(\lambda (_: (eq nat x1 (S x))).(\lambda (_: (lt x n0)).(drop_drop (Flat 
f) n0 c e H13 t)))) H14)) (lt_gen_xS x1 n0 H12)))))]) H9 H10 (drop_gen_drop k 
c e x0 n0 H8)))))))))) H4)) (\lambda (H4: (ex3_2 C nat (\lambda (_: 
C).(\lambda (j: nat).(eq nat i (s k j)))) (\lambda (c3: C).(\lambda (_: 
nat).(eq C c2 (CHead c3 k t)))) (\lambda (c2: C).(\lambda (j: nat).(csubst0 j 
v c c2))))).(ex3_2_ind C nat (\lambda (_: C).(\lambda (j: nat).(eq nat i (s k 
j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) (\lambda 
(c3: C).(\lambda (j: nat).(csubst0 j v c c3))) (drop (S n0) O (CHead c k t) 
e) (\lambda (x0: C).(\lambda (x1: nat).(\lambda (H5: (eq nat i (s k 
x1))).(\lambda (H6: (eq C c2 (CHead x0 k t))).(\lambda (H7: (csubst0 x1 v c 
x0)).(let H8 \def (eq_ind C c2 (\lambda (c: C).(drop (S n0) O c e)) H3 (CHead 
x0 k t) H6) in (let H9 \def (eq_ind nat i (\lambda (n: nat).(\forall (c2: 
C).(\forall (v: T).((csubst0 n v c c2) \to (\forall (e: C).((drop (S n0) O c2 
e) \to (drop (S n0) O c e))))))) H1 (s k x1) H5) in (let H10 \def (eq_ind nat 
i (\lambda (n: nat).(lt n (S n0))) H0 (s k x1) H5) in ((match k in K return 
(\lambda (k0: K).(((\forall (c2: C).(\forall (v: T).((csubst0 (s k0 x1) v c 
c2) \to (\forall (e: C).((drop (S n0) O c2 e) \to (drop (S n0) O c e))))))) 
\to ((lt (s k0 x1) (S n0)) \to ((drop (r k0 n0) O x0 e) \to (drop (S n0) O 
(CHead c k0 t) e))))) with [(Bind b) \Rightarrow (\lambda (_: ((\forall (c2: 
C).(\forall (v: T).((csubst0 (s (Bind b) x1) v c c2) \to (\forall (e: 
C).((drop (S n0) O c2 e) \to (drop (S n0) O c e)))))))).(\lambda (H12: (lt (s 
(Bind b) x1) (S n0))).(\lambda (H13: (drop (r (Bind b) n0) O x0 
e)).(drop_drop (Bind b) n0 c e (H x1 (lt_S_n x1 n0 H12) c x0 v H7 e H13) 
t)))) | (Flat f) \Rightarrow (\lambda (H11: ((\forall (c2: C).(\forall (v: 
T).((csubst0 (s (Flat f) x1) v c c2) \to (\forall (e: C).((drop (S n0) O c2 
e) \to (drop (S n0) O c e)))))))).(\lambda (H12: (lt (s (Flat f) x1) (S 
n0))).(\lambda (H13: (drop (r (Flat f) n0) O x0 e)).(or_ind (eq nat x1 O) 
(ex2 nat (\lambda (m: nat).(eq nat x1 (S m))) (\lambda (m: nat).(lt m n0))) 
(drop (S n0) O (CHead c (Flat f) t) e) (\lambda (_: (eq nat x1 O)).(drop_drop 
(Flat f) n0 c e (H11 x0 v H7 e H13) t)) (\lambda (H14: (ex2 nat (\lambda (m: 
nat).(eq nat x1 (S m))) (\lambda (m: nat).(lt m n0)))).(ex2_ind nat (\lambda 
(m: nat).(eq nat x1 (S m))) (\lambda (m: nat).(lt m n0)) (drop (S n0) O 
(CHead c (Flat f) t) e) (\lambda (x: nat).(\lambda (_: (eq nat x1 (S 
x))).(\lambda (_: (lt x n0)).(drop_drop (Flat f) n0 c e (H11 x0 v H7 e H13) 
t)))) H14)) (lt_gen_xS x1 n0 H12)))))]) H9 H10 (drop_gen_drop k x0 e t n0 
H8)))))))))) H4)) (\lambda (H4: (ex4_3 T C nat (\lambda (_: T).(\lambda (_: 
C).(\lambda (j: nat).(eq nat i (s k j))))) (\lambda (u2: T).(\lambda (c3: 
C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda 
(_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c2: 
C).(\lambda (j: nat).(csubst0 j v c c2)))))).(ex4_3_ind T C nat (\lambda (_: 
T).(\lambda (_: C).(\lambda (j: nat).(eq nat i (s k j))))) (\lambda (u2: 
T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda 
(u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: 
T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3)))) (drop (S n0) O 
(CHead c k t) e) (\lambda (x0: T).(\lambda (x1: C).(\lambda (x2: 
nat).(\lambda (H5: (eq nat i (s k x2))).(\lambda (H6: (eq C c2 (CHead x1 k 
x0))).(\lambda (_: (subst0 x2 v t x0)).(\lambda (H8: (csubst0 x2 v c 
x1)).(let H9 \def (eq_ind C c2 (\lambda (c: C).(drop (S n0) O c e)) H3 (CHead 
x1 k x0) H6) in (let H10 \def (eq_ind nat i (\lambda (n: nat).(\forall (c2: 
C).(\forall (v: T).((csubst0 n v c c2) \to (\forall (e: C).((drop (S n0) O c2 
e) \to (drop (S n0) O c e))))))) H1 (s k x2) H5) in (let H11 \def (eq_ind nat 
i (\lambda (n: nat).(lt n (S n0))) H0 (s k x2) H5) in ((match k in K return 
(\lambda (k0: K).(((\forall (c2: C).(\forall (v: T).((csubst0 (s k0 x2) v c 
c2) \to (\forall (e: C).((drop (S n0) O c2 e) \to (drop (S n0) O c e))))))) 
\to ((lt (s k0 x2) (S n0)) \to ((drop (r k0 n0) O x1 e) \to (drop (S n0) O 
(CHead c k0 t) e))))) with [(Bind b) \Rightarrow (\lambda (_: ((\forall (c2: 
C).(\forall (v: T).((csubst0 (s (Bind b) x2) v c c2) \to (\forall (e: 
C).((drop (S n0) O c2 e) \to (drop (S n0) O c e)))))))).(\lambda (H13: (lt (s 
(Bind b) x2) (S n0))).(\lambda (H14: (drop (r (Bind b) n0) O x1 
e)).(drop_drop (Bind b) n0 c e (H x2 (lt_S_n x2 n0 H13) c x1 v H8 e H14) 
t)))) | (Flat f) \Rightarrow (\lambda (H12: ((\forall (c2: C).(\forall (v: 
T).((csubst0 (s (Flat f) x2) v c c2) \to (\forall (e: C).((drop (S n0) O c2 
e) \to (drop (S n0) O c e)))))))).(\lambda (H13: (lt (s (Flat f) x2) (S 
n0))).(\lambda (H14: (drop (r (Flat f) n0) O x1 e)).(or_ind (eq nat x2 O) 
(ex2 nat (\lambda (m: nat).(eq nat x2 (S m))) (\lambda (m: nat).(lt m n0))) 
(drop (S n0) O (CHead c (Flat f) t) e) (\lambda (_: (eq nat x2 O)).(drop_drop 
(Flat f) n0 c e (H12 x1 v H8 e H14) t)) (\lambda (H15: (ex2 nat (\lambda (m: 
nat).(eq nat x2 (S m))) (\lambda (m: nat).(lt m n0)))).(ex2_ind nat (\lambda 
(m: nat).(eq nat x2 (S m))) (\lambda (m: nat).(lt m n0)) (drop (S n0) O 
(CHead c (Flat f) t) e) (\lambda (x: nat).(\lambda (_: (eq nat x2 (S 
x))).(\lambda (_: (lt x n0)).(drop_drop (Flat f) n0 c e (H12 x1 v H8 e H14) 
t)))) H15)) (lt_gen_xS x2 n0 H13)))))]) H10 H11 (drop_gen_drop k x1 e x0 n0 
H9)))))))))))) H4)) (csubst0_gen_head k c c2 t v i H2))))))))))) c1)))))) n).

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
nat i0 (\lambda (n: nat).(subst0 n v0 u1 u2)) H2 (minus (s k i0) (s k O)) 
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
(ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C c3 (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop O O c4 (CHead e0 k w)))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i0 (s k O)) v0 u 
w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c3 (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop O O c4 (CHead e2 k u)))))) (\lambda 
(k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i0 
(s k O)) v0 e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop O O c4 (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i0 (s k 
O)) v0 u w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus i0 (s k O)) v0 e1 e2))))))))).(\lambda 
(u: T).(let H4 \def (eq_ind_r nat i0 (\lambda (n: nat).(csubst0 n v0 c3 c4)) 
H2 (minus (s k i0) (s k O)) (s_arith0 k i0)) in (let H5 \def (eq_ind_r nat i0 
(\lambda (n: nat).(or4 (drop O O c4 c3) (ex3_4 K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e0 k 
u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop O O c4 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus n (s k O)) v0 u w)))))) (ex3_4 K C C T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c3 
(CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u: T).(drop O O c4 (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus n (s k O)) v0 e1 e2)))))) 
(ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C c3 (CHead e1 k u))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop O O c4 (CHead 
e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus n (s k O)) v0 u w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus n (s k O)) v0 e1 e2))))))))) H3 (minus (s k i0) (s k O)) (s_arith0 k 
i0)) in (or4_intro2 (drop O O (CHead c4 k u) (CHead c3 k u)) (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C 
(CHead c3 k u) (CHead e0 k0 u0)))))) (\lambda (k0: K).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop O O (CHead c4 k u) (CHead e0 k0 
w)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s k i0) (s k0 O)) v0 u0 w)))))) (ex3_4 K C C T (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C (CHead c3 k 
u) (CHead e1 k0 u0)))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop O O (CHead c4 k u) (CHead e2 k0 u0)))))) (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s 
k i0) (s k0 O)) v0 e1 e2)))))) (ex4_5 K C C T T (\lambda (k0: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead c3 k u) 
(CHead e1 k0 u0))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop O O (CHead c4 k u) (CHead e2 k0 
w))))))) (\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 (minus (s k i0) (s k0 O)) v0 u0 w)))))) (\lambda 
(k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: 
T).(csubst0 (minus (s k i0) (s k0 O)) v0 e1 e2))))))) (ex3_4_intro K C C T 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C 
(CHead c3 k u) (CHead e1 k0 u0)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u0: T).(drop O O (CHead c4 k u) (CHead e2 k0 
u0)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s k i0) (s k0 O)) v0 e1 e2))))) k c3 c4 u (refl_equal C 
(CHead c3 k u)) (drop_refl (CHead c4 k u)) H4)))))))))))) (\lambda (k: 
K).(\lambda (i0: nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda (u2: 
T).(\lambda (H2: (subst0 i0 v0 u1 u2)).(\lambda (c3: C).(\lambda (c4: 
C).(\lambda (H3: (csubst0 i0 v0 c3 c4)).(\lambda (_: (or4 (drop O O c4 c3) 
(ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C c3 (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop O O c4 (CHead e0 k w)))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i0 (s k O)) v0 u 
w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c3 (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop O O c4 (CHead e2 k u)))))) (\lambda 
(k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i0 
(s k O)) v0 e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop O O c4 (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i0 (s k 
O)) v0 u w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus i0 (s k O)) v0 e1 e2))))))))).(let H5 
\def (eq_ind_r nat i0 (\lambda (n: nat).(subst0 n v0 u1 u2)) H2 (minus (s k 
i0) (s k O)) (s_arith0 k i0)) in (let H6 \def (eq_ind_r nat i0 (\lambda (n: 
nat).(csubst0 n v0 c3 c4)) H3 (minus (s k i0) (s k O)) (s_arith0 k i0)) in 
(or4_intro3 (drop O O (CHead c4 k u2) (CHead c3 k u1)) (ex3_4 K C T T 
(\lambda (k0: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead c3 k u1) (CHead e0 k0 u)))))) (\lambda (k0: K).(\lambda (e0: 
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
(H2: (drop (S n0) O (CHead c k t) e)).(let H3 \def (match H1 in csubst0 
return (\lambda (n: nat).(\lambda (t0: T).(\lambda (c0: C).(\lambda (c1: 
C).(\lambda (_: (csubst0 n t0 c0 c1)).((eq nat n i) \to ((eq T t0 v) \to ((eq 
C c0 (CHead c k t)) \to ((eq C c1 c2) \to (or4 (drop (S n0) O c2 e) (ex3_4 K 
C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
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
n0))) v e1 e2))))))))))))))))) with [(csubst0_snd k0 i0 v0 u1 u2 H3 c0) 
\Rightarrow (\lambda (H4: (eq nat (s k0 i0) i)).(\lambda (H5: (eq T v0 
v)).(\lambda (H6: (eq C (CHead c0 k0 u1) (CHead c k t))).(\lambda (H7: (eq C 
(CHead c0 k0 u2) c2)).(eq_ind nat (s k0 i0) (\lambda (n: nat).((eq T v0 v) 
\to ((eq C (CHead c0 k0 u1) (CHead c k t)) \to ((eq C (CHead c0 k0 u2) c2) 
\to ((subst0 i0 v0 u1 u2) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus n (s k (S n0))) v u w)))))) 
(ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k u)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus n (s k 
(S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus n (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus n (s k (S n0))) v e1 
e2))))))))))))) (\lambda (H8: (eq T v0 v)).(eq_ind T v (\lambda (t0: T).((eq 
C (CHead c0 k0 u1) (CHead c k t)) \to ((eq C (CHead c0 k0 u2) c2) \to 
((subst0 i0 t0 u1 u2) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T (\lambda 
(k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k 
u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k0 i0) (s k (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k u)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s k0 i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s k0 i0) (s k (S n0))) v u w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s k0 i0) (s k (S n0))) v e1 e2)))))))))))) (\lambda (H9: (eq C (CHead 
c0 k0 u1) (CHead c k t))).(let H10 \def (f_equal C T (\lambda (e0: C).(match 
e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u1 | (CHead _ _ 
t) \Rightarrow t])) (CHead c0 k0 u1) (CHead c k t) H9) in ((let H11 \def 
(f_equal C K (\lambda (e0: C).(match e0 in C return (\lambda (_: C).K) with 
[(CSort _) \Rightarrow k0 | (CHead _ k _) \Rightarrow k])) (CHead c0 k0 u1) 
(CHead c k t) H9) in ((let H12 \def (f_equal C C (\lambda (e0: C).(match e0 
in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c0 | (CHead c _ _) 
\Rightarrow c])) (CHead c0 k0 u1) (CHead c k t) H9) in (eq_ind C c (\lambda 
(c: C).((eq K k0 k) \to ((eq T u1 t) \to ((eq C (CHead c k0 u2) c2) \to 
((subst0 i0 v u1 u2) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T (\lambda 
(k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k 
u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k0 i0) (s k (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k u)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s k0 i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s k0 i0) (s k (S n0))) v u w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s k0 i0) (s k (S n0))) v e1 e2))))))))))))) (\lambda (H13: (eq K k0 
k)).(eq_ind K k (\lambda (k: K).((eq T u1 t) \to ((eq C (CHead c k u2) c2) 
\to ((subst0 i0 v u1 u2) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T 
(\lambda (k1: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k1 u)))))) (\lambda (k1: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 k1 w)))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k i0) (s 
k1 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k1: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k1 u)))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead 
e2 k1 u)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s k i0) (s k1 (S n0))) v e1 e2)))))) (ex4_5 K C C T T 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e1 k1 u))))))) (\lambda (k1: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead 
e2 k1 w))))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s k i0) (s k1 (S n0))) v u w)))))) 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus (s k i0) (s k1 (S n0))) v e1 e2)))))))))))) (\lambda 
(H14: (eq T u1 t)).(eq_ind T t (\lambda (t: T).((eq C (CHead c k u2) c2) \to 
((subst0 i0 v t u2) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k 
u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k1: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k i0) (s k1 (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k u)))))) 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s k i0) (s k1 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) 
(\lambda (k1: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s k i0) (s k1 (S n0))) v u w)))))) (\lambda (k1: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s k i0) (s k1 (S n0))) v e1 e2))))))))))) (\lambda (H15: (eq C (CHead 
c k u2) c2)).(eq_ind C (CHead c k u2) (\lambda (c: C).((subst0 i0 v t u2) \to 
(or4 (drop (S n0) O c e) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k u)))))) (\lambda (k: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c (CHead 
e0 k w)))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s k i0) (s k1 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda 
(k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k 
u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O c (CHead e2 k u)))))) (\lambda (k1: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s k i0) (s k1 (S n0))) v 
e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O c (CHead e2 k w))))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k i0) (s k1 (S n0))) v u 
w)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus (s k i0) (s k1 (S n0))) v e1 e2)))))))))) 
(\lambda (_: (subst0 i0 v t u2)).(let H1 \def (eq_ind K k0 (\lambda (k: 
K).(eq nat (s k i0) i)) H4 k H13) in (let H17 \def (eq_ind_r nat i (\lambda 
(n: nat).(\forall (c2: C).(\forall (v: T).((csubst0 n v c c2) \to (\forall 
(e: C).((drop (S n0) O c e) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus n (s k (S n0))) v u w)))))) 
(ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k u)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus n (s k 
(S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus n (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus n (s k (S n0))) v e1 
e2)))))))))))))) H0 (s k i0) H1) in (let H18 \def (eq_ind_r nat i (\lambda 
(n: nat).(lt (S n0) n)) H (s k i0) H1) in (K_ind (\lambda (k: K).((drop (r k 
n0) O c e) \to (((\forall (c2: C).(\forall (v: T).((csubst0 (s k i0) v c c2) 
\to (\forall (e: C).((drop (S n0) O c e) \to (or4 (drop (S n0) O c2 e) (ex3_4 
K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k i0) (s 
k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead 
e2 k u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s k i0) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s k i0) (s k0 (S n0))) v u w)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s k i0) (s k0 (S n0))) v e1 e2)))))))))))))) \to ((lt (S n0) (s k 
i0)) \to (or4 (drop (S n0) O (CHead c k u2) e) (ex3_4 K C T T (\lambda (k1: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k1 
u)))))) (\lambda (k1: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead c k u2) (CHead e0 k1 w)))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k i0) (s 
k1 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k1: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k1 u)))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c k 
u2) (CHead e2 k1 u)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s k i0) (s k1 (S n0))) v e1 e2)))))) 
(ex4_5 K C C T T (\lambda (k1: K).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e1 k1 u))))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c k u2) (CHead e2 k1 w))))))) (\lambda (k1: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k i0) (s 
k1 (S n0))) v u w)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s k i0) (s k1 (S n0))) v 
e1 e2)))))))))))) (\lambda (b: B).(\lambda (H2: (drop (r (Bind b) n0) O c 
e)).(\lambda (_: ((\forall (c2: C).(\forall (v: T).((csubst0 (s (Bind b) i0) 
v c c2) \to (\forall (e: C).((drop (S n0) O c e) \to (or4 (drop (S n0) O c2 
e) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead 
e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T 
T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k 
w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u w)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2))))))))))))))).(\lambda (_: (lt (S n0) (s (Bind b) i0))).(or4_intro0 (drop 
(S n0) O (CHead c (Bind b) u2) e) (ex3_4 K C T T (\lambda (k: K).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k u)))))) (\lambda 
(k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead 
c (Bind b) u2) (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c (Bind b) u2) 
(CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c (Bind b) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S 
n0))) v e1 e2))))))) (drop_drop (Bind b) n0 c e H2 u2)))))) (\lambda (f: 
F).(\lambda (H2: (drop (r (Flat f) n0) O c e)).(\lambda (_: ((\forall (c2: 
C).(\forall (v: T).((csubst0 (s (Flat f) i0) v c c2) \to (\forall (e: 
C).((drop (S n0) O c e) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T (\lambda 
(k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k 
u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) i0) (s k (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k u)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2))))))))))))))).(\lambda (_: (lt 
(S n0) (s (Flat f) i0))).(or4_intro0 (drop (S n0) O (CHead c (Flat f) u2) e) 
(ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c (Flat f) u2) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k 
u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead c (Flat f) u2) (CHead e2 k u)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c (Flat f) u2) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2))))))) (drop_drop (Flat f) n0 c 
e H2 u2)))))) k (drop_gen_drop k c e t n0 H2) H17 H18))))) c2 H15)) u1 
(sym_eq T u1 t H14))) k0 (sym_eq K k0 k H13))) c0 (sym_eq C c0 c H12))) H11)) 
H10))) v0 (sym_eq T v0 v H8))) i H4 H5 H6 H7 H3))))) | (csubst0_fst k0 i0 c1 
c0 v0 H3 u) \Rightarrow (\lambda (H4: (eq nat (s k0 i0) i)).(\lambda (H5: (eq 
T v0 v)).(\lambda (H6: (eq C (CHead c1 k0 u) (CHead c k t))).(\lambda (H7: 
(eq C (CHead c0 k0 u) c2)).(eq_ind nat (s k0 i0) (\lambda (n: nat).((eq T v0 
v) \to ((eq C (CHead c1 k0 u) (CHead c k t)) \to ((eq C (CHead c0 k0 u) c2) 
\to ((csubst0 i0 v0 c1 c0) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e 
(CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus n (s k (S 
n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u0: T).(eq C e (CHead e1 k u0)))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (S n0) O c2 (CHead e2 k 
u0)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus n (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C e (CHead e1 k u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus n (s k (S n0))) v u0 w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus n (s k (S 
n0))) v e1 e2))))))))))))) (\lambda (H8: (eq T v0 v)).(eq_ind T v (\lambda 
(t0: T).((eq C (CHead c1 k0 u) (CHead c k t)) \to ((eq C (CHead c0 k0 u) c2) 
\to ((csubst0 i0 t0 c1 c0) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e 
(CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus (s k0 i0) 
(s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 k u0)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (S n0) O c2 (CHead 
e2 k u0)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s k0 i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda 
(_: T).(eq C e (CHead e1 k u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k 
w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 (minus (s k0 i0) (s k (S n0))) v u0 w)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus (s k0 i0) (s k (S n0))) v e1 e2)))))))))))) (\lambda 
(H9: (eq C (CHead c1 k0 u) (CHead c k t))).(let H10 \def (f_equal C T 
(\lambda (e0: C).(match e0 in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead c1 k0 u) (CHead c k t) 
H9) in ((let H11 \def (f_equal C K (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).K) with [(CSort _) \Rightarrow k0 | (CHead _ k _) \Rightarrow 
k])) (CHead c1 k0 u) (CHead c k t) H9) in ((let H12 \def (f_equal C C 
(\lambda (e0: C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow c1 | (CHead c _ _) \Rightarrow c])) (CHead c1 k0 u) (CHead c k t) 
H9) in (eq_ind C c (\lambda (c: C).((eq K k0 k) \to ((eq T u t) \to ((eq C 
(CHead c0 k0 u) c2) \to ((csubst0 i0 v c c0) \to (or4 (drop (S n0) O c2 e) 
(ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: 
T).(eq C e (CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus (s k0 i0) 
(s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 k u0)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (S n0) O c2 (CHead 
e2 k u0)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s k0 i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda 
(_: T).(eq C e (CHead e1 k u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k 
w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 (minus (s k0 i0) (s k (S n0))) v u0 w)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus (s k0 i0) (s k (S n0))) v e1 e2))))))))))))) (\lambda 
(H13: (eq K k0 k)).(eq_ind K k (\lambda (k: K).((eq T u t) \to ((eq C (CHead 
c0 k u) c2) \to ((csubst0 i0 v c c0) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C 
T T (\lambda (k1: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C 
e (CHead e0 k1 u0)))))) (\lambda (k1: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 k1 w)))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus (s k i0) 
(s k1 (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k1: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 k1 u0)))))) (\lambda 
(k1: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (S n0) O c2 
(CHead e2 k1 u0)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s k i0) (s k1 (S n0))) v e1 e2)))))) 
(ex4_5 K C C T T (\lambda (k1: K).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C e (CHead e1 k1 u0))))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O c2 (CHead e2 k1 w))))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus (s k i0) (s k1 (S n0))) v 
u0 w)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus (s k i0) (s k1 (S n0))) v e1 
e2)))))))))))) (\lambda (H14: (eq T u t)).(eq_ind T t (\lambda (t: T).((eq C 
(CHead c0 k t) c2) \to ((csubst0 i0 v c c0) \to (or4 (drop (S n0) O c2 e) 
(ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: 
T).(eq C e (CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus (s k i0) 
(s k1 (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 k u0)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (S n0) O c2 (CHead 
e2 k u0)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s k i0) (s k1 (S n0))) v e1 e2)))))) (ex4_5 K C C T T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda 
(_: T).(eq C e (CHead e1 k u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k 
w))))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 (minus (s k i0) (s k1 (S n0))) v u0 w)))))) 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus (s k i0) (s k1 (S n0))) v e1 e2))))))))))) (\lambda 
(H15: (eq C (CHead c0 k t) c2)).(eq_ind C (CHead c0 k t) (\lambda (c2: 
C).((csubst0 i0 v c c0) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T (\lambda 
(k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 k 
u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k1: K).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus (s k i0) (s k1 (S n0))) v 
u0 w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(eq C e (CHead e1 k u0)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u0: T).(drop (S n0) O c2 (CHead e2 k u0)))))) 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s k i0) (s k1 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e 
(CHead e1 k u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) 
(\lambda (k1: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda 
(w: T).(subst0 (minus (s k i0) (s k1 (S n0))) v u0 w)))))) (\lambda (k1: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s k i0) (s k1 (S n0))) v e1 e2)))))))))) (\lambda (H16: (csubst0 i0 v 
c c0)).(let H1 \def (eq_ind K k0 (\lambda (k: K).(eq nat (s k i0) i)) H4 k 
H13) in (let H17 \def (eq_ind_r nat i (\lambda (n: nat).(\forall (c2: 
C).(\forall (v: T).((csubst0 n v c c2) \to (\forall (e: C).((drop (S n0) O c 
e) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k u)))))) (\lambda (k: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead 
e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus n (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k 
u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O c2 (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus n (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O c2 (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus n (s k (S n0))) v u w)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus n (s k (S n0))) v e1 e2)))))))))))))) H0 (s k i0) H1) 
in (let H18 \def (eq_ind_r nat i (\lambda (n: nat).(lt (S n0) n)) H (s k i0) 
H1) in (K_ind (\lambda (k: K).((drop (r k n0) O c e) \to (((\forall (c2: 
C).(\forall (v: T).((csubst0 (s k i0) v c c2) \to (\forall (e: C).((drop (S 
n0) O c e) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k 
u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k0: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k i0) (s k0 (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k u)))))) 
(\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s k i0) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s k i0) (s k0 (S n0))) v u w)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s k i0) (s k0 (S n0))) v e1 e2)))))))))))))) \to ((lt (S n0) (s k 
i0)) \to (or4 (drop (S n0) O (CHead c0 k t) e) (ex3_4 K C T T (\lambda (k1: 
K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 k1 
u0)))))) (\lambda (k1: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead c0 k t) (CHead e0 k1 w)))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus (s k i0) 
(s k1 (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k1: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 k1 u0)))))) (\lambda 
(k1: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (S n0) O 
(CHead c0 k t) (CHead e2 k1 u0)))))) (\lambda (k1: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s k i0) (s k1 (S n0))) v 
e1 e2)))))) (ex4_5 K C C T T (\lambda (k1: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 k1 u0))))))) (\lambda 
(k1: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead c0 k t) (CHead e2 k1 w))))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus (s k i0) (s k1 (S n0))) v u0 w)))))) (\lambda (k1: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s k i0) 
(s k1 (S n0))) v e1 e2)))))))))))) (\lambda (b: B).(\lambda (H2: (drop (r 
(Bind b) n0) O c e)).(\lambda (_: ((\forall (c2: C).(\forall (v: T).((csubst0 
(s (Bind b) i0) v c c2) \to (\forall (e: C).((drop (S n0) O c e) \to (or4 
(drop (S n0) O c2 e) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e0 k u)))))) (\lambda (k: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k 
u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O c2 (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S 
n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s 
(Bind b) i0) (s k (S n0))) v e1 e2))))))))))))))).(\lambda (H: (lt (S n0) (s 
(Bind b) i0))).(let H19 \def (IHn i0 (le_S_n (S n0) i0 H) c c0 v H16 e H2) in 
(or4_ind (drop n0 O c0 e) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 k u0)))))) (\lambda (k: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O c0 (CHead e0 k 
w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus i0 (s k n0)) v u0 w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 k 
u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop n0 O c0 (CHead e2 k u0)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i0 (s k n0)) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 k u0))))))) (\lambda 
(k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop 
n0 O c0 (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus i0 (s k n0)) v u0 w)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i0 (s k n0)) v e1 e2))))))) (or4 (drop (S n0) O (CHead 
c0 (Bind b) t) e) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C e (CHead e0 k u0)))))) (\lambda (k: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) 
(CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda 
(w: T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C 
T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e 
(CHead e1 k u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e2 k u0)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C e (CHead e1 k u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) 
(CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (w: T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u0 
w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2)))))))) (\lambda (H20: (drop n0 O c0 e)).(or4_intro0 (drop (S n0) O (CHead 
c0 (Bind b) t) e) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C e (CHead e0 k u0)))))) (\lambda (k: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) 
(CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda 
(w: T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C 
T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e 
(CHead e1 k u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e2 k u0)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C e (CHead e1 k u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) 
(CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (w: T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u0 
w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2))))))) (drop_drop (Bind b) n0 c0 e H20 t))) (\lambda (H20: (ex3_4 K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop n0 O c0 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i0 (s k n0)) v u 
w))))))).(ex3_4_ind K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C e (CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop n0 O c0 (CHead e0 k w)))))) (\lambda 
(k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus i0 (s 
k n0)) v u0 w))))) (or4 (drop (S n0) O (CHead c0 (Bind b) t) e) (ex3_4 K C T 
T (\lambda (k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e 
(CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 k 
u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e2 k u0)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u0 w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2)))))))) (\lambda (x0: 
K).(\lambda (x1: C).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H21: (eq C e 
(CHead x1 x0 x2))).(\lambda (H22: (drop n0 O c0 (CHead x1 x0 x3))).(\lambda 
(H23: (subst0 (minus i0 (s x0 n0)) v x2 x3)).(eq_ind_r C (CHead x1 x0 x2) 
(\lambda (c: C).(or4 (drop (S n0) O (CHead c0 (Bind b) t) c) (ex3_4 K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C c 
(CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C c (CHead e1 k 
u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e2 k u0)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C c (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u0 w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2))))))))) (or4_intro1 (drop (S 
n0) O (CHead c0 (Bind b) t) (CHead x1 x0 x2)) (ex3_4 K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead x1 x0 x2) 
(CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C (CHead x1 x0 x2) 
(CHead e1 k u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e2 k u0)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C (CHead x1 x0 x2) (CHead e1 k u0))))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 
(Bind b) t) (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus (s (Bind b) i0) (s k (S 
n0))) v u0 w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2))))))) (ex3_4_intro K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C (CHead x1 x0 x2) (CHead e0 k u0)))))) (\lambda (k: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 
(Bind b) t) (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u0 w))))) 
x0 x1 x2 x3 (refl_equal C (CHead x1 x0 x2)) (drop_drop (Bind b) n0 c0 (CHead 
x1 x0 x3) H22 t) (eq_ind_r nat (S (s x0 n0)) (\lambda (n: nat).(subst0 (minus 
(s (Bind b) i0) n) v x2 x3)) H23 (s x0 (S n0)) (s_S x0 n0)))) e H21)))))))) 
H20)) (\lambda (H20: (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u: T).(drop n0 O c0 (CHead e2 k u)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus i0 (s k n0)) v e1 e2))))))).(ex3_4_ind K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 k 
u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop n0 O c0 (CHead e2 k u0)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i0 (s k n0)) v e1 e2))))) 
(or4 (drop (S n0) O (CHead c0 (Bind b) t) e) (ex3_4 K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 k 
u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus (s (Bind 
b) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 k u0)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (S 
n0) O (CHead c0 (Bind b) t) (CHead e2 k u0)))))) (\lambda (k: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k 
(S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u0 w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2)))))))) (\lambda (x0: 
K).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H21: (eq C e 
(CHead x1 x0 x3))).(\lambda (H22: (drop n0 O c0 (CHead x2 x0 x3))).(\lambda 
(H23: (csubst0 (minus i0 (s x0 n0)) v x1 x2)).(eq_ind_r C (CHead x1 x0 x3) 
(\lambda (c: C).(or4 (drop (S n0) O (CHead c0 (Bind b) t) c) (ex3_4 K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C c 
(CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C c (CHead e1 k 
u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e2 k u0)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C c (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u0 w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2))))))))) (or4_intro2 (drop (S 
n0) O (CHead c0 (Bind b) t) (CHead x1 x0 x3)) (ex3_4 K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead x1 x0 x3) 
(CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C (CHead x1 x0 x3) 
(CHead e1 k u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e2 k u0)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C (CHead x1 x0 x3) (CHead e1 k u0))))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 
(Bind b) t) (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus (s (Bind b) i0) (s k (S 
n0))) v u0 w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2))))))) (ex3_4_intro K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(eq C (CHead x1 x0 x3) (CHead e1 k u0)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (S n0) O (CHead c0 
(Bind b) t) (CHead e2 k u0)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2))))) x0 x1 x2 x3 (refl_equal C (CHead x1 x0 x3)) (drop_drop (Bind b) n0 c0 
(CHead x2 x0 x3) H22 t) (eq_ind_r nat (S (s x0 n0)) (\lambda (n: 
nat).(csubst0 (minus (s (Bind b) i0) n) v x1 x2)) H23 (s x0 (S n0)) (s_S x0 
n0)))) e H21)))))))) H20)) (\lambda (H20: (ex4_5 K C C T T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop n0 O c0 (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i0 (s k n0)) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (s k 
n0)) v e1 e2)))))))).(ex4_5_ind K C C T T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop n0 O c0 (CHead e2 k w))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus i0 (s k n0)) v u0 w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (s k n0)) v e1 
e2)))))) (or4 (drop (S n0) O (CHead c0 (Bind b) t) e) (ex3_4 K C T T (\lambda 
(k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 k 
u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus (s (Bind 
b) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 k u0)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (S 
n0) O (CHead c0 (Bind b) t) (CHead e2 k u0)))))) (\lambda (k: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k 
(S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u0 w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2)))))))) (\lambda (x0: 
K).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: 
T).(\lambda (H21: (eq C e (CHead x1 x0 x3))).(\lambda (H22: (drop n0 O c0 
(CHead x2 x0 x4))).(\lambda (H23: (subst0 (minus i0 (s x0 n0)) v x3 
x4)).(\lambda (H24: (csubst0 (minus i0 (s x0 n0)) v x1 x2)).(eq_ind_r C 
(CHead x1 x0 x3) (\lambda (c: C).(or4 (drop (S n0) O (CHead c0 (Bind b) t) c) 
(ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: 
T).(eq C c (CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C c (CHead e1 k 
u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e2 k u0)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C c (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u0 w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2))))))))) (or4_intro3 (drop (S 
n0) O (CHead c0 (Bind b) t) (CHead x1 x0 x3)) (ex3_4 K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead x1 x0 x3) 
(CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C (CHead x1 x0 x3) 
(CHead e1 k u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e2 k u0)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C (CHead x1 x0 x3) (CHead e1 k u0))))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 
(Bind b) t) (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus (s (Bind b) i0) (s k (S 
n0))) v u0 w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2))))))) (ex4_5_intro K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead x1 x0 x3) (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) t) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u0 w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2)))))) x0 x1 x2 x3 x4 (refl_equal 
C (CHead x1 x0 x3)) (drop_drop (Bind b) n0 c0 (CHead x2 x0 x4) H22 t) 
(eq_ind_r nat (S (s x0 n0)) (\lambda (n: nat).(subst0 (minus (s (Bind b) i0) 
n) v x3 x4)) H23 (s x0 (S n0)) (s_S x0 n0)) (eq_ind_r nat (S (s x0 n0)) 
(\lambda (n: nat).(csubst0 (minus (s (Bind b) i0) n) v x1 x2)) H24 (s x0 (S 
n0)) (s_S x0 n0)))) e H21)))))))))) H20)) H19)))))) (\lambda (f: F).(\lambda 
(H2: (drop (r (Flat f) n0) O c e)).(\lambda (H0: ((\forall (c2: C).(\forall 
(v: T).((csubst0 (s (Flat f) i0) v c c2) \to (\forall (e: C).((drop (S n0) O 
c e) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T (\lambda (k: K).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k u)))))) (\lambda 
(k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 
(CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u w)))))) (ex3_4 K C C 
T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u: T).(drop (S n0) O c2 (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S 
n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s 
(Flat f) i0) (s k (S n0))) v e1 e2))))))))))))))).(\lambda (_: (lt (S n0) (s 
(Flat f) i0))).(let H19 \def (H0 c0 v H16 e H2) in (or4_ind (drop (S n0) O c0 
e) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda 
(_: T).(eq C e (CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus i0 (s k (S 
n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u0: T).(eq C e (CHead e1 k u0)))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (S n0) O c0 (CHead e2 k 
u0)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus i0 (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C e (CHead e1 k u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus i0 (s k (S n0))) v u0 w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (s k 
(S n0))) v e1 e2))))))) (or4 (drop (S n0) O (CHead c0 (Flat f) t) e) (ex3_4 K 
C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C 
e (CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 k 
u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k u0)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2)))))))) (\lambda (H20: (drop (S 
n0) O c0 e)).(or4_intro0 (drop (S n0) O (CHead c0 (Flat f) t) e) (ex3_4 K C T 
T (\lambda (k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e 
(CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 k 
u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k u0)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2))))))) (drop_drop (Flat f) n0 c0 
e H20 t))) (\lambda (H20: (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k u)))))) (\lambda (k: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead 
e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i0 (s k (S n0))) v u w))))))).(ex3_4_ind K C T T (\lambda 
(k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 k 
u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c0 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus i0 (s k (S n0))) v u0 
w))))) (or4 (drop (S n0) O (CHead c0 (Flat f) t) e) (ex3_4 K C T T (\lambda 
(k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 k 
u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus (s (Flat 
f) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 k u0)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (S 
n0) O (CHead c0 (Flat f) t) (CHead e2 k u0)))))) (\lambda (k: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k 
(S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2)))))))) (\lambda (x0: 
K).(\lambda (x1: C).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H21: (eq C e 
(CHead x1 x0 x2))).(\lambda (H22: (drop (S n0) O c0 (CHead x1 x0 
x3))).(\lambda (H23: (subst0 (minus i0 (s x0 (S n0))) v x2 x3)).(eq_ind_r C 
(CHead x1 x0 x2) (\lambda (c: C).(or4 (drop (S n0) O (CHead c0 (Flat f) t) c) 
(ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: 
T).(eq C c (CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C c (CHead e1 k 
u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k u0)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C c (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2))))))))) (or4_intro1 (drop (S 
n0) O (CHead c0 (Flat f) t) (CHead x1 x0 x2)) (ex3_4 K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead x1 x0 x2) 
(CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C (CHead x1 x0 x2) 
(CHead e1 k u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k u0)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C (CHead x1 x0 x2) (CHead e1 k u0))))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 
(Flat f) t) (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus (s (Flat f) i0) (s k (S 
n0))) v u0 w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2))))))) (ex3_4_intro K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C (CHead x1 x0 x2) (CHead e0 k u0)))))) (\lambda (k: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 
(Flat f) t) (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u0 w))))) 
x0 x1 x2 x3 (refl_equal C (CHead x1 x0 x2)) (drop_drop (Flat f) n0 c0 (CHead 
x1 x0 x3) H22 t) H23)) e H21)))))))) H20)) (\lambda (H20: (ex3_4 K C C T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u: T).(drop (S n0) O c0 (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i0 (s k (S n0))) v e1 
e2))))))).(ex3_4_ind K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(eq C e (CHead e1 k u0)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u0: T).(drop (S n0) O c0 (CHead e2 k u0)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus i0 (s k (S n0))) v e1 e2))))) (or4 (drop (S n0) O (CHead c0 (Flat f) 
t) e) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C e (CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) 
(CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda 
(w: T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C 
T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e 
(CHead e1 k u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k u0)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C e (CHead e1 k u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) 
(CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (w: T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u0 
w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2)))))))) (\lambda (x0: K).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: 
T).(\lambda (H21: (eq C e (CHead x1 x0 x3))).(\lambda (H22: (drop (S n0) O c0 
(CHead x2 x0 x3))).(\lambda (H23: (csubst0 (minus i0 (s x0 (S n0))) v x1 
x2)).(eq_ind_r C (CHead x1 x0 x3) (\lambda (c: C).(or4 (drop (S n0) O (CHead 
c0 (Flat f) t) c) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C c (CHead e0 k u0)))))) (\lambda (k: K).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) 
(CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda 
(w: T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C 
T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C c 
(CHead e1 k u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k u0)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C c (CHead e1 k u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) 
(CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (w: T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u0 
w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2))))))))) (or4_intro2 (drop (S n0) O (CHead c0 (Flat f) t) (CHead x1 x0 
x3)) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C (CHead x1 x0 x3) (CHead e0 k u0)))))) (\lambda (k: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 
(Flat f) t) (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) 
(ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: 
T).(eq C (CHead x1 x0 x3) (CHead e1 k u0)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u0: T).(drop (S n0) O (CHead c0 (Flat f) t) 
(CHead e2 k u0)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead x1 x0 x3) (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2))))))) (ex3_4_intro K C C T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C 
(CHead x1 x0 x3) (CHead e1 k u0)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u0: T).(drop (S n0) O (CHead c0 (Flat f) t) 
(CHead e2 k u0)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 e2))))) 
x0 x1 x2 x3 (refl_equal C (CHead x1 x0 x3)) (drop_drop (Flat f) n0 c0 (CHead 
x2 x0 x3) H22 t) H23)) e H21)))))))) H20)) (\lambda (H20: (ex4_5 K C C T T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i0 (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (s k 
(S n0))) v e1 e2)))))))).(ex4_5_ind K C C T T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c0 (CHead e2 k w))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus i0 (s k (S n0))) v u0 w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (s k 
(S n0))) v e1 e2)))))) (or4 (drop (S n0) O (CHead c0 (Flat f) t) e) (ex3_4 K 
C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C 
e (CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 k 
u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k u0)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2)))))))) (\lambda (x0: 
K).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: 
T).(\lambda (H21: (eq C e (CHead x1 x0 x3))).(\lambda (H22: (drop (S n0) O c0 
(CHead x2 x0 x4))).(\lambda (H23: (subst0 (minus i0 (s x0 (S n0))) v x3 
x4)).(\lambda (H24: (csubst0 (minus i0 (s x0 (S n0))) v x1 x2)).(eq_ind_r C 
(CHead x1 x0 x3) (\lambda (c: C).(or4 (drop (S n0) O (CHead c0 (Flat f) t) c) 
(ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: 
T).(eq C c (CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C c (CHead e1 k 
u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k u0)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C c (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2))))))))) (or4_intro3 (drop (S 
n0) O (CHead c0 (Flat f) t) (CHead x1 x0 x3)) (ex3_4 K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead x1 x0 x3) 
(CHead e0 k u0)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C (CHead x1 x0 x3) 
(CHead e1 k u0)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k u0)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda 
(k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C (CHead x1 x0 x3) (CHead e1 k u0))))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 
(Flat f) t) (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 (minus (s (Flat f) i0) (s k (S 
n0))) v u0 w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2))))))) (ex4_5_intro K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead x1 x0 x3) (CHead e1 k 
u0))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) t) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u0 w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2)))))) x0 x1 x2 x3 x4 (refl_equal 
C (CHead x1 x0 x3)) (drop_drop (Flat f) n0 c0 (CHead x2 x0 x4) H22 t) H23 
H24)) e H21)))))))))) H20)) H19)))))) k (drop_gen_drop k c e t n0 H2) H17 
H18))))) c2 H15)) u (sym_eq T u t H14))) k0 (sym_eq K k0 k H13))) c1 (sym_eq 
C c1 c H12))) H11)) H10))) v0 (sym_eq T v0 v H8))) i H4 H5 H6 H7 H3))))) | 
(csubst0_both k0 i0 v0 u1 u2 H3 c1 c0 H4) \Rightarrow (\lambda (H5: (eq nat 
(s k0 i0) i)).(\lambda (H6: (eq T v0 v)).(\lambda (H7: (eq C (CHead c1 k0 u1) 
(CHead c k t))).(\lambda (H8: (eq C (CHead c0 k0 u2) c2)).(eq_ind nat (s k0 
i0) (\lambda (n: nat).((eq T v0 v) \to ((eq C (CHead c1 k0 u1) (CHead c k t)) 
\to ((eq C (CHead c0 k0 u2) c2) \to ((subst0 i0 v0 u1 u2) \to ((csubst0 i0 v0 
c1 c0) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T (\lambda (k: K).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k u)))))) (\lambda 
(k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 
(CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 (minus n (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k 
u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O c2 (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus n (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O c2 (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus n (s k (S n0))) v u w)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus n (s k (S n0))) v e1 e2)))))))))))))) (\lambda (H9: 
(eq T v0 v)).(eq_ind T v (\lambda (t0: T).((eq C (CHead c1 k0 u1) (CHead c k 
t)) \to ((eq C (CHead c0 k0 u2) c2) \to ((subst0 i0 t0 u1 u2) \to ((csubst0 
i0 t0 c1 c0) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k 
u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k0 i0) (s k (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k u)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s k0 i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s k0 i0) (s k (S n0))) v u w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s k0 i0) (s k (S n0))) v e1 e2))))))))))))) (\lambda (H10: (eq C 
(CHead c1 k0 u1) (CHead c k t))).(let H11 \def (f_equal C T (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u1 | 
(CHead _ _ t) \Rightarrow t])) (CHead c1 k0 u1) (CHead c k t) H10) in ((let 
H12 \def (f_equal C K (\lambda (e0: C).(match e0 in C return (\lambda (_: 
C).K) with [(CSort _) \Rightarrow k0 | (CHead _ k _) \Rightarrow k])) (CHead 
c1 k0 u1) (CHead c k t) H10) in ((let H13 \def (f_equal C C (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow c1 | 
(CHead c _ _) \Rightarrow c])) (CHead c1 k0 u1) (CHead c k t) H10) in (eq_ind 
C c (\lambda (c: C).((eq K k0 k) \to ((eq T u1 t) \to ((eq C (CHead c0 k0 u2) 
c2) \to ((subst0 i0 v u1 u2) \to ((csubst0 i0 v c c0) \to (or4 (drop (S n0) O 
c2 e) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s k0 i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k 
u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O c2 (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s k0 i0) (s k (S n0))) v 
e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O c2 (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k0 i0) (s k (S n0))) v u 
w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus (s k0 i0) (s k (S n0))) v e1 
e2)))))))))))))) (\lambda (H14: (eq K k0 k)).(eq_ind K k (\lambda (k: K).((eq 
T u1 t) \to ((eq C (CHead c0 k u2) c2) \to ((subst0 i0 v u1 u2) \to ((csubst0 
i0 v c c0) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T (\lambda (k1: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k1 
u)))))) (\lambda (k1: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c2 (CHead e0 k1 w)))))) (\lambda (k1: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k i0) (s k1 (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k1: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 k1 u)))))) (\lambda (k1: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k1 u)))))) 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s k i0) (s k1 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k1: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k1 u))))))) (\lambda (k1: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k1 w))))))) 
(\lambda (k1: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s k i0) (s k1 (S n0))) v u w)))))) (\lambda (k1: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s k i0) (s k1 (S n0))) v e1 e2))))))))))))) (\lambda (H15: (eq T u1 
t)).(eq_ind T t (\lambda (t: T).((eq C (CHead c0 k u2) c2) \to ((subst0 i0 v 
t u2) \to ((csubst0 i0 v c c0) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k1: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k i0) (s k1 (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k u)))))) 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s k i0) (s k1 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) 
(\lambda (k1: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s k i0) (s k1 (S n0))) v u w)))))) (\lambda (k1: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s k i0) (s k1 (S n0))) v e1 e2)))))))))))) (\lambda (H16: (eq C 
(CHead c0 k u2) c2)).(eq_ind C (CHead c0 k u2) (\lambda (c2: C).((subst0 i0 v 
t u2) \to ((csubst0 i0 v c c0) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k1: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k i0) (s k1 (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k u)))))) 
(\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s k i0) (s k1 (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) 
(\lambda (k1: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s k i0) (s k1 (S n0))) v u w)))))) (\lambda (k1: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s k i0) (s k1 (S n0))) v e1 e2))))))))))) (\lambda (_: (subst0 i0 v t 
u2)).(\lambda (H18: (csubst0 i0 v c c0)).(let H1 \def (eq_ind K k0 (\lambda 
(k: K).(eq nat (s k i0) i)) H5 k H14) in (let H19 \def (eq_ind_r nat i 
(\lambda (n: nat).(\forall (c2: C).(\forall (v: T).((csubst0 n v c c2) \to 
(\forall (e: C).((drop (S n0) O c e) \to (or4 (drop (S n0) O c2 e) (ex3_4 K C 
T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus n (s k (S n0))) v u w)))))) 
(ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O c2 (CHead e2 k u)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus n (s k 
(S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus n (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus n (s k (S n0))) v e1 
e2)))))))))))))) H0 (s k i0) H1) in (let H20 \def (eq_ind_r nat i (\lambda 
(n: nat).(lt (S n0) n)) H (s k i0) H1) in (K_ind (\lambda (k: K).((drop (r k 
n0) O c e) \to (((\forall (c2: C).(\forall (v: T).((csubst0 (s k i0) v c c2) 
\to (\forall (e: C).((drop (S n0) O c e) \to (or4 (drop (S n0) O c2 e) (ex3_4 
K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k0: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k i0) (s 
k0 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead 
e2 k u)))))) (\lambda (k0: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s k i0) (s k0 (S n0))) v e1 e2)))))) (ex4_5 K C C T T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k w))))))) 
(\lambda (k0: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s k i0) (s k0 (S n0))) v u w)))))) (\lambda (k0: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s k i0) (s k0 (S n0))) v e1 e2)))))))))))))) \to ((lt (S n0) (s k 
i0)) \to (or4 (drop (S n0) O (CHead c0 k u2) e) (ex3_4 K C T T (\lambda (k1: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k1 
u)))))) (\lambda (k1: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead c0 k u2) (CHead e0 k1 w)))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k i0) (s 
k1 (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k1: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k1 u)))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c0 
k u2) (CHead e2 k1 u)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s k i0) (s k1 (S n0))) v e1 e2)))))) 
(ex4_5 K C C T T (\lambda (k1: K).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e1 k1 u))))))) (\lambda (k1: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c0 k u2) (CHead e2 k1 w))))))) (\lambda (k1: K).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s k i0) (s 
k1 (S n0))) v u w)))))) (\lambda (k1: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s k i0) (s k1 (S n0))) v 
e1 e2)))))))))))) (\lambda (b: B).(\lambda (H2: (drop (r (Bind b) n0) O c 
e)).(\lambda (_: ((\forall (c2: C).(\forall (v: T).((csubst0 (s (Bind b) i0) 
v c c2) \to (\forall (e: C).((drop (S n0) O c e) \to (or4 (drop (S n0) O c2 
e) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead 
e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T 
T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k 
w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u w)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2))))))))))))))).(\lambda (H: (lt (S n0) (s (Bind b) i0))).(let H21 \def 
(IHn i0 (le_S_n (S n0) i0 H) c c0 v H18 e H2) in (or4_ind (drop n0 O c0 e) 
(ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop n0 O c0 (CHead e0 k w)))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i0 (s k n0)) v u 
w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop n0 O c0 (CHead e2 k u)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus i0 (s k n0)) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop n0 O c0 (CHead e2 k w))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus i0 (s k n0)) v u w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (s k n0)) v e1 
e2))))))) (or4 (drop (S n0) O (CHead c0 (Bind b) u2) e) (ex3_4 K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O (CHead c0 (Bind b) u2) (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c0 
(Bind b) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c0 (Bind b) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s 
(Bind b) i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) i0) (s k (S n0))) v e1 e2)))))))) (\lambda (H22: (drop n0 O c0 
e)).(or4_intro0 (drop (S n0) O (CHead c0 (Bind b) u2) e) (ex3_4 K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O (CHead c0 (Bind b) u2) (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c0 
(Bind b) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c0 (Bind b) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s 
(Bind b) i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) i0) (s k (S n0))) v e1 e2))))))) (drop_drop (Bind b) n0 c0 e H22 u2))) 
(\lambda (H22: (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop n0 O c0 (CHead e0 k w)))))) (\lambda 
(k: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i0 (s k 
n0)) v u w))))))).(ex3_4_ind K C T T (\lambda (k: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k u)))))) (\lambda (k: 
K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O c0 (CHead e0 k 
w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i0 (s k n0)) v u w))))) (or4 (drop (S n0) O (CHead c0 (Bind 
b) u2) e) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) u2) 
(CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u w)))))) (ex3_4 K C C 
T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u: T).(drop (S n0) O (CHead c0 (Bind b) u2) (CHead e2 k u)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) u2) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2)))))))) (\lambda (x0: 
K).(\lambda (x1: C).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H23: (eq C e 
(CHead x1 x0 x2))).(\lambda (H24: (drop n0 O c0 (CHead x1 x0 x3))).(\lambda 
(H25: (subst0 (minus i0 (s x0 n0)) v x2 x3)).(eq_ind_r C (CHead x1 x0 x2) 
(\lambda (c: C).(or4 (drop (S n0) O (CHead c0 (Bind b) u2) c) (ex3_4 K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O (CHead c0 (Bind b) u2) (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c0 
(Bind b) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c0 (Bind b) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s 
(Bind b) i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) i0) (s k (S n0))) v e1 e2))))))))) (or4_intro1 (drop (S n0) O (CHead c0 
(Bind b) u2) (CHead x1 x0 x2)) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 x0 x2) (CHead e0 k u)))))) 
(\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) 
O (CHead c0 (Bind b) u2) (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) i0) (s k (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C (CHead x1 x0 x2) (CHead e1 k u)))))) (\lambda 
(k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead 
c0 (Bind b) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 x0 x2) (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) u2) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2))))))) (ex3_4_intro K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead 
x1 x0 x2) (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) u2) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Bind b) i0) (s k (S n0))) v u w))))) x0 x1 x2 x3 (refl_equal C 
(CHead x1 x0 x2)) (drop_drop (Bind b) n0 c0 (CHead x1 x0 x3) H24 u2) 
(eq_ind_r nat (S (s x0 n0)) (\lambda (n: nat).(subst0 (minus (s (Bind b) i0) 
n) v x2 x3)) H25 (s x0 (S n0)) (s_S x0 n0)))) e H23)))))))) H22)) (\lambda 
(H22: (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop n0 O c0 (CHead e2 k u)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus i0 (s k n0)) v e1 e2))))))).(ex3_4_ind K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k 
u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop n0 O c0 (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i0 (s k n0)) v e1 e2))))) 
(or4 (drop (S n0) O (CHead c0 (Bind b) u2) e) (ex3_4 K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k 
u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead c0 (Bind b) u2) (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c0 
(Bind b) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c0 (Bind b) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s 
(Bind b) i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) i0) (s k (S n0))) v e1 e2)))))))) (\lambda (x0: K).(\lambda (x1: 
C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H23: (eq C e (CHead x1 x0 
x3))).(\lambda (H24: (drop n0 O c0 (CHead x2 x0 x3))).(\lambda (H25: (csubst0 
(minus i0 (s x0 n0)) v x1 x2)).(eq_ind_r C (CHead x1 x0 x3) (\lambda (c: 
C).(or4 (drop (S n0) O (CHead c0 (Bind b) u2) c) (ex3_4 K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e0 k 
u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead c0 (Bind b) u2) (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c0 
(Bind b) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c0 (Bind b) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s 
(Bind b) i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) i0) (s k (S n0))) v e1 e2))))))))) (or4_intro2 (drop (S n0) O (CHead c0 
(Bind b) u2) (CHead x1 x0 x3)) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 x0 x3) (CHead e0 k u)))))) 
(\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) 
O (CHead c0 (Bind b) u2) (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) i0) (s k (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C (CHead x1 x0 x3) (CHead e1 k u)))))) (\lambda 
(k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead 
c0 (Bind b) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 x0 x3) (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) u2) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2))))))) (ex3_4_intro K C C T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead 
x1 x0 x3) (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead c0 (Bind b) u2) (CHead e2 k u)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2))))) x0 x1 x2 x3 (refl_equal C 
(CHead x1 x0 x3)) (drop_drop (Bind b) n0 c0 (CHead x2 x0 x3) H24 u2) 
(eq_ind_r nat (S (s x0 n0)) (\lambda (n: nat).(csubst0 (minus (s (Bind b) i0) 
n) v x1 x2)) H25 (s x0 (S n0)) (s_S x0 n0)))) e H23)))))))) H22)) (\lambda 
(H22: (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop n0 
O c0 (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i0 (s k n0)) v u w)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i0 (s k n0)) v e1 e2)))))))).(ex4_5_ind K C C T T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop n0 O c0 (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i0 (s k n0)) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (s k 
n0)) v e1 e2)))))) (or4 (drop (S n0) O (CHead c0 (Bind b) u2) e) (ex3_4 K C T 
T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O (CHead c0 (Bind b) u2) (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c0 
(Bind b) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c0 (Bind b) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s 
(Bind b) i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) i0) (s k (S n0))) v e1 e2)))))))) (\lambda (x0: K).(\lambda (x1: 
C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: T).(\lambda (H23: (eq C e 
(CHead x1 x0 x3))).(\lambda (H24: (drop n0 O c0 (CHead x2 x0 x4))).(\lambda 
(H25: (subst0 (minus i0 (s x0 n0)) v x3 x4)).(\lambda (H26: (csubst0 (minus 
i0 (s x0 n0)) v x1 x2)).(eq_ind_r C (CHead x1 x0 x3) (\lambda (c: C).(or4 
(drop (S n0) O (CHead c0 (Bind b) u2) c) (ex3_4 K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e0 k 
u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead c0 (Bind b) u2) (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) 
i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c0 
(Bind b) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c0 (Bind b) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s 
(Bind b) i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Bind 
b) i0) (s k (S n0))) v e1 e2))))))))) (or4_intro3 (drop (S n0) O (CHead c0 
(Bind b) u2) (CHead x1 x0 x3)) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 x0 x3) (CHead e0 k u)))))) 
(\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) 
O (CHead c0 (Bind b) u2) (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) i0) (s k (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C (CHead x1 x0 x3) (CHead e1 k u)))))) (\lambda 
(k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead 
c0 (Bind b) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 x0 x3) (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Bind b) u2) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s (Bind b) i0) (s k (S n0))) v u w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Bind b) i0) (s k (S n0))) v e1 e2))))))) (ex4_5_intro K C C T T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C (CHead x1 x0 x3) (CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 
(Bind b) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Bind b) i0) (s k (S 
n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Bind b) i0) (s k (S n0))) v e1 
e2)))))) x0 x1 x2 x3 x4 (refl_equal C (CHead x1 x0 x3)) (drop_drop (Bind b) 
n0 c0 (CHead x2 x0 x4) H24 u2) (eq_ind_r nat (S (s x0 n0)) (\lambda (n: 
nat).(subst0 (minus (s (Bind b) i0) n) v x3 x4)) H25 (s x0 (S n0)) (s_S x0 
n0)) (eq_ind_r nat (S (s x0 n0)) (\lambda (n: nat).(csubst0 (minus (s (Bind 
b) i0) n) v x1 x2)) H26 (s x0 (S n0)) (s_S x0 n0)))) e H23)))))))))) H22)) 
H21)))))) (\lambda (f: F).(\lambda (H2: (drop (r (Flat f) n0) O c 
e)).(\lambda (H0: ((\forall (c2: C).(\forall (v: T).((csubst0 (s (Flat f) i0) 
v c c2) \to (\forall (e: C).((drop (S n0) O c e) \to (or4 (drop (S n0) O c2 
e) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) 
i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c2 (CHead 
e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T 
T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead e2 k 
w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u w)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2))))))))))))))).(\lambda (_: (lt (S n0) (s (Flat f) i0))).(let H21 \def (H0 
c0 v H18 e H2) in (or4_ind (drop (S n0) O c0 e) (ex3_4 K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k 
u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c0 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i0 (s k (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c0 (CHead e2 k u)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus i0 (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i0 (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (s k 
(S n0))) v e1 e2))))))) (or4 (drop (S n0) O (CHead c0 (Flat f) u2) e) (ex3_4 
K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) u2) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k 
u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O (CHead c0 (Flat f) u2) (CHead e2 k u)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) i0) (s k (S n0))) v e1 e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) u2) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2)))))))) (\lambda (H22: (drop (S 
n0) O c0 e)).(or4_intro0 (drop (S n0) O (CHead c0 (Flat f) u2) e) (ex3_4 K C 
T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O (CHead c0 (Flat f) u2) (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) 
i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c0 
(Flat f) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c0 (Flat f) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s 
(Flat f) i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) i0) (s k (S n0))) v e1 e2))))))) (drop_drop (Flat f) n0 c0 e H22 u2))) 
(\lambda (H22: (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus i0 (s k (S n0))) v u w))))))).(ex3_4_ind K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k 
u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O c0 (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i0 (s k (S n0))) v u w))))) 
(or4 (drop (S n0) O (CHead c0 (Flat f) u2) e) (ex3_4 K C T T (\lambda (k: 
K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k 
u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead c0 (Flat f) u2) (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) 
i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c0 
(Flat f) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c0 (Flat f) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s 
(Flat f) i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) i0) (s k (S n0))) v e1 e2)))))))) (\lambda (x0: K).(\lambda (x1: 
C).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H23: (eq C e (CHead x1 x0 
x2))).(\lambda (H24: (drop (S n0) O c0 (CHead x1 x0 x3))).(\lambda (H25: 
(subst0 (minus i0 (s x0 (S n0))) v x2 x3)).(eq_ind_r C (CHead x1 x0 x2) 
(\lambda (c: C).(or4 (drop (S n0) O (CHead c0 (Flat f) u2) c) (ex3_4 K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O (CHead c0 (Flat f) u2) (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) 
i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c0 
(Flat f) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c0 (Flat f) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s 
(Flat f) i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) i0) (s k (S n0))) v e1 e2))))))))) (or4_intro1 (drop (S n0) O (CHead c0 
(Flat f) u2) (CHead x1 x0 x2)) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 x0 x2) (CHead e0 k u)))))) 
(\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) 
O (CHead c0 (Flat f) u2) (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) i0) (s k (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C (CHead x1 x0 x2) (CHead e1 k u)))))) (\lambda 
(k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead 
c0 (Flat f) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 x0 x2) (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) u2) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2))))))) (ex3_4_intro K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead 
x1 x0 x2) (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) u2) (CHead e0 k w)))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus (s (Flat f) i0) (s k (S n0))) v u w))))) x0 x1 x2 x3 (refl_equal C 
(CHead x1 x0 x2)) (drop_drop (Flat f) n0 c0 (CHead x1 x0 x3) H24 u2) H25)) e 
H23)))))))) H22)) (\lambda (H22: (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c0 (CHead 
e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus i0 (s k (S n0))) v e1 e2))))))).(ex3_4_ind K C C T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u: T).(drop (S n0) O c0 (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i0 (s k (S n0))) v e1 
e2))))) (or4 (drop (S n0) O (CHead c0 (Flat f) u2) e) (ex3_4 K C T T (\lambda 
(k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k 
u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (S n0) O (CHead c0 (Flat f) u2) (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) 
i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c0 
(Flat f) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c0 (Flat f) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s 
(Flat f) i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) i0) (s k (S n0))) v e1 e2)))))))) (\lambda (x0: K).(\lambda (x1: 
C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H23: (eq C e (CHead x1 x0 
x3))).(\lambda (H24: (drop (S n0) O c0 (CHead x2 x0 x3))).(\lambda (H25: 
(csubst0 (minus i0 (s x0 (S n0))) v x1 x2)).(eq_ind_r C (CHead x1 x0 x3) 
(\lambda (c: C).(or4 (drop (S n0) O (CHead c0 (Flat f) u2) c) (ex3_4 K C T T 
(\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O (CHead c0 (Flat f) u2) (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) 
i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c0 
(Flat f) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c0 (Flat f) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s 
(Flat f) i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) i0) (s k (S n0))) v e1 e2))))))))) (or4_intro2 (drop (S n0) O (CHead c0 
(Flat f) u2) (CHead x1 x0 x3)) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 x0 x3) (CHead e0 k u)))))) 
(\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) 
O (CHead c0 (Flat f) u2) (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) i0) (s k (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C (CHead x1 x0 x3) (CHead e1 k u)))))) (\lambda 
(k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead 
c0 (Flat f) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 x0 x3) (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) u2) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2))))))) (ex3_4_intro K C C T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead 
x1 x0 x3) (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O (CHead c0 (Flat f) u2) (CHead e2 k u)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2))))) x0 x1 x2 x3 (refl_equal C 
(CHead x1 x0 x3)) (drop_drop (Flat f) n0 c0 (CHead x2 x0 x3) H24 u2) H25)) e 
H23)))))))) H22)) (\lambda (H22: (ex4_5 K C C T T (\lambda (k: K).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c0 (CHead e2 k w))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus i0 (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i0 (s k (S n0))) v e1 
e2)))))))).(ex4_5_ind K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O c0 (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i0 (s k (S n0))) v u 
w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i0 (s k (S n0))) v e1 e2)))))) (or4 (drop 
(S n0) O (CHead c0 (Flat f) u2) e) (ex3_4 K C T T (\lambda (k: K).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 k u)))))) (\lambda 
(k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead 
c0 (Flat f) u2) (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u 
w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c0 (Flat f) u2) 
(CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c0 (Flat f) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s 
(Flat f) i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) i0) (s k (S n0))) v e1 e2)))))))) (\lambda (x0: K).(\lambda (x1: 
C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: T).(\lambda (H23: (eq C e 
(CHead x1 x0 x3))).(\lambda (H24: (drop (S n0) O c0 (CHead x2 x0 
x4))).(\lambda (H25: (subst0 (minus i0 (s x0 (S n0))) v x3 x4)).(\lambda 
(H26: (csubst0 (minus i0 (s x0 (S n0))) v x1 x2)).(eq_ind_r C (CHead x1 x0 
x3) (\lambda (c: C).(or4 (drop (S n0) O (CHead c0 (Flat f) u2) c) (ex3_4 K C 
T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c 
(CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O (CHead c0 (Flat f) u2) (CHead e0 k w)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) 
i0) (s k (S n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 k u)))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead c0 
(Flat f) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O (CHead c0 (Flat f) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s 
(Flat f) i0) (s k (S n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus (s (Flat 
f) i0) (s k (S n0))) v e1 e2))))))))) (or4_intro3 (drop (S n0) O (CHead c0 
(Flat f) u2) (CHead x1 x0 x3)) (ex3_4 K C T T (\lambda (k: K).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 x0 x3) (CHead e0 k u)))))) 
(\lambda (k: K).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) 
O (CHead c0 (Flat f) u2) (CHead e0 k w)))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) i0) (s k (S 
n0))) v u w)))))) (ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C (CHead x1 x0 x3) (CHead e1 k u)))))) (\lambda 
(k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O (CHead 
c0 (Flat f) u2) (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 x0 x3) (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O (CHead c0 (Flat f) u2) (CHead e2 k w))))))) 
(\lambda (k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus (s (Flat f) i0) (s k (S n0))) v u w)))))) (\lambda (k: 
K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus (s (Flat f) i0) (s k (S n0))) v e1 e2))))))) (ex4_5_intro K C C T T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C (CHead x1 x0 x3) (CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O (CHead c0 
(Flat f) u2) (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus (s (Flat f) i0) (s k (S 
n0))) v u w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus (s (Flat f) i0) (s k (S n0))) v e1 
e2)))))) x0 x1 x2 x3 x4 (refl_equal C (CHead x1 x0 x3)) (drop_drop (Flat f) 
n0 c0 (CHead x2 x0 x4) H24 u2) H25 H26)) e H23)))))))))) H22)) H21)))))) k 
(drop_gen_drop k c e t n0 H2) H19 H20)))))) c2 H16)) u1 (sym_eq T u1 t H15))) 
k0 (sym_eq K k0 k H14))) c1 (sym_eq C c1 c H13))) H12)) H11))) v0 (sym_eq T 
v0 v H9))) i H5 H6 H7 H8 H3 H4)))))]) in (H3 (refl_equal nat i) (refl_equal T 
v) (refl_equal C (CHead c k t)) (refl_equal C c2)))))))))))) c1)))))) n).

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
(or4 (drop O O c2 c1) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c1 (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop O O c2 
(CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c1 (CHead e1 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop O O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C c1 (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop O O c2 (CHead e2 
(Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (y: nat).(\lambda (H1: (csubst0 y v c1 c2)).(csubst0_ind 
(\lambda (n0: nat).(\lambda (t: T).(\lambda (c: C).(\lambda (c0: C).((eq nat 
n0 O) \to (or4 (drop O O c0 c) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop O O c0 
(CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O t u w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop O O c0 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O t e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C c (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop O O c0 (CHead e2 
(Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O t u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O t e1 
e2))))))))))))) (\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: 
nat).(\forall (v0: T).(\forall (u1: T).(\forall (u2: T).((subst0 i v0 u1 u2) 
\to (\forall (c: C).((eq nat (s k0 i) O) \to (or4 (drop O O (CHead c k0 u2) 
(CHead c k0 u1)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead c k0 u1) (CHead e0 (Flat f) u)))))) (\lambda 
(f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop O O (CHead c k0 
u2) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v0 u w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead c k0 u1) 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop O O (CHead c k0 u2) (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c k0 u1) (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop O O (CHead c k0 u2) (CHead e2 (Flat f) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v0 u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 e2)))))))))))))))) 
(\lambda (b: B).(\lambda (i: nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda 
(u2: T).(\lambda (_: (subst0 i v0 u1 u2)).(\lambda (c: C).(\lambda (H3: (eq 
nat (S i) O)).(let H4 \def (eq_ind nat (S i) (\lambda (ee: nat).(match ee in 
nat return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) 
\Rightarrow True])) I O H3) in (False_ind (or4 (drop O O (CHead c (Bind b) 
u2) (CHead c (Bind b) u1)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c (Bind b) u1) (CHead e0 
(Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop O O (CHead c (Bind b) u2) (CHead e0 (Flat f) w)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v0 u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C (CHead c (Bind b) u1) (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop O O (CHead c (Bind 
b) u2) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead c (Bind b) u1) (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop O O (CHead c 
(Bind b) u2) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v0 u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v0 e1 e2)))))))) H4)))))))))) (\lambda (f: F).(\lambda (i: 
nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H2: (subst0 
i v0 u1 u2)).(\lambda (c: C).(\lambda (H3: (eq nat i O)).(let H4 \def (eq_ind 
nat i (\lambda (n: nat).(subst0 n v0 u1 u2)) H2 O H3) in (or4_intro1 (drop O 
O (CHead c (Flat f) u2) (CHead c (Flat f) u1)) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c (Flat f) 
u1) (CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop O O (CHead c (Flat f) u2) (CHead e0 (Flat f0) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v0 u w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead c (Flat f) u1) (CHead e1 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u: T).(drop O O (CHead c (Flat f) u2) (CHead e2 (Flat f0) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v0 e1 
e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c (Flat f) u1) (CHead e1 
(Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop O O (CHead c (Flat f) u2) (CHead e2 (Flat f0) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v0 u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 
e2))))))) (ex3_4_intro F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead c (Flat f) u1) (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop O O 
(CHead c (Flat f) u2) (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v0 u w))))) f c u1 u2 
(refl_equal C (CHead c (Flat f) u1)) (drop_refl (CHead c (Flat f) u2)) 
H4))))))))))) k)) (\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: 
nat).(\forall (c3: C).(\forall (c4: C).(\forall (v0: T).((csubst0 i v0 c3 c4) 
\to ((((eq nat i O) \to (or4 (drop O O c4 c3) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e0 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop O O c4 (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v0 u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c3 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop O O c4 (CHead e2 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v0 e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e1 (Flat f) u))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop O O c4 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v0 u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v0 e1 e2)))))))))) \to (\forall (u: T).((eq nat (s k0 i) O) 
\to (or4 (drop O O (CHead c4 k0 u) (CHead c3 k0 u)) (ex3_4 F C T T (\lambda 
(f: F).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead c3 k0 
u) (CHead e0 (Flat f) u0)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop O O (CHead c4 k0 u) (CHead e0 (Flat f) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v0 
u0 w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(eq C (CHead c3 k0 u) (CHead e1 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop O O 
(CHead c4 k0 u) (CHead e2 (Flat f) u0)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T 
T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda 
(_: T).(eq C (CHead c3 k0 u) (CHead e1 (Flat f) u0))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop O O 
(CHead c4 k0 u) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v0 u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v0 e1 e2))))))))))))))))) (\lambda (b: B).(\lambda (i: 
nat).(\lambda (c3: C).(\lambda (c4: C).(\lambda (v0: T).(\lambda (_: (csubst0 
i v0 c3 c4)).(\lambda (_: (((eq nat i O) \to (or4 (drop O O c4 c3) (ex3_4 F C 
T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 
(CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop O O c4 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v0 u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c3 (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop O O c4 (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e1 (Flat f) u))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop O O c4 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v0 u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v0 e1 e2))))))))))).(\lambda (u: T).(\lambda (H4: (eq nat 
(S i) O)).(let H5 \def (eq_ind nat (S i) (\lambda (ee: nat).(match ee in nat 
return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow 
True])) I O H4) in (False_ind (or4 (drop O O (CHead c4 (Bind b) u) (CHead c3 
(Bind b) u)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C (CHead c3 (Bind b) u) (CHead e0 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop O O 
(CHead c4 (Bind b) u) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v0 u0 w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C 
(CHead c3 (Bind b) u) (CHead e1 (Flat f) u0)))))) (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u0: T).(drop O O (CHead c4 (Bind b) u) 
(CHead e2 (Flat f) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C 
(CHead c3 (Bind b) u) (CHead e1 (Flat f) u0))))))) (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop O O (CHead c4 
(Bind b) u) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v0 u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v0 e1 e2)))))))) H5))))))))))) (\lambda (f: F).(\lambda (i: 
nat).(\lambda (c3: C).(\lambda (c4: C).(\lambda (v0: T).(\lambda (H2: 
(csubst0 i v0 c3 c4)).(\lambda (H3: (((eq nat i O) \to (or4 (drop O O c4 c3) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C c3 (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop O O c4 (CHead e0 (Flat f) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v0 
u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c3 (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop O O c4 (CHead e2 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e1 
(Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop O O c4 (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v0 u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v0 e1 e2))))))))))).(\lambda (u: T).(\lambda 
(H4: (eq nat i O)).(let H5 \def (eq_ind nat i (\lambda (n: nat).((eq nat n O) 
\to (or4 (drop O O c4 c3) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop O O c4 
(CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v0 u w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c3 (CHead e1 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop O O c4 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T 
T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C c3 (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop O O c4 (CHead e2 
(Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v0 u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 
e2)))))))))) H3 O H4) in (let H6 \def (eq_ind nat i (\lambda (n: 
nat).(csubst0 n v0 c3 c4)) H2 O H4) in (or4_intro2 (drop O O (CHead c4 (Flat 
f) u) (CHead c3 (Flat f) u)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead c3 (Flat f) u) (CHead e0 
(Flat f0) u0)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop O O (CHead c4 (Flat f) u) (CHead e0 (Flat f0) w)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v0 u0 
w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(eq C (CHead c3 (Flat f) u) (CHead e1 (Flat f0) u0)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop O O 
(CHead c4 (Flat f) u) (CHead e2 (Flat f0) u0)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C (CHead c3 (Flat f) u) (CHead e1 (Flat f0) u0))))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(drop O O (CHead c4 (Flat f) u) (CHead e2 (Flat f0) w))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 O v0 u0 w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 e2))))))) (ex3_4_intro F 
C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq 
C (CHead c3 (Flat f) u) (CHead e1 (Flat f0) u0)))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop O O (CHead c4 
(Flat f) u) (CHead e2 (Flat f0) u0)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v0 e1 e2))))) f c3 c4 u 
(refl_equal C (CHead c3 (Flat f) u)) (drop_refl (CHead c4 (Flat f) u)) 
H6))))))))))))) k)) (\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: 
nat).(\forall (v0: T).(\forall (u1: T).(\forall (u2: T).((subst0 i v0 u1 u2) 
\to (\forall (c3: C).(\forall (c4: C).((csubst0 i v0 c3 c4) \to ((((eq nat i 
O) \to (or4 (drop O O c4 c3) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop O O c4 
(CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v0 u w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c3 (CHead e1 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop O O c4 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T 
T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C c3 (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop O O c4 (CHead e2 
(Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v0 u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 
e2)))))))))) \to ((eq nat (s k0 i) O) \to (or4 (drop O O (CHead c4 k0 u2) 
(CHead c3 k0 u1)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C (CHead c3 k0 u1) (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop O O 
(CHead c4 k0 u2) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v0 u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead 
c3 k0 u1) (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(drop O O (CHead c4 k0 u2) (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c3 k0 u1) (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop O O (CHead c4 k0 u2) (CHead e2 (Flat f) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v0 u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 e2))))))))))))))))))) 
(\lambda (b: B).(\lambda (i: nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda 
(u2: T).(\lambda (_: (subst0 i v0 u1 u2)).(\lambda (c3: C).(\lambda (c4: 
C).(\lambda (_: (csubst0 i v0 c3 c4)).(\lambda (_: (((eq nat i O) \to (or4 
(drop O O c4 c3) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C c3 (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop O O c4 (CHead e0 
(Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v0 u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c3 (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop O O c4 
(CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 
(CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop O O c4 (CHead e2 (Flat f) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v0 u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 e2))))))))))).(\lambda 
(H5: (eq nat (S i) O)).(let H6 \def (eq_ind nat (S i) (\lambda (ee: 
nat).(match ee in nat return (\lambda (_: nat).Prop) with [O \Rightarrow 
False | (S _) \Rightarrow True])) I O H5) in (False_ind (or4 (drop O O (CHead 
c4 (Bind b) u2) (CHead c3 (Bind b) u1)) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c3 (Bind b) 
u1) (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop O O (CHead c4 (Bind b) u2) (CHead e0 (Flat f) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v0 u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead c3 (Bind b) u1) (CHead e1 
(Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u: T).(drop O O (CHead c4 (Bind b) u2) (CHead e2 (Flat f) u)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v0 e1 
e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead c3 (Bind b) u1) (CHead e1 
(Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop O O (CHead c4 (Bind b) u2) (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v0 u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 
e2)))))))) H6))))))))))))) (\lambda (f: F).(\lambda (i: nat).(\lambda (v0: 
T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H2: (subst0 i v0 u1 
u2)).(\lambda (c3: C).(\lambda (c4: C).(\lambda (H3: (csubst0 i v0 c3 
c4)).(\lambda (H4: (((eq nat i O) \to (or4 (drop O O c4 c3) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 
(CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop O O c4 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v0 u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c3 (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop O O c4 (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e1 (Flat f) u))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop O O c4 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v0 u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v0 e1 e2))))))))))).(\lambda (H5: (eq nat i O)).(let H6 
\def (eq_ind nat i (\lambda (n: nat).((eq nat n O) \to (or4 (drop O O c4 c3) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C c3 (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop O O c4 (CHead e0 (Flat f) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v0 
u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C c3 (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop O O c4 (CHead e2 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c3 (CHead e1 
(Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop O O c4 (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v0 u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v0 e1 e2)))))))))) H4 O H5) in (let H7 \def 
(eq_ind nat i (\lambda (n: nat).(csubst0 n v0 c3 c4)) H3 O H5) in (let H8 
\def (eq_ind nat i (\lambda (n: nat).(subst0 n v0 u1 u2)) H2 O H5) in 
(or4_intro3 (drop O O (CHead c4 (Flat f) u2) (CHead c3 (Flat f) u1)) (ex3_4 F 
C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
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
(drop_refl (CHead c4 (Flat f) u2)) H8 H7)))))))))))))))) k)) y v c1 c2 H1))) 
H) e (drop_gen_refl c1 e H0)))))))) (\lambda (n0: nat).(\lambda (IHn: 
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
e)).(let H2 \def (match H0 in csubst0 return (\lambda (n: nat).(\lambda (t0: 
T).(\lambda (c0: C).(\lambda (c1: C).(\lambda (_: (csubst0 n t0 c0 c1)).((eq 
nat n (S n0)) \to ((eq T t0 v) \to ((eq C c0 (CHead c k t)) \to ((eq C c1 c2) 
\to (or4 (drop (S n0) O c2 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) 
O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c2 (CHead 
e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))))))))))) with [(csubst0_snd k0 i v0 u1 u2 H2 c0) \Rightarrow 
(\lambda (H3: (eq nat (s k0 i) (S n0))).(\lambda (H4: (eq T v0 v)).(\lambda 
(H5: (eq C (CHead c0 k0 u1) (CHead c k t))).(\lambda (H6: (eq C (CHead c0 k0 
u2) c2)).((let H7 \def (f_equal nat nat (\lambda (e0: nat).e0) (s k0 i) (S 
n0) H3) in (eq_ind nat (s k0 i) (\lambda (n: nat).((eq T v0 v) \to ((eq C 
(CHead c0 k0 u1) (CHead c k t)) \to ((eq C (CHead c0 k0 u2) c2) \to ((subst0 
i v0 u1 u2) \to (or4 (drop n O c2 e) (ex3_4 F C T T (\lambda (f: F).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n O c2 
(CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop n O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop n O c2 (CHead e2 
(Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))))))) (\lambda (H8: (eq T v0 v)).(eq_ind T v (\lambda (t0: T).((eq 
C (CHead c0 k0 u1) (CHead c k t)) \to ((eq C (CHead c0 k0 u2) c2) \to 
((subst0 i t0 u1 u2) \to (or4 (drop (s k0 i) O c2 e) (ex3_4 F C T T (\lambda 
(f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 
(Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (s k0 i) O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (s k0 i) O c2 (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s k0 i) O c2 (CHead e2 (Flat f) w))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))))))) (\lambda 
(H9: (eq C (CHead c0 k0 u1) (CHead c k t))).(let H10 \def (f_equal C T 
(\lambda (e0: C).(match e0 in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow u1 | (CHead _ _ t) \Rightarrow t])) (CHead c0 k0 u1) (CHead c k 
t) H9) in ((let H11 \def (f_equal C K (\lambda (e0: C).(match e0 in C return 
(\lambda (_: C).K) with [(CSort _) \Rightarrow k0 | (CHead _ k _) \Rightarrow 
k])) (CHead c0 k0 u1) (CHead c k t) H9) in ((let H12 \def (f_equal C C 
(\lambda (e0: C).(match e0 in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow c0 | (CHead c _ _) \Rightarrow c])) (CHead c0 k0 u1) (CHead c k 
t) H9) in (eq_ind C c (\lambda (c: C).((eq K k0 k) \to ((eq T u1 t) \to ((eq 
C (CHead c k0 u2) c2) \to ((subst0 i v u1 u2) \to (or4 (drop (s k0 i) O c2 e) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s k0 i) O c2 (CHead e0 (Flat f) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (s k0 
i) O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s k0 i) O c2 (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))))))) (\lambda (H13: (eq K k0 k)).(eq_ind K k (\lambda (k: K).((eq 
T u1 t) \to ((eq C (CHead c k u2) c2) \to ((subst0 i v u1 u2) \to (or4 (drop 
(s k i) O c2 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s k i) O c2 (CHead 
e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (s k 
i) O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s k i) O c2 (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))))))) (\lambda (H14: (eq T u1 t)).(eq_ind T t (\lambda (t: T).((eq C 
(CHead c k u2) c2) \to ((subst0 i v t u2) \to (or4 (drop (s k i) O c2 e) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s k i) O c2 (CHead e0 (Flat f) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (s k 
i) O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s k i) O c2 (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))))) (\lambda (H15: (eq C (CHead c k u2) c2)).(eq_ind C (CHead c k 
u2) (\lambda (c: C).((subst0 i v t u2) \to (or4 (drop (s k i) O c e) (ex3_4 F 
C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s k i) O c (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (s k i) O c (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s k i) O c (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))))))) (\lambda (H16: (subst0 i v t 
u2)).(let H0 \def (eq_ind K k0 (\lambda (k: K).(eq nat (s k i) (S n0))) H7 k 
H13) in (K_ind (\lambda (k: K).((drop (r k n0) O c e) \to ((eq nat (s k i) (S 
n0)) \to (or4 (drop (s k i) O (CHead c k u2) e) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (s k i) O (CHead c k u2) (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (s k i) O (CHead c k u2) (CHead e2 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 
(Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop (s k i) O (CHead c k u2) (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))))) (\lambda (b: B).(\lambda (H1: (drop (r (Bind b) n0) O c 
e)).(\lambda (H17: (eq nat (s (Bind b) i) (S n0))).(let H18 \def (f_equal nat 
nat (\lambda (e0: nat).(match e0 in nat return (\lambda (_: nat).nat) with [O 
\Rightarrow i | (S n) \Rightarrow n])) (S i) (S n0) H17) in (let H19 \def 
(eq_ind nat i (\lambda (n: nat).(subst0 n v t u2)) H16 n0 H18) in (eq_ind_r 
nat n0 (\lambda (n: nat).(or4 (drop (s (Bind b) n) O (CHead c (Bind b) u2) e) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n) O (CHead c (Bind b) 
u2) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (s (Bind b) n) O (CHead c (Bind b) u2) (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (s (Bind b) n) O (CHead c (Bind b) u2) (CHead e2 (Flat f) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))))) (or4_intro0 
(drop (s (Bind b) n0) O (CHead c (Bind b) u2) e) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (s (Bind b) n0) O (CHead c (Bind b) u2) (CHead e0 (Flat f) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u 
w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (s (Bind b) n0) O 
(CHead c (Bind b) u2) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Bind b) n0) O (CHead c (Bind b) u2) (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (drop_drop (Bind b) n0 c e H1 
u2)) i H18)))))) (\lambda (f: F).(\lambda (H1: (drop (r (Flat f) n0) O c 
e)).(\lambda (H17: (eq nat (s (Flat f) i) (S n0))).(let H18 \def (f_equal nat 
nat (\lambda (e0: nat).e0) i (S n0) H17) in (let H19 \def (eq_ind nat i 
(\lambda (n: nat).(subst0 n v t u2)) H16 (S n0) H18) in (eq_ind_r nat (S n0) 
(\lambda (n: nat).(or4 (drop (s (Flat f) n) O (CHead c (Flat f) u2) e) (ex3_4 
F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (s (Flat f) n) O (CHead c (Flat f) u2) (CHead e0 
(Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (s 
(Flat f) n) O (CHead c (Flat f) u2) (CHead e2 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u))))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Flat f) n) O (CHead c (Flat f) u2) (CHead e2 (Flat f0) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2))))))))) (or4_intro0 (drop (s (Flat f) 
(S n0)) O (CHead c (Flat f) u2) e) (ex3_4 F C T T (\lambda (f0: F).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Flat f) (S n0)) O (CHead c (Flat f) u2) (CHead e0 (Flat f0) w)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (s (Flat f) (S n0)) O (CHead c 
(Flat f) u2) (CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) 
O (CHead c (Flat f) u2) (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (drop_drop (Flat f) n0 c e H1 u2)) i 
H18)))))) k (drop_gen_drop k c e t n0 H1) H0))) c2 H15)) u1 (sym_eq T u1 t 
H14))) k0 (sym_eq K k0 k H13))) c0 (sym_eq C c0 c H12))) H11)) H10))) v0 
(sym_eq T v0 v H8))) (S n0) H7)) H4 H5 H6 H2))))) | (csubst0_fst k0 i c1 c0 
v0 H2 u) \Rightarrow (\lambda (H3: (eq nat (s k0 i) (S n0))).(\lambda (H4: 
(eq T v0 v)).(\lambda (H5: (eq C (CHead c1 k0 u) (CHead c k t))).(\lambda 
(H6: (eq C (CHead c0 k0 u) c2)).((let H7 \def (f_equal nat nat (\lambda (e0: 
nat).e0) (s k0 i) (S n0) H3) in (eq_ind nat (s k0 i) (\lambda (n: nat).((eq T 
v0 v) \to ((eq C (CHead c1 k0 u) (CHead c k t)) \to ((eq C (CHead c0 k0 u) 
c2) \to ((csubst0 i v0 c1 c0) \to (or4 (drop n O c2 e) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e 
(CHead e0 (Flat f) u0)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop n O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: 
T).(eq C e (CHead e1 (Flat f) u0)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u0: T).(drop n O c2 (CHead e2 (Flat f) u0)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u0))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop n O c2 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))))))) (\lambda (H8: (eq T v0 v)).(eq_ind T v 
(\lambda (t0: T).((eq C (CHead c1 k0 u) (CHead c k t)) \to ((eq C (CHead c0 
k0 u) c2) \to ((csubst0 i t0 c1 c0) \to (or4 (drop (s k0 i) O c2 e) (ex3_4 F 
C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C 
e (CHead e0 (Flat f) u0)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s k0 i) O c2 (CHead e0 (Flat f) w)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 
w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(eq C e (CHead e1 (Flat f) u0)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (s k0 i) O c2 
(CHead e2 (Flat f) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e 
(CHead e1 (Flat f) u0))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s k0 i) O c2 (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 O v u0 w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))))))) (\lambda (H9: (eq C (CHead c1 k0 u) (CHead c k t))).(let H10 
\def (f_equal C T (\lambda (e0: C).(match e0 in C return (\lambda (_: C).T) 
with [(CSort _) \Rightarrow u | (CHead _ _ t) \Rightarrow t])) (CHead c1 k0 
u) (CHead c k t) H9) in ((let H11 \def (f_equal C K (\lambda (e0: C).(match 
e0 in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k0 | (CHead _ k 
_) \Rightarrow k])) (CHead c1 k0 u) (CHead c k t) H9) in ((let H12 \def 
(f_equal C C (\lambda (e0: C).(match e0 in C return (\lambda (_: C).C) with 
[(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) (CHead c1 k0 u) 
(CHead c k t) H9) in (eq_ind C c (\lambda (c: C).((eq K k0 k) \to ((eq T u t) 
\to ((eq C (CHead c0 k0 u) c2) \to ((csubst0 i v c c0) \to (or4 (drop (s k0 
i) O c2 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u0)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s k0 i) O c2 
(CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 (Flat 
f) u0)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (s k0 i) O c2 (CHead e2 (Flat f) u0)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u0))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
k0 i) O c2 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))))))) (\lambda (H13: (eq K k0 k)).(eq_ind K 
k (\lambda (k: K).((eq T u t) \to ((eq C (CHead c0 k u) c2) \to ((csubst0 i v 
c c0) \to (or4 (drop (s k i) O c2 e) (ex3_4 F C T T (\lambda (f: F).(\lambda 
(e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s k 
i) O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 (Flat 
f) u0)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (s k i) O c2 (CHead e2 (Flat f) u0)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u0))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
k i) O c2 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))))))))) (\lambda (H14: (eq T u t)).(eq_ind T t 
(\lambda (t: T).((eq C (CHead c0 k t) c2) \to ((csubst0 i v c c0) \to (or4 
(drop (s k i) O c2 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s k 
i) O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 (Flat 
f) u0)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (s k i) O c2 (CHead e2 (Flat f) u0)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u0))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
k i) O c2 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))))) (\lambda (H15: (eq C (CHead c0 k t) 
c2)).(eq_ind C (CHead c0 k t) (\lambda (c2: C).((csubst0 i v c c0) \to (or4 
(drop (s k i) O c2 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s k 
i) O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 (Flat 
f) u0)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (s k i) O c2 (CHead e2 (Flat f) u0)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u0))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
k i) O c2 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))))))) (\lambda (H16: (csubst0 i v c c0)).(let 
H0 \def (eq_ind K k0 (\lambda (k: K).(eq nat (s k i) (S n0))) H7 k H13) in 
(K_ind (\lambda (k: K).((drop (r k n0) O c e) \to ((eq nat (s k i) (S n0)) 
\to (or4 (drop (s k i) O (CHead c0 k t) e) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 (Flat 
f) u0)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (s k i) O (CHead c0 k t) (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: 
T).(eq C e (CHead e1 (Flat f) u0)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u0: T).(drop (s k i) O (CHead c0 k t) (CHead e2 
(Flat f) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 
(Flat f) u0))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop (s k i) O (CHead c0 k t) (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 O v u0 w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))))) (\lambda (b: B).(\lambda (H1: (drop (r (Bind b) n0) O c 
e)).(\lambda (H17: (eq nat (s (Bind b) i) (S n0))).(let H18 \def (f_equal nat 
nat (\lambda (e0: nat).(match e0 in nat return (\lambda (_: nat).nat) with [O 
\Rightarrow i | (S n) \Rightarrow n])) (S i) (S n0) H17) in (let H19 \def 
(eq_ind nat i (\lambda (n: nat).(csubst0 n v c c0)) H16 n0 H18) in (eq_ind_r 
nat n0 (\lambda (n: nat).(or4 (drop (s (Bind b) n) O (CHead c0 (Bind b) t) e) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: 
T).(eq C e (CHead e0 (Flat f) u0)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n) O (CHead c0 (Bind b) 
t) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 (Flat 
f) u0)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (s (Bind b) n) O (CHead c0 (Bind b) t) (CHead e2 (Flat f) u0)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u0))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (s (Bind b) n) O (CHead c0 (Bind b) t) (CHead e2 (Flat f) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 O v u0 w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))))) (let H \def 
(IHn c c0 v H19 e H1) in (or4_ind (drop n0 O c0 e) (ex3_4 F C T T (\lambda 
(f: F).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 
(Flat f) u0)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop n0 O c0 (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e 
(CHead e1 (Flat f) u0)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop n0 O c0 (CHead e2 (Flat f) u0)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u0))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop n0 
O c0 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))) (or4 (drop (s (Bind b) n0) O (CHead c0 (Bind b) t) e) (ex3_4 
F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C e (CHead e0 (Flat f) u0)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead e0 
(Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda 
(w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) t) (CHead e2 (Flat f) u0)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u0))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) t) (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O 
v u0 w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda (H20: (drop n0 O c0 
e)).(or4_intro0 (drop (s (Bind b) n0) O (CHead c0 (Bind b) t) e) (ex3_4 F C T 
T (\lambda (f: F).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e 
(CHead e0 (Flat f) u0)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead e0 
(Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda 
(w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) t) (CHead e2 (Flat f) u0)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u0))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) t) (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O 
v u0 w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (drop_drop (Bind b) n0 c0 e H20 
t))) (\lambda (H20: (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O c0 (CHead e0 
(Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w))))))).(ex3_4_ind F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O 
c0 (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 O v u0 w))))) (or4 (drop (s (Bind b) n0) O (CHead 
c0 (Bind b) t) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u0)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) O 
(CHead c0 (Bind b) t) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e 
(CHead e1 (Flat f) u0)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead e2 
(Flat f) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 
(Flat f) u0))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead 
e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (x0: F).(\lambda (x1: C).(\lambda (x2: T).(\lambda (x3: 
T).(\lambda (H21: (eq C e (CHead x1 (Flat x0) x2))).(\lambda (H22: (drop n0 O 
c0 (CHead x1 (Flat x0) x3))).(\lambda (H23: (subst0 O v x2 x3)).(eq_ind_r C 
(CHead x1 (Flat x0) x2) (\lambda (c: C).(or4 (drop (s (Bind b) n0) O (CHead 
c0 (Bind b) t) c) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C c (CHead e0 (Flat f) u0)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) O 
(CHead c0 (Bind b) t) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C c 
(CHead e1 (Flat f) u0)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead e2 
(Flat f) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C c (CHead e1 
(Flat f) u0))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead 
e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (or4_intro1 (drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead 
x1 (Flat x0) x2)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) x2) (CHead e0 (Flat f) 
u0)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead e0 (Flat f) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v 
u0 w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(eq C (CHead x1 (Flat x0) x2) (CHead e1 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) t) (CHead e2 (Flat f) u0)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) x2) (CHead e1 (Flat f) 
u0))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead e2 
(Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) 
(ex3_4_intro F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) x2) (CHead e0 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) t) (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w))))) x0 
x1 x2 x3 (refl_equal C (CHead x1 (Flat x0) x2)) (drop_drop (Bind b) n0 c0 
(CHead x1 (Flat x0) x3) H22 t) H23)) e H21)))))))) H20)) (\lambda (H20: 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop n0 O c0 (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2))))))).(ex3_4_ind F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u0: T).(eq C e (CHead e1 (Flat f) u0)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop n0 O c0 (CHead e2 
(Flat f) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2))))) (or4 (drop (s (Bind b) n0) O (CHead c0 (Bind 
b) t) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u0)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) O 
(CHead c0 (Bind b) t) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e 
(CHead e1 (Flat f) u0)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead e2 
(Flat f) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 
(Flat f) u0))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead 
e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (x0: F).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: 
T).(\lambda (H21: (eq C e (CHead x1 (Flat x0) x3))).(\lambda (H22: (drop n0 O 
c0 (CHead x2 (Flat x0) x3))).(\lambda (H23: (csubst0 O v x1 x2)).(eq_ind_r C 
(CHead x1 (Flat x0) x3) (\lambda (c: C).(or4 (drop (s (Bind b) n0) O (CHead 
c0 (Bind b) t) c) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C c (CHead e0 (Flat f) u0)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) O 
(CHead c0 (Bind b) t) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C c 
(CHead e1 (Flat f) u0)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead e2 
(Flat f) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C c (CHead e1 
(Flat f) u0))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead 
e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (or4_intro2 (drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead 
x1 (Flat x0) x3)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) x3) (CHead e0 (Flat f) 
u0)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead e0 (Flat f) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v 
u0 w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(eq C (CHead x1 (Flat x0) x3) (CHead e1 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) t) (CHead e2 (Flat f) u0)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) x3) (CHead e1 (Flat f) 
u0))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead e2 
(Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) 
(ex3_4_intro F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(eq C (CHead x1 (Flat x0) x3) (CHead e1 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) t) (CHead e2 (Flat f) u0)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))) 
x0 x1 x2 x3 (refl_equal C (CHead x1 (Flat x0) x3)) (drop_drop (Bind b) n0 c0 
(CHead x2 (Flat x0) x3) H22 t) H23)) e H21)))))))) H20)) (\lambda (H20: 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop n0 
O c0 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2)))))))).(ex4_5_ind F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 (Flat 
f) u0))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop n0 O c0 (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O 
v u0 w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))) (or4 (drop (s (Bind b) n0) O 
(CHead c0 (Bind b) t) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) t) (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: 
T).(eq C e (CHead e1 (Flat f) u0)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u0: T).(drop (s (Bind b) n0) O (CHead c0 (Bind 
b) t) (CHead e2 (Flat f) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C e (CHead e1 (Flat f) u0))))))) (\lambda (f: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 
(Bind b) t) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))))) (\lambda (x0: F).(\lambda (x1: C).(\lambda 
(x2: C).(\lambda (x3: T).(\lambda (x4: T).(\lambda (H21: (eq C e (CHead x1 
(Flat x0) x3))).(\lambda (H22: (drop n0 O c0 (CHead x2 (Flat x0) 
x4))).(\lambda (H23: (subst0 O v x3 x4)).(\lambda (H24: (csubst0 O v x1 
x2)).(eq_ind_r C (CHead x1 (Flat x0) x3) (\lambda (c: C).(or4 (drop (s (Bind 
b) n0) O (CHead c0 (Bind b) t) c) (ex3_4 F C T T (\lambda (f: F).(\lambda 
(e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C c (CHead e0 (Flat f) u0)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) t) (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: 
T).(eq C c (CHead e1 (Flat f) u0)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u0: T).(drop (s (Bind b) n0) O (CHead c0 (Bind 
b) t) (CHead e2 (Flat f) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C c (CHead e1 (Flat f) u0))))))) (\lambda (f: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 
(Bind b) t) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))) (or4_intro3 (drop (s (Bind b) n0) O (CHead 
c0 (Bind b) t) (CHead x1 (Flat x0) x3)) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead x1 (Flat 
x0) x3) (CHead e0 (Flat f) u0)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead 
e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda 
(w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(eq C (CHead x1 (Flat x0) x3) (CHead e1 
(Flat f) u0)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u0: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) t) (CHead e2 (Flat f) 
u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) 
x3) (CHead e1 (Flat f) u0))))))) (\lambda (f: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 
(Bind b) t) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (ex4_5_intro F C C T T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C 
(CHead x1 (Flat x0) x3) (CHead e1 (Flat f) u0))))))) (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) 
O (CHead c0 (Bind b) t) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 
w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))) x0 x1 x2 x3 x4 (refl_equal C 
(CHead x1 (Flat x0) x3)) (drop_drop (Bind b) n0 c0 (CHead x2 (Flat x0) x4) 
H22 t) H23 H24)) e H21)))))))))) H20)) H)) i H18)))))) (\lambda (f: 
F).(\lambda (H1: (drop (r (Flat f) n0) O c e)).(\lambda (H17: (eq nat (s 
(Flat f) i) (S n0))).(let H18 \def (f_equal nat nat (\lambda (e0: nat).e0) i 
(S n0) H17) in (let H19 \def (eq_ind nat i (\lambda (n: nat).(csubst0 n v c 
c0)) H16 (S n0) H18) in (eq_ind_r nat (S n0) (\lambda (n: nat).(or4 (drop (s 
(Flat f) n) O (CHead c0 (Flat f) t) e) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 (Flat 
f0) u0)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (s (Flat f) n) O (CHead c0 (Flat f) t) (CHead e0 (Flat f0) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v 
u0 w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(eq C e (CHead e1 (Flat f0) u0)))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (s (Flat f) n) O 
(CHead c0 (Flat f) t) (CHead e2 (Flat f0) u0)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u0))))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Flat f) n) O (CHead c0 (Flat f) t) (CHead e2 (Flat f0) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O 
v u0 w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2))))))))) (let H20 \def (H c0 v H19 e 
H1) in (or4_ind (drop (S n0) O c0 e) (ex3_4 F C T T (\lambda (f0: F).(\lambda 
(e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u0)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O c0 (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 (Flat 
f0) u0)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (S n0) O c0 (CHead e2 (Flat f0) u0)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u0))))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S 
n0) O c0 (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (or4 (drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) t) e) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u0)))))) (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) 
O (CHead c0 (Flat f) t) (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e 
(CHead e1 (Flat f0) u0)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead 
e2 (Flat f0) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e 
(CHead e1 (Flat f0) u0))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) t) (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))))) (\lambda (H21: (drop (S n0) O c0 
e)).(or4_intro0 (drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) e) (ex3_4 F 
C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq 
C e (CHead e0 (Flat f0) u0)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) 
(CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 (Flat 
f0) u0)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead e2 (Flat f0) 
u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 (Flat 
f0) u0))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead 
e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))) (drop_drop (Flat f) n0 c0 e H21 t))) (\lambda (H21: (ex3_4 F 
C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c0 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u 
w))))))).(ex3_4_ind F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u0: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u0)))))) (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead 
e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 O v u0 w))))) (or4 (drop (s (Flat f) (S n0)) O 
(CHead c0 (Flat f) t) e) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u0)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead e0 (Flat f0) w)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 
w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(eq C e (CHead e1 (Flat f0) u0)))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (s (Flat f) (S 
n0)) O (CHead c0 (Flat f) t) (CHead e2 (Flat f0) u0)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u0))))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead e2 (Flat f0) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 O v u0 w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda (x0: 
F).(\lambda (x1: C).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H22: (eq C e 
(CHead x1 (Flat x0) x2))).(\lambda (H23: (drop (S n0) O c0 (CHead x1 (Flat 
x0) x3))).(\lambda (H24: (subst0 O v x2 x3)).(eq_ind_r C (CHead x1 (Flat x0) 
x2) (\lambda (c: C).(or4 (drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) c) 
(ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u0: T).(\lambda 
(_: T).(eq C c (CHead e0 (Flat f0) u0)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) t) (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C c 
(CHead e1 (Flat f0) u0)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead 
e2 (Flat f0) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C c 
(CHead e1 (Flat f0) u0))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) t) (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))) (or4_intro1 (drop (s (Flat f) (S n0)) O 
(CHead c0 (Flat f) t) (CHead x1 (Flat x0) x2)) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead x1 (Flat 
x0) x2) (CHead e0 (Flat f0) u0)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) t) (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C 
(CHead x1 (Flat x0) x2) (CHead e1 (Flat f0) u0)))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (s (Flat f) (S 
n0)) O (CHead c0 (Flat f) t) (CHead e2 (Flat f0) u0)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) x2) (CHead e1 (Flat f0) 
u0))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead 
e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))) (ex3_4_intro F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) x2) (CHead e0 
(Flat f0) u0)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead e0 (Flat f0) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 O v u0 w))))) x0 x1 x2 x3 (refl_equal C (CHead x1 (Flat x0) x2)) 
(drop_drop (Flat f) n0 c0 (CHead x1 (Flat x0) x3) H23 t) H24)) e H22)))))))) 
H21)) (\lambda (H21: (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S n0) O c0 (CHead 
e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2))))))).(ex3_4_ind F C C T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 (Flat 
f0) u0)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: 
T).(drop (S n0) O c0 (CHead e2 (Flat f0) u0)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))) (or4 (drop 
(s (Flat f) (S n0)) O (CHead c0 (Flat f) t) e) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 (Flat 
f0) u0)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead e0 (Flat f0) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 O v u0 w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(eq C e (CHead e1 (Flat f0) u0)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (s 
(Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead e2 (Flat f0) u0)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u0))))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead e2 (Flat f0) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 O v u0 w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (x0: F).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: 
T).(\lambda (H22: (eq C e (CHead x1 (Flat x0) x3))).(\lambda (H23: (drop (S 
n0) O c0 (CHead x2 (Flat x0) x3))).(\lambda (H24: (csubst0 O v x1 
x2)).(eq_ind_r C (CHead x1 (Flat x0) x3) (\lambda (c: C).(or4 (drop (s (Flat 
f) (S n0)) O (CHead c0 (Flat f) t) c) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C c (CHead e0 (Flat 
f0) u0)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead e0 (Flat f0) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 O v u0 w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(eq C c (CHead e1 (Flat f0) u0)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (s 
(Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead e2 (Flat f0) u0)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C c (CHead e1 (Flat f0) u0))))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead e2 (Flat f0) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: 
T).(\lambda (w: T).(subst0 O v u0 w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (or4_intro2 (drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) 
(CHead x1 (Flat x0) x3)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) x3) (CHead e0 
(Flat f0) u0)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead e0 (Flat f0) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 O v u0 w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(eq C (CHead x1 (Flat x0) x3) (CHead e1 
(Flat f0) u0)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u0: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead e2 (Flat f0) 
u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) 
x3) (CHead e1 (Flat f0) u0))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) t) (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (ex3_4_intro F C C T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C (CHead x1 (Flat 
x0) x3) (CHead e1 (Flat f0) u0)))))) (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u0: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) t) (CHead e2 (Flat f0) u0)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))) x0 x1 x2 x3 
(refl_equal C (CHead x1 (Flat x0) x3)) (drop_drop (Flat f) n0 c0 (CHead x2 
(Flat x0) x3) H23 t) H24)) e H22)))))))) H21)) (\lambda (H21: (ex4_5 F C C T 
T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead 
e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))).(ex4_5_ind F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u0))))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O c0 (CHead e2 (Flat f0) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O 
v u0 w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))) (or4 (drop (s (Flat f) (S n0)) O 
(CHead c0 (Flat f) t) e) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u0: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u0)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead e0 (Flat f0) w)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 
w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(eq C e (CHead e1 (Flat f0) u0)))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (s (Flat f) (S 
n0)) O (CHead c0 (Flat f) t) (CHead e2 (Flat f0) u0)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u0))))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead e2 (Flat f0) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: 
T).(subst0 O v u0 w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda (x0: 
F).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: 
T).(\lambda (H22: (eq C e (CHead x1 (Flat x0) x3))).(\lambda (H23: (drop (S 
n0) O c0 (CHead x2 (Flat x0) x4))).(\lambda (H24: (subst0 O v x3 
x4)).(\lambda (H25: (csubst0 O v x1 x2)).(eq_ind_r C (CHead x1 (Flat x0) x3) 
(\lambda (c: C).(or4 (drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) c) 
(ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u0: T).(\lambda 
(_: T).(eq C c (CHead e0 (Flat f0) u0)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) t) (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C c 
(CHead e1 (Flat f0) u0)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u0: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead 
e2 (Flat f0) u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C c 
(CHead e1 (Flat f0) u0))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) t) (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))) (or4_intro3 (drop (s (Flat f) (S n0)) O 
(CHead c0 (Flat f) t) (CHead x1 (Flat x0) x3)) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead x1 (Flat 
x0) x3) (CHead e0 (Flat f0) u0)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) t) (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u0: T).(eq C 
(CHead x1 (Flat x0) x3) (CHead e1 (Flat f0) u0)))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(drop (s (Flat f) (S 
n0)) O (CHead c0 (Flat f) t) (CHead e2 (Flat f0) u0)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u0: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) x3) (CHead e1 (Flat f0) 
u0))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) t) (CHead 
e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))) (ex4_5_intro F C C T T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) 
x3) (CHead e1 (Flat f0) u0))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) t) (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u0: T).(\lambda (w: T).(subst0 O v u0 w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) x0 x1 x2 x3 x4 (refl_equal C (CHead x1 (Flat 
x0) x3)) (drop_drop (Flat f) n0 c0 (CHead x2 (Flat x0) x4) H23 t) H24 H25)) e 
H22)))))))))) H21)) H20)) i H18)))))) k (drop_gen_drop k c e t n0 H1) H0))) 
c2 H15)) u (sym_eq T u t H14))) k0 (sym_eq K k0 k H13))) c1 (sym_eq C c1 c 
H12))) H11)) H10))) v0 (sym_eq T v0 v H8))) (S n0) H7)) H4 H5 H6 H2))))) | 
(csubst0_both k0 i v0 u1 u2 H2 c1 c0 H3) \Rightarrow (\lambda (H4: (eq nat (s 
k0 i) (S n0))).(\lambda (H5: (eq T v0 v)).(\lambda (H6: (eq C (CHead c1 k0 
u1) (CHead c k t))).(\lambda (H7: (eq C (CHead c0 k0 u2) c2)).((let H8 \def 
(f_equal nat nat (\lambda (e0: nat).e0) (s k0 i) (S n0) H4) in (eq_ind nat (s 
k0 i) (\lambda (n: nat).((eq T v0 v) \to ((eq C (CHead c1 k0 u1) (CHead c k 
t)) \to ((eq C (CHead c0 k0 u2) c2) \to ((subst0 i v0 u1 u2) \to ((csubst0 i 
v0 c1 c0) \to (or4 (drop n O c2 e) (ex3_4 F C T T (\lambda (f: F).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n O c2 
(CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop n O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop n O c2 (CHead e2 
(Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))))))))) (\lambda (H9: (eq T v0 v)).(eq_ind T v (\lambda (t0: T).((eq 
C (CHead c1 k0 u1) (CHead c k t)) \to ((eq C (CHead c0 k0 u2) c2) \to 
((subst0 i t0 u1 u2) \to ((csubst0 i t0 c1 c0) \to (or4 (drop (s k0 i) O c2 
e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s k0 i) O c2 (CHead e0 (Flat f) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (s k0 
i) O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s k0 i) O c2 (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))))))) (\lambda (H10: (eq C (CHead c1 k0 u1) (CHead c k t))).(let 
H11 \def (f_equal C T (\lambda (e0: C).(match e0 in C return (\lambda (_: 
C).T) with [(CSort _) \Rightarrow u1 | (CHead _ _ t) \Rightarrow t])) (CHead 
c1 k0 u1) (CHead c k t) H10) in ((let H12 \def (f_equal C K (\lambda (e0: 
C).(match e0 in C return (\lambda (_: C).K) with [(CSort _) \Rightarrow k0 | 
(CHead _ k _) \Rightarrow k])) (CHead c1 k0 u1) (CHead c k t) H10) in ((let 
H13 \def (f_equal C C (\lambda (e0: C).(match e0 in C return (\lambda (_: 
C).C) with [(CSort _) \Rightarrow c1 | (CHead c _ _) \Rightarrow c])) (CHead 
c1 k0 u1) (CHead c k t) H10) in (eq_ind C c (\lambda (c: C).((eq K k0 k) \to 
((eq T u1 t) \to ((eq C (CHead c0 k0 u2) c2) \to ((subst0 i v u1 u2) \to 
((csubst0 i v c c0) \to (or4 (drop (s k0 i) O c2 e) (ex3_4 F C T T (\lambda 
(f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 
(Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (s k0 i) O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (s k0 i) O c2 (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s k0 i) O c2 (CHead e2 (Flat f) w))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))))))))) (\lambda 
(H14: (eq K k0 k)).(eq_ind K k (\lambda (k: K).((eq T u1 t) \to ((eq C (CHead 
c0 k u2) c2) \to ((subst0 i v u1 u2) \to ((csubst0 i v c c0) \to (or4 (drop 
(s k i) O c2 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s k i) O c2 (CHead 
e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (s k 
i) O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s k i) O c2 (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))))))) (\lambda (H15: (eq T u1 t)).(eq_ind T t (\lambda (t: T).((eq 
C (CHead c0 k u2) c2) \to ((subst0 i v t u2) \to ((csubst0 i v c c0) \to (or4 
(drop (s k i) O c2 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s k 
i) O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (s k i) O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
k i) O c2 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))))))))) (\lambda (H16: (eq C (CHead c0 k u2) 
c2)).(eq_ind C (CHead c0 k u2) (\lambda (c2: C).((subst0 i v t u2) \to 
((csubst0 i v c c0) \to (or4 (drop (s k i) O c2 e) (ex3_4 F C T T (\lambda 
(f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 
(Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (s k i) O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (s k i) O c2 (CHead e2 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
k i) O c2 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))))) (\lambda (H17: (subst0 i v t 
u2)).(\lambda (H18: (csubst0 i v c c0)).(let H0 \def (eq_ind K k0 (\lambda 
(k: K).(eq nat (s k i) (S n0))) H8 k H14) in (K_ind (\lambda (k: K).((drop (r 
k n0) O c e) \to ((eq nat (s k i) (S n0)) \to (or4 (drop (s k i) O (CHead c0 
k u2) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s k i) O (CHead c0 
k u2) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (s k i) O (CHead c0 k u2) (CHead e2 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
k i) O (CHead c0 k u2) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))))) (\lambda (b: B).(\lambda (H1: (drop (r 
(Bind b) n0) O c e)).(\lambda (H19: (eq nat (s (Bind b) i) (S n0))).(let H20 
\def (f_equal nat nat (\lambda (e0: nat).(match e0 in nat return (\lambda (_: 
nat).nat) with [O \Rightarrow i | (S n) \Rightarrow n])) (S i) (S n0) H19) in 
(let H21 \def (eq_ind nat i (\lambda (n: nat).(csubst0 n v c c0)) H18 n0 H20) 
in (let H22 \def (eq_ind nat i (\lambda (n: nat).(subst0 n v t u2)) H17 n0 
H20) in (eq_ind_r nat n0 (\lambda (n: nat).(or4 (drop (s (Bind b) n) O (CHead 
c0 (Bind b) u2) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n) O 
(CHead c0 (Bind b) u2) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (s (Bind b) n) O (CHead c0 (Bind b) u2) (CHead e2 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 
(Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop (s (Bind b) n) O (CHead c0 (Bind b) u2) (CHead 
e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (let H \def (IHn c c0 v H21 e H1) in (or4_ind (drop n0 O c0 e) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop n0 O c0 (CHead e0 (Flat f) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u 
w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop n0 O c0 (CHead e2 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 
(Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop n0 O c0 (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (or4 (drop (s (Bind b) n0) O 
(CHead c0 (Bind b) u2) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (s (Bind b) n0) O (CHead c0 (Bind 
b) u2) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) 
u2) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2)))))))) (\lambda (H23: (drop n0 O c0 e)).(or4_intro0 (drop (s (Bind 
b) n0) O (CHead c0 (Bind b) u2) e) (ex3_4 F C T T (\lambda (f: F).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (s (Bind b) n0) O (CHead c0 (Bind 
b) u2) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) 
u2) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))) (drop_drop (Bind b) n0 c0 e H23 u2))) (\lambda (H23: (ex3_4 
F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop n0 O c0 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u 
w))))))).(ex3_4_ind F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop n0 O c0 (CHead e0 
(Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w))))) (or4 (drop (s (Bind b) n0) O (CHead c0 (Bind b) u2) 
e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) 
u2) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e2 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e2 (Flat f) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda (x0: 
F).(\lambda (x1: C).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H24: (eq C e 
(CHead x1 (Flat x0) x2))).(\lambda (H25: (drop n0 O c0 (CHead x1 (Flat x0) 
x3))).(\lambda (H26: (subst0 O v x2 x3)).(eq_ind_r C (CHead x1 (Flat x0) x2) 
(\lambda (c: C).(or4 (drop (s (Bind b) n0) O (CHead c0 (Bind b) u2) c) (ex3_4 
F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq 
C c (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e0 
(Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e2 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C c (CHead e1 (Flat f) u))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e2 (Flat f) w))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))))) (or4_intro1 
(drop (s (Bind b) n0) O (CHead c0 (Bind b) u2) (CHead x1 (Flat x0) x2)) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C (CHead x1 (Flat x0) x2) (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) O 
(CHead c0 (Bind b) u2) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead 
x1 (Flat x0) x2) (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (s (Bind b) n0) O (CHead c0 (Bind 
b) u2) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead x1 (Flat x0) x2) (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) 
O (CHead c0 (Bind b) u2) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (ex3_4_intro F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) 
x2) (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e0 
(Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w))))) x0 x1 x2 x3 (refl_equal C (CHead x1 (Flat x0) x2)) 
(drop_drop (Bind b) n0 c0 (CHead x1 (Flat x0) x3) H25 u2) H26)) e H24)))))))) 
H23)) (\lambda (H23: (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop n0 O c0 (CHead e2 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2))))))).(ex3_4_ind F C C T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop n0 O 
c0 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2))))) (or4 (drop (s (Bind b) n0) O 
(CHead c0 (Bind b) u2) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (s (Bind b) n0) O (CHead c0 (Bind 
b) u2) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) 
u2) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2)))))))) (\lambda (x0: F).(\lambda (x1: C).(\lambda (x2: C).(\lambda 
(x3: T).(\lambda (H24: (eq C e (CHead x1 (Flat x0) x3))).(\lambda (H25: (drop 
n0 O c0 (CHead x2 (Flat x0) x3))).(\lambda (H26: (csubst0 O v x1 
x2)).(eq_ind_r C (CHead x1 (Flat x0) x3) (\lambda (c: C).(or4 (drop (s (Bind 
b) n0) O (CHead c0 (Bind b) u2) c) (ex3_4 F C T T (\lambda (f: F).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e0 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C c (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (s (Bind b) n0) O (CHead c0 (Bind 
b) u2) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
c (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) 
u2) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))))) (or4_intro2 (drop (s (Bind b) n0) O (CHead c0 (Bind b) u2) 
(CHead x1 (Flat x0) x3)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) x3) (CHead e0 
(Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e0 (Flat f) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x1 (Flat x0) x3) (CHead e1 
(Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) 
x3) (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) 
u2) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))) (ex3_4_intro F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x1 (Flat x0) x3) (CHead e1 
(Flat f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e2 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2))))) x0 x1 x2 x3 (refl_equal C (CHead x1 (Flat x0) x3)) 
(drop_drop (Bind b) n0 c0 (CHead x2 (Flat x0) x3) H25 u2) H26)) e H24)))))))) 
H23)) (\lambda (H23: (ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop n0 O c0 (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))))).(ex4_5_ind F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop n0 O c0 (CHead e2 (Flat f) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))) (or4 (drop (s 
(Bind b) n0) O (CHead c0 (Bind b) u2) e) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e0 (Flat f) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u 
w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (s (Bind b) n0) O 
(CHead c0 (Bind b) u2) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e1 (Flat f) u))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e2 (Flat f) w))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda (x0: 
F).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: 
T).(\lambda (H24: (eq C e (CHead x1 (Flat x0) x3))).(\lambda (H25: (drop n0 O 
c0 (CHead x2 (Flat x0) x4))).(\lambda (H26: (subst0 O v x3 x4)).(\lambda 
(H27: (csubst0 O v x1 x2)).(eq_ind_r C (CHead x1 (Flat x0) x3) (\lambda (c: 
C).(or4 (drop (s (Bind b) n0) O (CHead c0 (Bind b) u2) c) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c 
(CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s (Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e0 
(Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e2 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C c (CHead e1 (Flat f) u))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Bind b) n0) O (CHead c0 (Bind b) u2) (CHead e2 (Flat f) w))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))))) (or4_intro3 
(drop (s (Bind b) n0) O (CHead c0 (Bind b) u2) (CHead x1 (Flat x0) x3)) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C (CHead x1 (Flat x0) x3) (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) O 
(CHead c0 (Bind b) u2) (CHead e0 (Flat f) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead 
x1 (Flat x0) x3) (CHead e1 (Flat f) u)))))) (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(drop (s (Bind b) n0) O (CHead c0 (Bind 
b) u2) (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead x1 (Flat x0) x3) (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) 
O (CHead c0 (Bind b) u2) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (ex4_5_intro F C C T T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead x1 (Flat x0) x3) (CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Bind b) n0) 
O (CHead c0 (Bind b) u2) (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) x0 x1 x2 x3 x4 (refl_equal C (CHead x1 (Flat 
x0) x3)) (drop_drop (Bind b) n0 c0 (CHead x2 (Flat x0) x4) H25 u2) H26 H27)) 
e H24)))))))))) H23)) H)) i H20))))))) (\lambda (f: F).(\lambda (H1: (drop (r 
(Flat f) n0) O c e)).(\lambda (H19: (eq nat (s (Flat f) i) (S n0))).(let H20 
\def (f_equal nat nat (\lambda (e0: nat).e0) i (S n0) H19) in (let H21 \def 
(eq_ind nat i (\lambda (n: nat).(csubst0 n v c c0)) H18 (S n0) H20) in (let 
H22 \def (eq_ind nat i (\lambda (n: nat).(subst0 n v t u2)) H17 (S n0) H20) 
in (eq_ind_r nat (S n0) (\lambda (n: nat).(or4 (drop (s (Flat f) n) O (CHead 
c0 (Flat f) u2) e) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) n) O 
(CHead c0 (Flat f) u2) (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (s (Flat f) n) O (CHead c0 (Flat f) u2) (CHead e2 
(Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 
(Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop (s (Flat f) n) O (CHead c0 (Flat f) u2) (CHead 
e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))))) (let H23 \def (H c0 v H21 e H1) in (or4_ind (drop (S n0) O 
c0 e) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead 
e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (S 
n0) O c0 (CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C e (CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead 
e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))) (or4 (drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) e) 
(ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) u2) (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead 
e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) u2) (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))))) (\lambda (H24: (drop (S n0) O c0 
e)).(or4_intro0 (drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) e) (ex3_4 
F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) 
(CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat 
f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead e2 (Flat f0) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat 
f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead 
e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))) (drop_drop (Flat f) n0 c0 e H24 u2))) (\lambda (H24: (ex3_4 
F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (S n0) O c0 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u 
w))))))).(ex3_4_ind F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead 
e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 O v u w))))) (or4 (drop (s (Flat f) (S n0)) O (CHead c0 (Flat 
f) u2) e) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) 
O (CHead c0 (Flat f) u2) (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead 
e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) u2) (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2)))))))) (\lambda (x0: F).(\lambda (x1: C).(\lambda 
(x2: T).(\lambda (x3: T).(\lambda (H25: (eq C e (CHead x1 (Flat x0) 
x2))).(\lambda (H26: (drop (S n0) O c0 (CHead x1 (Flat x0) x3))).(\lambda 
(H27: (subst0 O v x2 x3)).(eq_ind_r C (CHead x1 (Flat x0) x2) (\lambda (c: 
C).(or4 (drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) c) (ex3_4 F C T T 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c 
(CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead 
e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (s 
(Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead e2 (Flat f0) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 (Flat f0) u))))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead e2 (Flat f0) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (or4_intro1 (drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) 
(CHead x1 (Flat x0) x2)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) x2) (CHead e0 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead e0 (Flat f0) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x1 (Flat x0) x2) (CHead e1 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead e2 (Flat f0) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) 
x2) (CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) u2) (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (ex3_4_intro F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) 
x2) (CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) 
(CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w))))) x0 x1 x2 x3 (refl_equal C (CHead x1 
(Flat x0) x2)) (drop_drop (Flat f) n0 c0 (CHead x1 (Flat x0) x3) H26 u2) 
H27)) e H25)))))))) H24)) (\lambda (H24: (ex3_4 F C C T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop (S n0) O c0 (CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))))).(ex3_4_ind F C 
C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (S n0) O c0 (CHead e2 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))) 
(or4 (drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) e) (ex3_4 F C T T 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead 
e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (s 
(Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead e2 (Flat f0) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u))))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead e2 (Flat f0) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (x0: F).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: 
T).(\lambda (H25: (eq C e (CHead x1 (Flat x0) x3))).(\lambda (H26: (drop (S 
n0) O c0 (CHead x2 (Flat x0) x3))).(\lambda (H27: (csubst0 O v x1 
x2)).(eq_ind_r C (CHead x1 (Flat x0) x3) (\lambda (c: C).(or4 (drop (s (Flat 
f) (S n0)) O (CHead c0 (Flat f) u2) c) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e0 (Flat 
f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead e0 (Flat f0) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (s 
(Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead e2 (Flat f0) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 (Flat f0) u))))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead e2 (Flat f0) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (or4_intro2 (drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) 
(CHead x1 (Flat x0) x3)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) x3) (CHead e0 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead e0 (Flat f0) 
w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x1 (Flat x0) x3) (CHead e1 
(Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(u: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead e2 (Flat f0) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) 
x3) (CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) u2) (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))) (ex3_4_intro F C C T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x1 (Flat x0) 
x3) (CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) 
(CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2))))) x0 x1 x2 x3 (refl_equal C (CHead 
x1 (Flat x0) x3)) (drop_drop (Flat f) n0 c0 (CHead x2 (Flat x0) x3) H26 u2) 
H27)) e H25)))))))) H24)) (\lambda (H24: (ex4_5 F C C T T (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 (Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (S n0) O c0 (CHead e2 (Flat f) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))).(ex4_5_ind F C C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u))))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(drop (S n0) O c0 (CHead e2 (Flat f0) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))) (or4 (drop (s (Flat f) (S n0)) O 
(CHead c0 (Flat f) u2) e) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead e0 (Flat f0) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u 
w)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Flat f0) u)))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop (s (Flat f) (S n0)) 
O (CHead c0 (Flat f) u2) (CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e1 (Flat f0) u))))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead e2 (Flat f0) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda (x0: 
F).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: 
T).(\lambda (H25: (eq C e (CHead x1 (Flat x0) x3))).(\lambda (H26: (drop (S 
n0) O c0 (CHead x2 (Flat x0) x4))).(\lambda (H27: (subst0 O v x3 
x4)).(\lambda (H28: (csubst0 O v x1 x2)).(eq_ind_r C (CHead x1 (Flat x0) x3) 
(\lambda (c: C).(or4 (drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) c) 
(ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C c (CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) u2) (CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c 
(CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead 
e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C c 
(CHead e1 (Flat f0) u))))))) (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 
(Flat f) u2) (CHead e2 (Flat f0) w))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))) (or4_intro3 (drop (s (Flat f) (S n0)) O 
(CHead c0 (Flat f) u2) (CHead x1 (Flat x0) x3)) (ex3_4 F C T T (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) 
x3) (CHead e0 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) 
(CHead e0 (Flat f0) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (ex3_4 F C C T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x1 (Flat x0) 
x3) (CHead e1 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) 
(CHead e2 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead x1 (Flat x0) x3) (CHead e1 (Flat f0) u))))))) (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop (s 
(Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead e2 (Flat f0) w))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (ex4_5_intro F C 
C T T (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead x1 (Flat x0) x3) (CHead e1 (Flat f0) u))))))) 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(drop (s (Flat f) (S n0)) O (CHead c0 (Flat f) u2) (CHead e2 (Flat f0) 
w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
x0 x1 x2 x3 x4 (refl_equal C (CHead x1 (Flat x0) x3)) (drop_drop (Flat f) n0 
c0 (CHead x2 (Flat x0) x4) H26 u2) H27 H28)) e H25)))))))))) H24)) H23)) i 
H20))))))) k (drop_gen_drop k c e t n0 H1) H0)))) c2 H16)) u1 (sym_eq T u1 t 
H15))) k0 (sym_eq K k0 k H14))) c1 (sym_eq C c1 c H13))) H12)) H11))) v0 
(sym_eq T v0 v H9))) (S n0) H8)) H5 H6 H7 H2 H3)))))]) in (H2 (refl_equal nat 
(S n0)) (refl_equal T v) (refl_equal C (CHead c k t)) (refl_equal C 
c2)))))))))))) c1)))) n).

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
(or4 (drop O O c1 c2) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C c2 (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop O O 
c1 (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C c2 (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop O O c1 (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C c2 (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop O O c1 (CHead e1 
(Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (y: nat).(\lambda (H1: (csubst0 y v c1 c2)).(csubst0_ind 
(\lambda (n0: nat).(\lambda (t: T).(\lambda (c: C).(\lambda (c0: C).((eq nat 
n0 O) \to (or4 (drop O O c c0) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop O O c 
(CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O t u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C c0 (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop O O c (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O t e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C c0 (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop O O c (CHead e1 
(Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 O t u1 u2)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O t e1 
e2))))))))))))) (\lambda (k: K).(K_ind (\lambda (k0: K).(\forall (i: 
nat).(\forall (v0: T).(\forall (u1: T).(\forall (u2: T).((subst0 i v0 u1 u2) 
\to (\forall (c: C).((eq nat (s k0 i) O) \to (or4 (drop O O (CHead c k0 u1) 
(CHead c k0 u2)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u4: T).(eq C (CHead c k0 u2) (CHead e0 (Flat f) u4)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u3: T).(\lambda (_: T).(drop O O 
(CHead c k0 u1) (CHead e0 (Flat f) u3)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u3: T).(\lambda (u4: T).(subst0 O v0 u3 u4)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C (CHead 
c k0 u2) (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u: T).(drop O O (CHead c k0 u1) (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u4: T).(eq C (CHead c k0 u2) (CHead e2 (Flat f) 
u4))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u3: 
T).(\lambda (_: T).(drop O O (CHead c k0 u1) (CHead e1 (Flat f) u3))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u3: T).(\lambda 
(u4: T).(subst0 O v0 u3 u4)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 e2)))))))))))))))) 
(\lambda (b: B).(\lambda (i: nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda 
(u2: T).(\lambda (_: (subst0 i v0 u1 u2)).(\lambda (c: C).(\lambda (H3: (eq 
nat (S i) O)).(let H4 \def (eq_ind nat (S i) (\lambda (ee: nat).(match ee in 
nat return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) 
\Rightarrow True])) I O H3) in (False_ind (or4 (drop O O (CHead c (Bind b) 
u1) (CHead c (Bind b) u2)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u4: T).(eq C (CHead c (Bind b) u2) (CHead e0 
(Flat f) u4)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u3: T).(\lambda 
(_: T).(drop O O (CHead c (Bind b) u1) (CHead e0 (Flat f) u3)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: T).(subst0 O v0 u3 
u4)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C (CHead c (Bind b) u2) (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop O O 
(CHead c (Bind b) u1) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u4: T).(eq C (CHead c (Bind b) u2) (CHead e2 (Flat f) u4))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u3: T).(\lambda 
(_: T).(drop O O (CHead c (Bind b) u1) (CHead e1 (Flat f) u3))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: 
T).(subst0 O v0 u3 u4)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 e2)))))))) H4)))))))))) 
(\lambda (f: F).(\lambda (i: nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda 
(u2: T).(\lambda (H2: (subst0 i v0 u1 u2)).(\lambda (c: C).(\lambda (H3: (eq 
nat i O)).(let H4 \def (eq_ind nat i (\lambda (n: nat).(subst0 n v0 u1 u2)) 
H2 O H3) in (or4_intro1 (drop O O (CHead c (Flat f) u1) (CHead c (Flat f) 
u2)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: 
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
(drop_refl (CHead c (Flat f) u1)) H4))))))))))) k)) (\lambda (k: K).(K_ind 
(\lambda (k0: K).(\forall (i: nat).(\forall (c3: C).(\forall (c4: C).(\forall 
(v0: T).((csubst0 i v0 c3 c4) \to ((((eq nat i O) \to (or4 (drop O O c3 c4) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: 
T).(eq C c4 (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop O O c3 (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O 
v0 u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C c4 (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop O O c3 (CHead e1 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C c4 (CHead e2 
(Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(drop O O c3 (CHead e1 (Flat f) u1))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v0 u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 e2)))))))))) \to (\forall 
(u: T).((eq nat (s k0 i) O) \to (or4 (drop O O (CHead c3 k0 u) (CHead c4 k0 
u)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C (CHead c4 k0 u) (CHead e0 (Flat f) u2)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop O O (CHead c3 k0 
u) (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v0 u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(eq C (CHead c4 k0 u) 
(CHead e2 (Flat f) u0)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(drop O O (CHead c3 k0 u) (CHead e1 (Flat f) u0)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead c4 k0 u) (CHead e2 (Flat f) 
u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop O O (CHead c3 k0 u) (CHead e1 (Flat f) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v0 u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 e2))))))))))))))))) 
(\lambda (b: B).(\lambda (i: nat).(\lambda (c3: C).(\lambda (c4: C).(\lambda 
(v0: T).(\lambda (_: (csubst0 i v0 c3 c4)).(\lambda (_: (((eq nat i O) \to 
(or4 (drop O O c3 c4) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C c4 (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop O O 
c3 (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v0 u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C c4 (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop O O c3 (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T 
T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C c4 (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop O O c3 (CHead e1 
(Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 O v0 u1 u2)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 
e2))))))))))).(\lambda (u: T).(\lambda (H4: (eq nat (S i) O)).(let H5 \def 
(eq_ind nat (S i) (\lambda (ee: nat).(match ee in nat return (\lambda (_: 
nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) I O H4) in 
(False_ind (or4 (drop O O (CHead c3 (Bind b) u) (CHead c4 (Bind b) u)) (ex3_4 
F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq 
C (CHead c4 (Bind b) u) (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(drop O O (CHead c3 (Bind b) u) 
(CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v0 u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(eq C (CHead c4 (Bind b) 
u) (CHead e2 (Flat f) u0)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u0: T).(drop O O (CHead c3 (Bind b) u) (CHead e1 (Flat f) 
u0)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead c4 (Bind b) 
u) (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop O O (CHead c3 (Bind b) u) (CHead e1 
(Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 O v0 u1 u2)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 
e2)))))))) H5))))))))))) (\lambda (f: F).(\lambda (i: nat).(\lambda (c3: 
C).(\lambda (c4: C).(\lambda (v0: T).(\lambda (H2: (csubst0 i v0 c3 
c4)).(\lambda (H3: (((eq nat i O) \to (or4 (drop O O c3 c4) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c4 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop O O c3 (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v0 u1 u2)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C c4 (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop O O c3 (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C c4 (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop O O c3 (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v0 u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v0 e1 e2))))))))))).(\lambda (u: T).(\lambda (H4: (eq nat i 
O)).(let H5 \def (eq_ind nat i (\lambda (n: nat).((eq nat n O) \to (or4 (drop 
O O c3 c4) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C c4 (CHead e0 (Flat f) u2)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop O O c3 (CHead e0 
(Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v0 u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C c4 (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop O O c3 
(CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C c4 
(CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop O O c3 (CHead e1 (Flat f) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v0 u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 e2)))))))))) H3 O 
H4) in (let H6 \def (eq_ind nat i (\lambda (n: nat).(csubst0 n v0 c3 c4)) H2 
O H4) in (or4_intro2 (drop O O (CHead c3 (Flat f) u) (CHead c4 (Flat f) u)) 
(ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C (CHead c4 (Flat f) u) (CHead e0 (Flat f0) u2)))))) (\lambda 
(f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop O O (CHead c3 
(Flat f) u) (CHead e0 (Flat f0) u1)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v0 u1 u2)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u0: T).(eq C 
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
(drop_refl (CHead c3 (Flat f) u)) H6))))))))))))) k)) (\lambda (k: K).(K_ind 
(\lambda (k0: K).(\forall (i: nat).(\forall (v0: T).(\forall (u1: T).(\forall 
(u2: T).((subst0 i v0 u1 u2) \to (\forall (c3: C).(\forall (c4: C).((csubst0 
i v0 c3 c4) \to ((((eq nat i O) \to (or4 (drop O O c3 c4) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c4 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop O O c3 (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v0 u1 u2)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C c4 (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop O O c3 (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C c4 (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop O O c3 (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v0 u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v0 e1 e2)))))))))) \to ((eq nat (s k0 i) O) \to (or4 (drop 
O O (CHead c3 k0 u1) (CHead c4 k0 u2)) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u4: T).(eq C (CHead c4 k0 u2) 
(CHead e0 (Flat f) u4)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u3: 
T).(\lambda (_: T).(drop O O (CHead c3 k0 u1) (CHead e0 (Flat f) u3)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: T).(subst0 O 
v0 u3 u4)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C (CHead c4 k0 u2) (CHead e2 (Flat f) u)))))) (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop O O (CHead c3 
k0 u1) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda 
(f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u4: T).(eq 
C (CHead c4 k0 u2) (CHead e2 (Flat f) u4))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u3: T).(\lambda (_: T).(drop O O (CHead c3 k0 
u1) (CHead e1 (Flat f) u3))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u3: T).(\lambda (u4: T).(subst0 O v0 u3 u4)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v0 e1 e2))))))))))))))))))) (\lambda (b: B).(\lambda (i: nat).(\lambda (v0: 
T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (_: (subst0 i v0 u1 
u2)).(\lambda (c3: C).(\lambda (c4: C).(\lambda (_: (csubst0 i v0 c3 
c4)).(\lambda (_: (((eq nat i O) \to (or4 (drop O O c3 c4) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c4 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop O O c3 (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v0 u1 u2)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C c4 (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop O O c3 (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C c4 (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop O O c3 (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v0 u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v0 e1 e2))))))))))).(\lambda (H5: (eq nat (S i) O)).(let H6 
\def (eq_ind nat (S i) (\lambda (ee: nat).(match ee in nat return (\lambda 
(_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) I O H5) 
in (False_ind (or4 (drop O O (CHead c3 (Bind b) u1) (CHead c4 (Bind b) u2)) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u4: 
T).(eq C (CHead c4 (Bind b) u2) (CHead e0 (Flat f) u4)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u3: T).(\lambda (_: T).(drop O O (CHead c3 
(Bind b) u1) (CHead e0 (Flat f) u3)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u3: T).(\lambda (u4: T).(subst0 O v0 u3 u4)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C (CHead 
c4 (Bind b) u2) (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop O O (CHead c3 (Bind b) u1) (CHead e1 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u4: T).(eq C (CHead c4 
(Bind b) u2) (CHead e2 (Flat f) u4))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u3: T).(\lambda (_: T).(drop O O (CHead c3 (Bind 
b) u1) (CHead e1 (Flat f) u3))))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(_: C).(\lambda (u3: T).(\lambda (u4: T).(subst0 O v0 u3 u4)))))) (\lambda 
(_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: 
T).(csubst0 O v0 e1 e2)))))))) H6))))))))))))) (\lambda (f: F).(\lambda (i: 
nat).(\lambda (v0: T).(\lambda (u1: T).(\lambda (u2: T).(\lambda (H2: (subst0 
i v0 u1 u2)).(\lambda (c3: C).(\lambda (c4: C).(\lambda (H3: (csubst0 i v0 c3 
c4)).(\lambda (H4: (((eq nat i O) \to (or4 (drop O O c3 c4) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C c4 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop O O c3 (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v0 u1 u2)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C c4 (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop O O c3 (CHead e1 (Flat f) u)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O 
v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C c4 (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop O O c3 (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v0 u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v0 e1 e2))))))))))).(\lambda (H5: (eq nat i O)).(let H6 
\def (eq_ind nat i (\lambda (n: nat).((eq nat n O) \to (or4 (drop O O c3 c4) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: 
T).(eq C c4 (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop O O c3 (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O 
v0 u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C c4 (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop O O c3 (CHead e1 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C c4 (CHead e2 
(Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(drop O O c3 (CHead e1 (Flat f) u1))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v0 u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 e2)))))))))) H4 O H5) in 
(let H7 \def (eq_ind nat i (\lambda (n: nat).(csubst0 n v0 c3 c4)) H3 O H5) 
in (let H8 \def (eq_ind nat i (\lambda (n: nat).(subst0 n v0 u1 u2)) H2 O H5) 
in (or4_intro3 (drop O O (CHead c3 (Flat f) u1) (CHead c4 (Flat f) u2)) 
(ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(u4: T).(eq C (CHead c4 (Flat f) u2) (CHead e0 (Flat f0) u4)))))) (\lambda 
(f0: F).(\lambda (e0: C).(\lambda (u3: T).(\lambda (_: T).(drop O O (CHead c3 
(Flat f) u1) (CHead e0 (Flat f0) u3)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u3: T).(\lambda (u4: T).(subst0 O v0 u3 u4)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C 
(CHead c4 (Flat f) u2) (CHead e2 (Flat f0) u)))))) (\lambda (f0: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(drop O O (CHead c3 (Flat f) u1) 
(CHead e1 (Flat f0) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u4: T).(eq C 
(CHead c4 (Flat f) u2) (CHead e2 (Flat f0) u4))))))) (\lambda (f0: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u3: T).(\lambda (_: T).(drop O 
O (CHead c3 (Flat f) u1) (CHead e1 (Flat f0) u3))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: T).(subst0 
O v0 u3 u4)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 O v0 e1 e2))))))) (ex4_5_intro F C C T T 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u4: T).(eq C (CHead c4 (Flat f) u2) (CHead e2 (Flat f0) u4))))))) (\lambda 
(f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u3: T).(\lambda (_: 
T).(drop O O (CHead c3 (Flat f) u1) (CHead e1 (Flat f0) u3))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u3: T).(\lambda (u4: 
T).(subst0 O v0 u3 u4)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v0 e1 e2)))))) f c3 c4 u1 u2 
(refl_equal C (CHead c4 (Flat f) u2)) (drop_refl (CHead c3 (Flat f) u1)) H8 
H7)))))))))))))))) k)) y v c1 c2 H1))) H) e (drop_gen_refl c2 e H0)))))))) 
(\lambda (n0: nat).(\lambda (IHn: ((\forall (c1: C).(\forall (c2: C).(\forall 
(v: T).((csubst0 n0 v c1 c2) \to (\forall (e: C).((drop n0 O c2 e) \to (or4 
(drop n0 O c1 e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop n0 O c1 (CHead e0 
(Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop n0 O 
c1 (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop n0 O c1 (CHead e1 (Flat f) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))))))))))).(\lambda (c1: C).(C_ind (\lambda (c: C).(\forall (c2: 
C).(\forall (v: T).((csubst0 (S n0) v c c2) \to (\forall (e: C).((drop (S n0) 
O c2 e) \to (or4 (drop (S n0) O c e) (ex3_4 F C T T (\lambda (f: F).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O c (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O c (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O c (CHead 
e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2)))))))))))))) (\lambda (n1: nat).(\lambda (c2: C).(\lambda (v: 
T).(\lambda (H: (csubst0 (S n0) v (CSort n1) c2)).(\lambda (e: C).(\lambda 
(_: (drop (S n0) O c2 e)).(csubst0_gen_sort c2 v (S n0) n1 H (or4 (drop (S 
n0) O (CSort n1) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CSort 
n1) (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O (CSort n1) (CHead e1 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CSort n1) (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 O v e1 e2))))))))))))))) (\lambda (c: C).(\lambda (H: 
((\forall (c2: C).(\forall (v: T).((csubst0 (S n0) v c c2) \to (\forall (e: 
C).((drop (S n0) O c2 e) \to (or4 (drop (S n0) O c e) (ex3_4 F C T T (\lambda 
(f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 
(Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O c (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C 
T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e 
(CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop (S n0) O c (CHead e1 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O c (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2))))))))))))))).(\lambda (k: K).(\lambda (t: T).(\lambda (c2: 
C).(\lambda (v: T).(\lambda (H0: (csubst0 (S n0) v (CHead c k t) 
c2)).(\lambda (e: C).(\lambda (H1: (drop (S n0) O c2 e)).(or3_ind (ex3_2 T 
nat (\lambda (_: T).(\lambda (j: nat).(eq nat (S n0) (s k j)))) (\lambda (u2: 
T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: 
nat).(subst0 j v t u2)))) (ex3_2 C nat (\lambda (_: C).(\lambda (j: nat).(eq 
nat (S n0) (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k 
t)))) (\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3)))) (ex4_3 T C nat 
(\lambda (_: T).(\lambda (_: C).(\lambda (j: nat).(eq nat (S n0) (s k j))))) 
(\lambda (u2: T).(\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k 
u2))))) (\lambda (u2: T).(\lambda (_: C).(\lambda (j: nat).(subst0 j v t 
u2)))) (\lambda (_: T).(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c 
c3))))) (or4 (drop (S n0) O (CHead c k t) e) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat 
f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c k t) (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c k t) (CHead e1 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat 
f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c k t) (CHead e1 (Flat f) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda 
(H2: (ex3_2 T nat (\lambda (_: T).(\lambda (j: nat).(eq nat (S n0) (s k j)))) 
(\lambda (u2: T).(\lambda (_: nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: 
T).(\lambda (j: nat).(subst0 j v t u2))))).(ex3_2_ind T nat (\lambda (_: 
T).(\lambda (j: nat).(eq nat (S n0) (s k j)))) (\lambda (u2: T).(\lambda (_: 
nat).(eq C c2 (CHead c k u2)))) (\lambda (u2: T).(\lambda (j: nat).(subst0 j 
v t u2))) (or4 (drop (S n0) O (CHead c k t) e) (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat 
f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c k t) (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c k t) (CHead e1 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat 
f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c k t) (CHead e1 (Flat f) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))))) (\lambda 
(x0: T).(\lambda (x1: nat).(\lambda (H3: (eq nat (S n0) (s k x1))).(\lambda 
(H4: (eq C c2 (CHead c k x0))).(\lambda (H5: (subst0 x1 v t x0)).(let H6 \def 
(eq_ind C c2 (\lambda (c: C).(drop (S n0) O c e)) H1 (CHead c k x0) H4) in 
((match k in K return (\lambda (k0: K).((eq nat (S n0) (s k0 x1)) \to ((drop 
(r k0 n0) O c e) \to (or4 (drop (S n0) O (CHead c k0 t) e) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
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
O v e1 e2))))))))))) with [(Bind b) \Rightarrow (\lambda (H7: (eq nat (S n0) 
(s (Bind b) x1))).(\lambda (H8: (drop (r (Bind b) n0) O c e)).(let H9 \def 
(f_equal nat nat (\lambda (e0: nat).(match e0 in nat return (\lambda (_: 
nat).nat) with [O \Rightarrow n0 | (S n) \Rightarrow n])) (S n0) (S x1) H7) 
in (let H10 \def (eq_ind_r nat x1 (\lambda (n: nat).(subst0 n v t x0)) H5 n0 
H9) in (or4_intro0 (drop (S n0) O (CHead c (Bind b) t) e) (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e 
(CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) 
u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) 
O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u1))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (drop_drop (Bind b) n0 c e 
H8 t)))))) | (Flat f) \Rightarrow (\lambda (H7: (eq nat (S n0) (s (Flat f) 
x1))).(\lambda (H8: (drop (r (Flat f) n0) O c e)).(let H9 \def (f_equal nat 
nat (\lambda (e0: nat).e0) (S n0) x1 H7) in (let H10 \def (eq_ind_r nat x1 
(\lambda (n: nat).(subst0 n v t x0)) H5 (S n0) H9) in (or4_intro0 (drop (S 
n0) O (CHead c (Flat f) t) e) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: 
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
O v e1 e2))))))) (drop_drop (Flat f) n0 c e H8 t))))))]) H3 (drop_gen_drop k 
c e x0 n0 H6)))))))) H2)) (\lambda (H2: (ex3_2 C nat (\lambda (_: C).(\lambda 
(j: nat).(eq nat (S n0) (s k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C 
c2 (CHead c3 k t)))) (\lambda (c2: C).(\lambda (j: nat).(csubst0 j v c 
c2))))).(ex3_2_ind C nat (\lambda (_: C).(\lambda (j: nat).(eq nat (S n0) (s 
k j)))) (\lambda (c3: C).(\lambda (_: nat).(eq C c2 (CHead c3 k t)))) 
(\lambda (c3: C).(\lambda (j: nat).(csubst0 j v c c3))) (or4 (drop (S n0) O 
(CHead c k t) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: 
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
(_: T).(csubst0 O v e1 e2)))))))) (\lambda (x0: C).(\lambda (x1: 
nat).(\lambda (H3: (eq nat (S n0) (s k x1))).(\lambda (H4: (eq C c2 (CHead x0 
k t))).(\lambda (H5: (csubst0 x1 v c x0)).(let H6 \def (eq_ind C c2 (\lambda 
(c: C).(drop (S n0) O c e)) H1 (CHead x0 k t) H4) in ((match k in K return 
(\lambda (k0: K).((eq nat (S n0) (s k0 x1)) \to ((drop (r k0 n0) O x0 e) \to 
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
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))))))) with [(Bind 
b) \Rightarrow (\lambda (H7: (eq nat (S n0) (s (Bind b) x1))).(\lambda (H8: 
(drop (r (Bind b) n0) O x0 e)).(let H9 \def (f_equal nat nat (\lambda (e0: 
nat).(match e0 in nat return (\lambda (_: nat).nat) with [O \Rightarrow n0 | 
(S n) \Rightarrow n])) (S n0) (S x1) H7) in (let H10 \def (eq_ind_r nat x1 
(\lambda (n: nat).(csubst0 n v c x0)) H5 n0 H9) in (let H11 \def (IHn c x0 v 
H10 e H8) in (or4_ind (drop n0 O c e) (ex3_4 F C T T (\lambda (f: F).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop n0 O 
c (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop n0 O c (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop n0 O c (CHead e1 
(Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))) (or4 (drop (S n0) O (CHead c (Bind b) t) e) (ex3_4 F C T T (\lambda 
(f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 
(Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v 
u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
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
(_: T).(csubst0 O v e1 e2)))))))) (\lambda (H12: (drop n0 O c e)).(or4_intro0 
(drop (S n0) O (CHead c (Bind b) t) e) (ex3_4 F C T T (\lambda (f: 
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
(_: T).(csubst0 O v e1 e2))))))) (drop_drop (Bind b) n0 c e H12 t))) (\lambda 
(H12: (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop n0 O c (CHead e0 
(Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2))))))).(ex3_4_ind F C T T (\lambda (f: F).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop n0 O 
c (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2))))) (or4 (drop (S n0) O (CHead c (Bind 
b) t) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e 
(CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat 
f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (x2: F).(\lambda (x3: C).(\lambda (x4: T).(\lambda (x5: 
T).(\lambda (H13: (eq C e (CHead x3 (Flat x2) x5))).(\lambda (H14: (drop n0 O 
c (CHead x3 (Flat x2) x4))).(\lambda (H15: (subst0 O v x4 x5)).(eq_ind_r C 
(CHead x3 (Flat x2) x5) (\lambda (c0: C).(or4 (drop (S n0) O (CHead c (Bind 
b) t) c0) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C c0 (CHead e0 (Flat f) u2)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C c0 
(CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 (CHead e2 (Flat 
f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (or4_intro1 (drop (S n0) O (CHead c (Bind b) t) (CHead x3 (Flat 
x2) x5)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C (CHead x3 (Flat x2) x5) (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C (CHead x3 (Flat x2) x5) (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C (CHead x3 (Flat x2) x5) (CHead e2 (Flat f) u2))))))) (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u1))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (ex3_4_intro F C 
T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C 
(CHead x3 (Flat x2) x5) (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) 
(CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2))))) x2 x3 x4 x5 (refl_equal C (CHead 
x3 (Flat x2) x5)) (drop_drop (Bind b) n0 c (CHead x3 (Flat x2) x4) H14 t) 
H15)) e H13)))))))) H12)) (\lambda (H12: (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop n0 O c (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))))).(ex3_4_ind F C 
C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e 
(CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop n0 O c (CHead e1 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))) 
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
(x4: C).(\lambda (x5: T).(\lambda (H13: (eq C e (CHead x4 (Flat x2) 
x5))).(\lambda (H14: (drop n0 O c (CHead x3 (Flat x2) x5))).(\lambda (H15: 
(csubst0 O v x3 x4)).(eq_ind_r C (CHead x4 (Flat x2) x5) (\lambda (c0: 
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
(_: T).(csubst0 O v e1 e2))))))))) (or4_intro2 (drop (S n0) O (CHead c (Bind 
b) t) (CHead x4 (Flat x2) x5)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x4 (Flat x2) x5) (CHead e0 
(Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v 
u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C (CHead x4 (Flat x2) x5) (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) 
O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C (CHead x4 (Flat x2) x5) (CHead e2 (Flat f) 
u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
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
c (CHead x3 (Flat x2) x5) H14 t) H15 H16)) e H13)))))))))) H12)) H11)))))) | 
(Flat f) \Rightarrow (\lambda (H7: (eq nat (S n0) (s (Flat f) x1))).(\lambda 
(H8: (drop (r (Flat f) n0) O x0 e)).(let H9 \def (f_equal nat nat (\lambda 
(e0: nat).e0) (S n0) x1 H7) in (let H10 \def (eq_ind_r nat x1 (\lambda (n: 
nat).(csubst0 n v c x0)) H5 (S n0) H9) in (let H11 \def (H x0 v H10 e H8) in 
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
H12 t))) (\lambda (H12: (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O c (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
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
H12)) (\lambda (H12: (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda 
(e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O c (CHead 
e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
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
(ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O c (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2)))))))).(ex4_5_ind F C C T T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat 
f0) u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O c (CHead e1 (Flat f0) u1))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))) (or4 (drop (S n0) 
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
(x5: T).(\lambda (x6: T).(\lambda (H13: (eq C e (CHead x4 (Flat x2) 
x6))).(\lambda (H14: (drop (S n0) O c (CHead x3 (Flat x2) x5))).(\lambda 
(H15: (subst0 O v x5 x6)).(\lambda (H16: (csubst0 O v x3 x4)).(eq_ind_r C 
(CHead x4 (Flat x2) x6) (\lambda (c0: C).(or4 (drop (S n0) O (CHead c (Flat 
f) t) c0) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C c0 (CHead e0 (Flat f0) u2)))))) (\lambda (f0: 
F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Flat f) t) (CHead e0 (Flat f0) u1)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T 
(\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C c0 
(CHead e2 (Flat f0) u)))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 (CHead e2 (Flat 
f0) u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (or4_intro3 (drop (S n0) O (CHead c (Flat f) t) (CHead x4 (Flat 
x2) x6)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: 
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
H13)))))))))) H12)) H11))))))]) H3 (drop_gen_drop k x0 e t n0 H6)))))))) H2)) 
(\lambda (H2: (ex4_3 T C nat (\lambda (_: T).(\lambda (_: C).(\lambda (j: 
nat).(eq nat (S n0) (s k j))))) (\lambda (u2: T).(\lambda (c3: C).(\lambda 
(_: nat).(eq C c2 (CHead c3 k u2))))) (\lambda (u2: T).(\lambda (_: 
C).(\lambda (j: nat).(subst0 j v t u2)))) (\lambda (_: T).(\lambda (c2: 
C).(\lambda (j: nat).(csubst0 j v c c2)))))).(ex4_3_ind T C nat (\lambda (_: 
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
v c x1)).(let H7 \def (eq_ind C c2 (\lambda (c: C).(drop (S n0) O c e)) H1 
(CHead x1 k x0) H4) in ((match k in K return (\lambda (k0: K).((eq nat (S n0) 
(s k0 x2)) \to ((drop (r k0 n0) O x1 e) \to (or4 (drop (S n0) O (CHead c k0 
t) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
k0 t) (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O (CHead c k0 t) (CHead e1 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c k0 t) (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2))))))))))) with [(Bind b) \Rightarrow 
(\lambda (H8: (eq nat (S n0) (s (Bind b) x2))).(\lambda (H9: (drop (r (Bind 
b) n0) O x1 e)).(let H10 \def (f_equal nat nat (\lambda (e0: nat).(match e0 
in nat return (\lambda (_: nat).nat) with [O \Rightarrow n0 | (S n) 
\Rightarrow n])) (S n0) (S x2) H8) in (let H11 \def (eq_ind_r nat x2 (\lambda 
(n: nat).(csubst0 n v c x1)) H6 n0 H10) in (let H12 \def (eq_ind_r nat x2 
(\lambda (n: nat).(subst0 n v t x0)) H5 n0 H10) in (let H13 \def (IHn c x1 v 
H11 e H9) in (or4_ind (drop n0 O c e) (ex3_4 F C T T (\lambda (f: F).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop n0 O 
c (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop n0 O c (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C e (CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop n0 O c (CHead e1 
(Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))) (or4 (drop (S n0) O (CHead c (Bind b) t) e) (ex3_4 F C T T (\lambda 
(f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 
(Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v 
u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
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
(_: T).(csubst0 O v e1 e2)))))))) (\lambda (H14: (drop n0 O c e)).(or4_intro0 
(drop (S n0) O (CHead c (Bind b) t) e) (ex3_4 F C T T (\lambda (f: 
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
(_: T).(csubst0 O v e1 e2))))))) (drop_drop (Bind b) n0 c e H14 t))) (\lambda 
(H14: (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop n0 O c (CHead e0 
(Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2))))))).(ex3_4_ind F C T T (\lambda (f: F).(\lambda 
(e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop n0 O 
c (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2))))) (or4 (drop (S n0) O (CHead c (Bind 
b) t) e) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C e (CHead e0 (Flat f) u2)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e 
(CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat 
f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2)))))))) (\lambda (x3: F).(\lambda (x4: C).(\lambda (x5: T).(\lambda (x6: 
T).(\lambda (H15: (eq C e (CHead x4 (Flat x3) x6))).(\lambda (H16: (drop n0 O 
c (CHead x4 (Flat x3) x5))).(\lambda (H17: (subst0 O v x5 x6)).(eq_ind_r C 
(CHead x4 (Flat x3) x6) (\lambda (c0: C).(or4 (drop (S n0) O (CHead c (Bind 
b) t) c0) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C c0 (CHead e0 (Flat f) u2)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C c0 
(CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) 
u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C c0 (CHead e2 (Flat 
f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 
e2))))))))) (or4_intro1 (drop (S n0) O (CHead c (Bind b) t) (CHead x4 (Flat 
x3) x6)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C (CHead x4 (Flat x3) x6) (CHead e0 (Flat f) u2)))))) 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S 
n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) 
(ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(eq C (CHead x4 (Flat x3) x6) (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) O (CHead c 
(Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(u2: T).(eq C (CHead x4 (Flat x3) x6) (CHead e2 (Flat f) u2))))))) (\lambda 
(f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) u1))))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: 
T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (ex3_4_intro F C 
T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C 
(CHead x4 (Flat x3) x6) (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) 
(CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2))))) x3 x4 x5 x6 (refl_equal C (CHead 
x4 (Flat x3) x6)) (drop_drop (Bind b) n0 c (CHead x4 (Flat x3) x5) H16 t) 
H17)) e H15)))))))) H14)) (\lambda (H14: (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop n0 O c (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))))).(ex3_4_ind F C 
C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e 
(CHead e2 (Flat f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(drop n0 O c (CHead e1 (Flat f) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2))))) 
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
(x5: C).(\lambda (x6: T).(\lambda (H15: (eq C e (CHead x5 (Flat x3) 
x6))).(\lambda (H16: (drop n0 O c (CHead x4 (Flat x3) x6))).(\lambda (H17: 
(csubst0 O v x4 x5)).(eq_ind_r C (CHead x5 (Flat x3) x6) (\lambda (c0: 
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
(_: T).(csubst0 O v e1 e2))))))))) (or4_intro2 (drop (S n0) O (CHead c (Bind 
b) t) (CHead x5 (Flat x3) x6)) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x5 (Flat x3) x6) (CHead e0 
(Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v 
u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C (CHead x5 (Flat x3) x6) (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S n0) 
O (CHead c (Bind b) t) (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C 
C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C (CHead x5 (Flat x3) x6) (CHead e2 (Flat f) 
u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Bind b) t) (CHead e1 (Flat f) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
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
c (CHead x4 (Flat x3) x6) H16 t) H17 H18)) e H15)))))))))) H14)) H13))))))) | 
(Flat f) \Rightarrow (\lambda (H8: (eq nat (S n0) (s (Flat f) x2))).(\lambda 
(H9: (drop (r (Flat f) n0) O x1 e)).(let H10 \def (f_equal nat nat (\lambda 
(e0: nat).e0) (S n0) x2 H8) in (let H11 \def (eq_ind_r nat x2 (\lambda (n: 
nat).(csubst0 n v c x1)) H6 (S n0) H10) in (let H12 \def (eq_ind_r nat x2 
(\lambda (n: nat).(subst0 n v t x0)) H5 (S n0) H10) in (let H13 \def (H x1 v 
H11 e H9) in (or4_ind (drop (S n0) O c e) (ex3_4 F C T T (\lambda (f0: 
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
(Flat f) n0 c e H14 t))) (\lambda (H14: (ex3_4 F C T T (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e0 (Flat 
f) u2)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O c (CHead e0 (Flat f) u1)))))) (\lambda (_: F).(\lambda (_: 
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
H17)) e H15)))))))) H14)) (\lambda (H14: (ex3_4 F C C T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(eq C e (CHead e2 (Flat 
f) u)))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(drop (S n0) O c (CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: 
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
(\lambda (H14: (ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C e (CHead e2 (Flat f) u2))))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(_: T).(drop (S n0) O c (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))))).(ex4_5_ind F C C T T (\lambda 
(f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq 
C e (CHead e2 (Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O c (CHead e1 (Flat f0) 
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
(_: T).(csubst0 O v e1 e2)))))))) (\lambda (x3: F).(\lambda (x4: C).(\lambda 
(x5: C).(\lambda (x6: T).(\lambda (x7: T).(\lambda (H15: (eq C e (CHead x5 
(Flat x3) x7))).(\lambda (H16: (drop (S n0) O c (CHead x4 (Flat x3) 
x6))).(\lambda (H17: (subst0 O v x6 x7)).(\lambda (H18: (csubst0 O v x4 
x5)).(eq_ind_r C (CHead x5 (Flat x3) x7) (\lambda (c0: C).(or4 (drop (S n0) O 
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
O v e1 e2))))))))) (or4_intro3 (drop (S n0) O (CHead c (Flat f) t) (CHead x5 
(Flat x3) x7)) (ex3_4 F C T T (\lambda (f0: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C (CHead x5 (Flat x3) x7) (CHead e0 (Flat f0) 
u2)))))) (\lambda (f0: F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(drop (S n0) O (CHead c (Flat f) t) (CHead e0 (Flat f0) u1)))))) (\lambda 
(_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 
u2)))))) (ex3_4 F C C T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C (CHead x5 (Flat x3) x7) (CHead e2 (Flat f0) u)))))) 
(\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop (S 
n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) u)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 O v e1 e2)))))) 
(ex4_5 F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C (CHead x5 (Flat x3) x7) (CHead e2 (Flat f0) 
u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) (CHead e1 (Flat f0) 
u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) 
(ex4_5_intro F C C T T (\lambda (f0: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(eq C (CHead x5 (Flat x3) x7) (CHead e2 
(Flat f0) u2))))))) (\lambda (f0: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop (S n0) O (CHead c (Flat f) t) 
(CHead e1 (Flat f0) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2)))))) x3 x4 x5 x6 x7 (refl_equal C (CHead x5 (Flat x3) x7)) 
(drop_drop (Flat f) n0 c (CHead x4 (Flat x3) x6) H16 t) H17 H18)) e 
H15)))))))))) H14)) H13)))))))]) H3 (drop_gen_drop k x1 e x0 n0 H7)))))))))) 
H2)) (csubst0_gen_head k c c2 t v (S n0) H0))))))))))) c1)))) n).

