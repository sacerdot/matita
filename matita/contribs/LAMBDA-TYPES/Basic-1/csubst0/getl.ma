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

include "Basic-1/csubst0/clear.ma".

include "Basic-1/csubst0/drop.ma".

include "Basic-1/getl/fwd.ma".

theorem csubst0_getl_ge:
 \forall (i: nat).(\forall (n: nat).((le i n) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (e: C).((getl n c1 
e) \to (getl n c2 e)))))))))
\def
 \lambda (i: nat).(\lambda (n: nat).(\lambda (H: (le i n)).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (v: T).(\lambda (H0: (csubst0 i v c1 
c2)).(\lambda (e: C).(\lambda (H1: (getl n c1 e)).(let H2 \def (getl_gen_all 
c1 e n H1) in (ex2_ind C (\lambda (e0: C).(drop n O c1 e0)) (\lambda (e0: 
C).(clear e0 e)) (getl n c2 e) (\lambda (x: C).(\lambda (H3: (drop n O c1 
x)).(\lambda (H4: (clear x e)).(lt_eq_gt_e i n (getl n c2 e) (\lambda (H5: 
(lt i n)).(getl_intro n c2 e x (csubst0_drop_gt n i H5 c1 c2 v H0 x H3) H4)) 
(\lambda (H5: (eq nat i n)).(let H6 \def (eq_ind_r nat n (\lambda (n0: 
nat).(drop n0 O c1 x)) H3 i H5) in (let H7 \def (eq_ind_r nat n (\lambda (n0: 
nat).(le i n0)) H i H5) in (eq_ind nat i (\lambda (n0: nat).(getl n0 c2 e)) 
(let H8 \def (csubst0_drop_eq i c1 c2 v H0 x H6) in (or4_ind (drop i O c2 x) 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C x (CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop i O c2 (CHead e0 (Flat f) w)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u 
w)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C x (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop i O c2 (CHead e2 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C x (CHead e1 
(Flat f) u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(drop i O c2 (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (getl i c2 e) (\lambda (H9: 
(drop i O c2 x)).(getl_intro i c2 e x H9 H4)) (\lambda (H9: (ex3_4 F C T T 
(\lambda (f: F).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C x 
(CHead e0 (Flat f) u)))))) (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop i O c2 (CHead e0 (Flat f) w)))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u 
w))))))).(ex3_4_ind F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C x (CHead e0 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(drop i O c2 (CHead e0 
(Flat f) w)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 O v u w))))) (getl i c2 e) (\lambda (x0: F).(\lambda (x1: 
C).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H10: (eq C x (CHead x1 (Flat 
x0) x2))).(\lambda (H11: (drop i O c2 (CHead x1 (Flat x0) x3))).(\lambda (_: 
(subst0 O v x2 x3)).(let H13 \def (eq_ind C x (\lambda (c: C).(clear c e)) H4 
(CHead x1 (Flat x0) x2) H10) in (getl_intro i c2 e (CHead x1 (Flat x0) x3) 
H11 (clear_flat x1 e (clear_gen_flat x0 x1 e x2 H13) x0 x3)))))))))) H9)) 
(\lambda (H9: (ex3_4 F C C T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C x (CHead e1 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop i O c2 (CHead e2 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2))))))).(ex3_4_ind F C C T (\lambda (f: F).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(eq C x (CHead e1 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(drop i O c2 
(CHead e2 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2))))) (getl i c2 e) (\lambda (x0: 
F).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H10: (eq C x 
(CHead x1 (Flat x0) x3))).(\lambda (H11: (drop i O c2 (CHead x2 (Flat x0) 
x3))).(\lambda (H12: (csubst0 O v x1 x2)).(let H13 \def (eq_ind C x (\lambda 
(c: C).(clear c e)) H4 (CHead x1 (Flat x0) x3) H10) in (getl_intro i c2 e 
(CHead x2 (Flat x0) x3) H11 (clear_flat x2 e (csubst0_clear_O x1 x2 v H12 e 
(clear_gen_flat x0 x1 e x3 H13)) x0 x3)))))))))) H9)) (\lambda (H9: (ex4_5 F 
C C T T (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C x (CHead e1 (Flat f) u))))))) (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop i O 
c2 (CHead e2 (Flat f) w))))))) (\lambda (_: F).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 O v u w)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2)))))))).(ex4_5_ind F C C T T (\lambda (f: F).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C x (CHead e1 (Flat f) 
u))))))) (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop i O c2 (CHead e2 (Flat f) w))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 O 
v u w)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 O v e1 e2)))))) (getl i c2 e) (\lambda (x0: 
F).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: 
T).(\lambda (H10: (eq C x (CHead x1 (Flat x0) x3))).(\lambda (H11: (drop i O 
c2 (CHead x2 (Flat x0) x4))).(\lambda (_: (subst0 O v x3 x4)).(\lambda (H13: 
(csubst0 O v x1 x2)).(let H14 \def (eq_ind C x (\lambda (c: C).(clear c e)) 
H4 (CHead x1 (Flat x0) x3) H10) in (getl_intro i c2 e (CHead x2 (Flat x0) x4) 
H11 (clear_flat x2 e (csubst0_clear_O x1 x2 v H13 e (clear_gen_flat x0 x1 e 
x3 H14)) x0 x4)))))))))))) H9)) H8)) n H5)))) (\lambda (H5: (lt n 
i)).(le_lt_false i n H H5 (getl n c2 e))))))) H2)))))))))).
(* COMMENTS
Initial nodes: 1525
END *)

theorem csubst0_getl_lt:
 \forall (i: nat).(\forall (n: nat).((lt n i) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (e: C).((getl n c1 
e) \to (or4 (getl n c2 e) (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 
(CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Bind b) u))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2))))))))))))))))
\def
 \lambda (i: nat).(\lambda (n: nat).(\lambda (H: (lt n i)).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (v: T).(\lambda (H0: (csubst0 i v c1 
c2)).(\lambda (e: C).(\lambda (H1: (getl n c1 e)).(let H2 \def (getl_gen_all 
c1 e n H1) in (ex2_ind C (\lambda (e0: C).(drop n O c1 e0)) (\lambda (e0: 
C).(clear e0 e)) (or4 (getl n c2 e) (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 
(CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Bind b) u))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))))) (\lambda (x: 
C).(\lambda (H3: (drop n O c1 x)).(\lambda (H4: (clear x e)).(let H5 \def 
(csubst0_drop_lt n i H c1 c2 v H0 x H3) in (or4_ind (drop n O c2 x) (ex3_4 K 
C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
x (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop n O c2 (CHead e0 k w)))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k n)) v u w)))))) 
(ex3_4 K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(eq C x (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop n O c2 (CHead e2 k u)))))) (\lambda (k: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (s k n)) v e1 
e2)))))) (ex4_5 K C C T T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C x (CHead e1 k u))))))) (\lambda (k: 
K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(drop n O 
c2 (CHead e2 k w))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k n)) v u w)))))) 
(\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i (s k n)) v e1 e2))))))) (or4 (getl n c2 e) (ex3_4 B 
C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C 
e (CHead e0 (Bind b) u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 (CHead e2 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 (Bind b) w))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))))) (\lambda (H6: (drop n O c2 x)).(or4_intro0 (getl n c2 e) 
(ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 (Bind b) u)))))) (\lambda (b: B).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e0 (Bind b) w)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus i (S n)) v u w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 
(CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 
(Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus i (S n)) v e1 e2))))))) (getl_intro n c2 e x H6 H4))) (\lambda (H6: 
(ex3_4 K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C x (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(drop n O c2 (CHead e0 k w)))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k n)) v u 
w))))))).(ex3_4_ind K C T T (\lambda (k: K).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C x (CHead e0 k u)))))) (\lambda (k: K).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(drop n O c2 (CHead e0 k w)))))) (\lambda 
(k: K).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k 
n)) v u w))))) (or4 (getl n c2 e) (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 
(CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Bind b) u))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))))) (\lambda (x0: 
K).(\lambda (x1: C).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H7: (eq C x 
(CHead x1 x0 x2))).(\lambda (H8: (drop n O c2 (CHead x1 x0 x3))).(\lambda 
(H9: (subst0 (minus i (s x0 n)) v x2 x3)).(let H10 \def (eq_ind C x (\lambda 
(c: C).(clear c e)) H4 (CHead x1 x0 x2) H7) in (K_ind (\lambda (k: K).((drop 
n O c2 (CHead x1 k x3)) \to ((subst0 (minus i (s k n)) v x2 x3) \to ((clear 
(CHead x1 k x2) e) \to (or4 (getl n c2 e) (ex3_4 B C T T (\lambda (b: 
B).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 
B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq 
C e (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Bind b) u))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))))))))) (\lambda (b: 
B).(\lambda (H11: (drop n O c2 (CHead x1 (Bind b) x3))).(\lambda (H12: 
(subst0 (minus i (s (Bind b) n)) v x2 x3)).(\lambda (H13: (clear (CHead x1 
(Bind b) x2) e)).(eq_ind_r C (CHead x1 (Bind b) x2) (\lambda (c: C).(or4 
(getl n c2 c) (ex3_4 B C T T (\lambda (b0: B).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C c (CHead e0 (Bind b0) u)))))) (\lambda (b0: 
B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e0 
(Bind b0) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T (\lambda (b0: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 (Bind 
b0) u)))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(getl n c2 (CHead e2 (Bind b0) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C c (CHead e1 (Bind b0) u))))))) (\lambda (b0: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl n 
c2 (CHead e2 (Bind b0) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e1 e2))))))))) (or4_intro1 (getl n c2 
(CHead x1 (Bind b) x2)) (ex3_4 B C T T (\lambda (b0: B).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 (Bind b) x2) (CHead e0 
(Bind b0) u)))))) (\lambda (b0: B).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(getl n c2 (CHead e0 (Bind b0) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 
B C C T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq 
C (CHead x1 (Bind b) x2) (CHead e1 (Bind b0) u)))))) (\lambda (b0: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 (CHead e2 
(Bind b0) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T (\lambda (b0: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead x1 (Bind b) x2) (CHead e1 (Bind b0) u))))))) (\lambda (b0: B).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 
(Bind b0) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus i (S n)) v e1 e2))))))) (ex3_4_intro B C T T (\lambda (b0: B).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 (Bind b) x2) (CHead 
e0 (Bind b0) u)))))) (\lambda (b0: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl n c2 (CHead e0 (Bind b0) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w))))) b x1 x2 x3 (refl_equal C (CHead x1 (Bind b) x2)) (getl_intro n c2 
(CHead x1 (Bind b) x3) (CHead x1 (Bind b) x3) H11 (clear_bind b x1 x3)) H12)) 
e (clear_gen_bind b x1 e x2 H13)))))) (\lambda (f: F).(\lambda (H11: (drop n 
O c2 (CHead x1 (Flat f) x3))).(\lambda (_: (subst0 (minus i (s (Flat f) n)) v 
x2 x3)).(\lambda (H13: (clear (CHead x1 (Flat f) x2) e)).(or4_intro0 (getl n 
c2 e) (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e0 
(Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e1 (Bind b) u))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl n 
c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e1 e2))))))) (getl_intro n c2 e (CHead x1 
(Flat f) x3) H11 (clear_flat x1 e (clear_gen_flat f x1 e x2 H13) f x3))))))) 
x0 H8 H9 H10))))))))) H6)) (\lambda (H6: (ex3_4 K C C T (\lambda (k: 
K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C x (CHead e1 k 
u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(drop n O c2 (CHead e2 k u)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(csubst0 (minus i (s k n)) v e1 e2))))))).(ex3_4_ind 
K C C T (\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq 
C x (CHead e1 k u)))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(drop n O c2 (CHead e2 k u)))))) (\lambda (k: K).(\lambda 
(e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (s k n)) v e1 
e2))))) (or4 (getl n c2 e) (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 
(CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Bind b) u))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))))) (\lambda (x0: 
K).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H7: (eq C x 
(CHead x1 x0 x3))).(\lambda (H8: (drop n O c2 (CHead x2 x0 x3))).(\lambda 
(H9: (csubst0 (minus i (s x0 n)) v x1 x2)).(let H10 \def (eq_ind C x (\lambda 
(c: C).(clear c e)) H4 (CHead x1 x0 x3) H7) in (K_ind (\lambda (k: K).((drop 
n O c2 (CHead x2 k x3)) \to ((csubst0 (minus i (s k n)) v x1 x2) \to ((clear 
(CHead x1 k x3) e) \to (or4 (getl n c2 e) (ex3_4 B C T T (\lambda (b: 
B).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 
B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq 
C e (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Bind b) u))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))))))))) (\lambda (b: 
B).(\lambda (H11: (drop n O c2 (CHead x2 (Bind b) x3))).(\lambda (H12: 
(csubst0 (minus i (s (Bind b) n)) v x1 x2)).(\lambda (H13: (clear (CHead x1 
(Bind b) x3) e)).(eq_ind_r C (CHead x1 (Bind b) x3) (\lambda (c: C).(or4 
(getl n c2 c) (ex3_4 B C T T (\lambda (b0: B).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C c (CHead e0 (Bind b0) u)))))) (\lambda (b0: 
B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e0 
(Bind b0) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: T).(\lambda 
(w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T (\lambda (b0: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 (Bind 
b0) u)))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(getl n c2 (CHead e2 (Bind b0) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C c (CHead e1 (Bind b0) u))))))) (\lambda (b0: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl n 
c2 (CHead e2 (Bind b0) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e1 e2))))))))) (or4_intro2 (getl n c2 
(CHead x1 (Bind b) x3)) (ex3_4 B C T T (\lambda (b0: B).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 (Bind b) x3) (CHead e0 
(Bind b0) u)))))) (\lambda (b0: B).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(getl n c2 (CHead e0 (Bind b0) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 
B C C T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq 
C (CHead x1 (Bind b) x3) (CHead e1 (Bind b0) u)))))) (\lambda (b0: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 (CHead e2 
(Bind b0) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T (\lambda (b0: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C 
(CHead x1 (Bind b) x3) (CHead e1 (Bind b0) u))))))) (\lambda (b0: B).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 
(Bind b0) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus i (S n)) v e1 e2))))))) (ex3_4_intro B C C T (\lambda (b0: B).(\lambda 
(e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x1 (Bind b) x3) (CHead 
e1 (Bind b0) u)))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b0) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2))))) b x1 x2 x3 (refl_equal C (CHead x1 (Bind b) x3)) (getl_intro n 
c2 (CHead x2 (Bind b) x3) (CHead x2 (Bind b) x3) H11 (clear_bind b x2 x3)) 
H12)) e (clear_gen_bind b x1 e x3 H13)))))) (\lambda (f: F).(\lambda (H11: 
(drop n O c2 (CHead x2 (Flat f) x3))).(\lambda (H12: (csubst0 (minus i (s 
(Flat f) n)) v x1 x2)).(\lambda (H13: (clear (CHead x1 (Flat f) x3) e)).(let 
H14 \def (eq_ind nat (minus i n) (\lambda (n0: nat).(csubst0 n0 v x1 x2)) H12 
(S (minus i (S n))) (minus_x_Sy i n H)) in (let H15 \def (csubst0_clear_S x1 
x2 v (minus i (S n)) H14 e (clear_gen_flat f x1 e x3 H13)) in (or4_ind (clear 
x2 e) (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u1: 
T).(\lambda (_: T).(eq C e (CHead e0 (Bind b) u1)))))) (\lambda (b: 
B).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(clear x2 (CHead e0 
(Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 (minus i (S n)) v u1 u2)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear x2 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(eq C e (CHead e1 (Bind b) u1))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(clear 
x2 (CHead e2 (Bind b) u2))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (u2: T).(subst0 (minus i (S n)) v u1 u2)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e1 e2))))))) (or4 (getl n c2 e) (ex3_4 B C 
T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 (Bind b) u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 (CHead e2 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 (Bind b) w))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))))) (\lambda (H16: (clear x2 e)).(or4_intro0 (getl n c2 e) (ex3_4 
B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq 
C e (CHead e0 (Bind b) u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 (CHead e2 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 (Bind b) w))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2))))))) (getl_intro n c2 e (CHead x2 (Flat f) x3) H11 (clear_flat x2 e 
H16 f x3)))) (\lambda (H16: (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(eq C e (CHead e0 (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(clear x2 
(CHead e0 (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 (minus i (S n)) v u1 u2))))))).(ex3_4_ind B C T T 
(\lambda (b: B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C e 
(CHead e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(clear x2 (CHead e0 (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 (minus i (S n)) 
v u1 u2))))) (or4 (getl n c2 e) (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 
(CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Bind b) u))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))))) (\lambda (x4: 
B).(\lambda (x5: C).(\lambda (x6: T).(\lambda (x7: T).(\lambda (H17: (eq C e 
(CHead x5 (Bind x4) x6))).(\lambda (H18: (clear x2 (CHead x5 (Bind x4) 
x7))).(\lambda (H19: (subst0 (minus i (S n)) v x6 x7)).(eq_ind_r C (CHead x5 
(Bind x4) x6) (\lambda (c: C).(or4 (getl n c2 c) (ex3_4 B C T T (\lambda (b: 
B).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e0 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 
B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq 
C c (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 (Bind b) u))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2))))))))) (or4_intro1 
(getl n c2 (CHead x5 (Bind x4) x6)) (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x5 (Bind x4) x6) (CHead 
e0 (Bind b) u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 
B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq 
C (CHead x5 (Bind x4) x6) (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x5 (Bind x4) 
x6) (CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 (Bind b) w))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2))))))) (ex3_4_intro B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C (CHead x5 (Bind x4) x6) (CHead e0 (Bind b) 
u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w))))) x4 x5 
x6 x7 (refl_equal C (CHead x5 (Bind x4) x6)) (getl_intro n c2 (CHead x5 (Bind 
x4) x7) (CHead x2 (Flat f) x3) H11 (clear_flat x2 (CHead x5 (Bind x4) x7) H18 
f x3)) H19)) e H17)))))))) H16)) (\lambda (H16: (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear x2 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 
e2))))))).(ex3_4_ind B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear x2 (CHead e2 (Bind 
b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus i (S n)) v e1 e2))))) (or4 (getl n c2 e) (ex3_4 B C T T 
(\lambda (b: B).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 (Bind b) u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 (CHead e2 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 (Bind b) w))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))))) (\lambda (x4: B).(\lambda (x5: C).(\lambda (x6: C).(\lambda 
(x7: T).(\lambda (H17: (eq C e (CHead x5 (Bind x4) x7))).(\lambda (H18: 
(clear x2 (CHead x6 (Bind x4) x7))).(\lambda (H19: (csubst0 (minus i (S n)) v 
x5 x6)).(eq_ind_r C (CHead x5 (Bind x4) x7) (\lambda (c: C).(or4 (getl n c2 
c) (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u: T).(\lambda 
(_: T).(eq C c (CHead e0 (Bind b) u)))))) (\lambda (b: B).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e0 (Bind b) w)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus i (S n)) v u w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 
(CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C c (CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 
(Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus i (S n)) v e1 e2))))))))) (or4_intro2 (getl n c2 (CHead x5 (Bind x4) 
x7)) (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u: T).(\lambda 
(_: T).(eq C (CHead x5 (Bind x4) x7) (CHead e0 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e0 
(Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x5 (Bind x4) 
x7) (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x5 (Bind x4) x7) (CHead e1 
(Bind b) u))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(getl n c2 (CHead e2 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus i (S n)) v u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2))))))) 
(ex3_4_intro B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C (CHead x5 (Bind x4) x7) (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 
(CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2))))) x4 x5 x6 x7 
(refl_equal C (CHead x5 (Bind x4) x7)) (getl_intro n c2 (CHead x6 (Bind x4) 
x7) (CHead x2 (Flat f) x3) H11 (clear_flat x2 (CHead x6 (Bind x4) x7) H18 f 
x3)) H19)) e H17)))))))) H16)) (\lambda (H16: (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C e 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear x2 (CHead e2 (Bind b) u2))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 (minus i (S n)) v u1 u2)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))))).(ex4_5_ind B C C T T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C e (CHead e1 (Bind 
b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(clear x2 (CHead e2 (Bind b) u2))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
(minus i (S n)) v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))) 
(or4 (getl n c2 e) (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e0 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e0 
(Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e1 (Bind b) u))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl n 
c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e1 e2)))))))) (\lambda (x4: B).(\lambda 
(x5: C).(\lambda (x6: C).(\lambda (x7: T).(\lambda (x8: T).(\lambda (H17: (eq 
C e (CHead x5 (Bind x4) x7))).(\lambda (H18: (clear x2 (CHead x6 (Bind x4) 
x8))).(\lambda (H19: (subst0 (minus i (S n)) v x7 x8)).(\lambda (H20: 
(csubst0 (minus i (S n)) v x5 x6)).(eq_ind_r C (CHead x5 (Bind x4) x7) 
(\lambda (c: C).(or4 (getl n c2 c) (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e0 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 
(CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 (Bind b) u))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2))))))))) (or4_intro3 
(getl n c2 (CHead x5 (Bind x4) x7)) (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x5 (Bind x4) x7) (CHead 
e0 (Bind b) u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 
B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq 
C (CHead x5 (Bind x4) x7) (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x5 (Bind x4) 
x7) (CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 (Bind b) w))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2))))))) (ex4_5_intro B C C T T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x5 (Bind x4) 
x7) (CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 (Bind b) w))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) x4 x5 x6 x7 x8 (refl_equal C (CHead x5 (Bind x4) x7)) 
(getl_intro n c2 (CHead x6 (Bind x4) x8) (CHead x2 (Flat f) x3) H11 
(clear_flat x2 (CHead x6 (Bind x4) x8) H18 f x3)) H19 H20)) e H17)))))))))) 
H16)) H15))))))) x0 H8 H9 H10))))))))) H6)) (\lambda (H6: (ex4_5 K C C T T 
(\lambda (k: K).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C x (CHead e1 k u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(drop n O c2 (CHead e2 k w))))))) (\lambda 
(k: K).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (s k n)) v u w)))))) (\lambda (k: K).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (s k 
n)) v e1 e2)))))))).(ex4_5_ind K C C T T (\lambda (k: K).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C x (CHead e1 k 
u))))))) (\lambda (k: K).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (w: T).(drop n O c2 (CHead e2 k w))))))) (\lambda (k: K).(\lambda 
(_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (s k 
n)) v u w)))))) (\lambda (k: K).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 (minus i (s k n)) v e1 e2)))))) (or4 (getl n 
c2 e) (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u: 
T).(\lambda (_: T).(eq C e (CHead e0 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e0 
(Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e1 (Bind b) u))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl n 
c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e1 e2)))))))) (\lambda (x0: K).(\lambda 
(x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: T).(\lambda (H7: (eq 
C x (CHead x1 x0 x3))).(\lambda (H8: (drop n O c2 (CHead x2 x0 x4))).(\lambda 
(H9: (subst0 (minus i (s x0 n)) v x3 x4)).(\lambda (H10: (csubst0 (minus i (s 
x0 n)) v x1 x2)).(let H11 \def (eq_ind C x (\lambda (c: C).(clear c e)) H4 
(CHead x1 x0 x3) H7) in (K_ind (\lambda (k: K).((drop n O c2 (CHead x2 k x4)) 
\to ((subst0 (minus i (s k n)) v x3 x4) \to ((csubst0 (minus i (s k n)) v x1 
x2) \to ((clear (CHead x1 k x3) e) \to (or4 (getl n c2 e) (ex3_4 B C T T 
(\lambda (b: B).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 (Bind b) u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 (CHead e2 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 (Bind b) w))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2))))))))))))) (\lambda (b: B).(\lambda (H12: (drop n O c2 (CHead x2 
(Bind b) x4))).(\lambda (H13: (subst0 (minus i (s (Bind b) n)) v x3 
x4)).(\lambda (H14: (csubst0 (minus i (s (Bind b) n)) v x1 x2)).(\lambda 
(H15: (clear (CHead x1 (Bind b) x3) e)).(eq_ind_r C (CHead x1 (Bind b) x3) 
(\lambda (c: C).(or4 (getl n c2 c) (ex3_4 B C T T (\lambda (b0: B).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e0 (Bind b0) u)))))) 
(\lambda (b0: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 
(CHead e0 (Bind b0) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T 
(\lambda (b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c 
(CHead e1 (Bind b0) u)))))) (\lambda (b0: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b0) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 (Bind b0) u))))))) 
(\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(getl n c2 (CHead e2 (Bind b0) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2))))))))) (or4_intro3 
(getl n c2 (CHead x1 (Bind b) x3)) (ex3_4 B C T T (\lambda (b0: B).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x1 (Bind b) x3) (CHead 
e0 (Bind b0) u)))))) (\lambda (b0: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl n c2 (CHead e0 (Bind b0) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (ex3_4 B C C T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C (CHead x1 (Bind b) x3) (CHead e1 (Bind b0) u)))))) 
(\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 
(CHead e2 (Bind b0) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda 
(_: T).(eq C (CHead x1 (Bind b) x3) (CHead e1 (Bind b0) u))))))) (\lambda 
(b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e2 (Bind b0) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2))))))) (ex4_5_intro B C C 
T T (\lambda (b0: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: 
T).(\lambda (_: T).(eq C (CHead x1 (Bind b) x3) (CHead e1 (Bind b0) u))))))) 
(\lambda (b0: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(w: T).(getl n c2 (CHead e2 (Bind b0) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))) b x1 x2 x3 x4 
(refl_equal C (CHead x1 (Bind b) x3)) (getl_intro n c2 (CHead x2 (Bind b) x4) 
(CHead x2 (Bind b) x4) H12 (clear_bind b x2 x4)) H13 H14)) e (clear_gen_bind 
b x1 e x3 H15))))))) (\lambda (f: F).(\lambda (H12: (drop n O c2 (CHead x2 
(Flat f) x4))).(\lambda (_: (subst0 (minus i (s (Flat f) n)) v x3 
x4)).(\lambda (H14: (csubst0 (minus i (s (Flat f) n)) v x1 x2)).(\lambda 
(H15: (clear (CHead x1 (Flat f) x3) e)).(let H16 \def (eq_ind nat (minus i n) 
(\lambda (n0: nat).(csubst0 n0 v x1 x2)) H14 (S (minus i (S n))) (minus_x_Sy 
i n H)) in (let H17 \def (csubst0_clear_S x1 x2 v (minus i (S n)) H16 e 
(clear_gen_flat f x1 e x3 H15)) in (or4_ind (clear x2 e) (ex3_4 B C T T 
(\lambda (b: B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C e 
(CHead e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(clear x2 (CHead e0 (Bind b) u2)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 (minus i (S n)) 
v u1 u2)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear x2 (CHead e2 (Bind 
b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C e 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear x2 (CHead e2 (Bind b) u2))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 (minus i (S n)) v u1 u2)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2))))))) (or4 (getl n c2 e) (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 
(CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Bind b) u))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))))) (\lambda (H18: 
(clear x2 e)).(or4_intro0 (getl n c2 e) (ex3_4 B C T T (\lambda (b: 
B).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e0 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 
B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq 
C e (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C e (CHead e1 (Bind b) u))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2))))))) (getl_intro n c2 e 
(CHead x2 (Flat f) x4) H12 (clear_flat x2 e H18 f x4)))) (\lambda (H18: 
(ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: 
T).(eq C e (CHead e0 (Bind b) u1)))))) (\lambda (b: B).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (u2: T).(clear x2 (CHead e0 (Bind b) u2)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
(minus i (S n)) v u1 u2))))))).(ex3_4_ind B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u1: T).(\lambda (_: T).(eq C e (CHead e0 (Bind b) u1)))))) 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: T).(clear x2 
(CHead e0 (Bind b) u2)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (u2: T).(subst0 (minus i (S n)) v u1 u2))))) (or4 (getl n c2 e) 
(ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e0 (Bind b) u)))))) (\lambda (b: B).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e0 (Bind b) w)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus i (S n)) v u w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 
(CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C e (CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 
(Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus i (S n)) v e1 e2)))))))) (\lambda (x5: B).(\lambda (x6: C).(\lambda 
(x7: T).(\lambda (x8: T).(\lambda (H19: (eq C e (CHead x6 (Bind x5) 
x7))).(\lambda (H20: (clear x2 (CHead x6 (Bind x5) x8))).(\lambda (H21: 
(subst0 (minus i (S n)) v x7 x8)).(eq_ind_r C (CHead x6 (Bind x5) x7) 
(\lambda (c: C).(or4 (getl n c2 c) (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e0 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 
(CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 (Bind b) u))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2))))))))) (or4_intro1 
(getl n c2 (CHead x6 (Bind x5) x7)) (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x6 (Bind x5) x7) (CHead 
e0 (Bind b) u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 
B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq 
C (CHead x6 (Bind x5) x7) (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x6 (Bind x5) 
x7) (CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 (Bind b) w))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2))))))) (ex3_4_intro B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C (CHead x6 (Bind x5) x7) (CHead e0 (Bind b) 
u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w))))) x5 x6 
x7 x8 (refl_equal C (CHead x6 (Bind x5) x7)) (getl_intro n c2 (CHead x6 (Bind 
x5) x8) (CHead x2 (Flat f) x4) H12 (clear_flat x2 (CHead x6 (Bind x5) x8) H20 
f x4)) H21)) e H19)))))))) H18)) (\lambda (H18: (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(clear x2 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 
e2))))))).(ex3_4_ind B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(clear x2 (CHead e2 (Bind 
b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(csubst0 (minus i (S n)) v e1 e2))))) (or4 (getl n c2 e) (ex3_4 B C T T 
(\lambda (b: B).(\lambda (e0: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e0 (Bind b) u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (w: T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C e (CHead e1 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 (CHead e2 
(Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C e 
(CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 (Bind b) w))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))))) (\lambda (x5: B).(\lambda (x6: C).(\lambda (x7: C).(\lambda 
(x8: T).(\lambda (H19: (eq C e (CHead x6 (Bind x5) x8))).(\lambda (H20: 
(clear x2 (CHead x7 (Bind x5) x8))).(\lambda (H21: (csubst0 (minus i (S n)) v 
x6 x7)).(eq_ind_r C (CHead x6 (Bind x5) x8) (\lambda (c: C).(or4 (getl n c2 
c) (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u: T).(\lambda 
(_: T).(eq C c (CHead e0 (Bind b) u)))))) (\lambda (b: B).(\lambda (e0: 
C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e0 (Bind b) w)))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus i (S n)) v u w)))))) (ex3_4 B C C T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(eq C c (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 
(CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: 
T).(eq C c (CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 
(Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
(minus i (S n)) v e1 e2))))))))) (or4_intro2 (getl n c2 (CHead x6 (Bind x5) 
x8)) (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda (u: T).(\lambda 
(_: T).(eq C (CHead x6 (Bind x5) x8) (CHead e0 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e0 
(Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C (CHead x6 (Bind x5) 
x8) (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x6 (Bind x5) x8) (CHead e1 
(Bind b) u))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (w: T).(getl n c2 (CHead e2 (Bind b) w))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 
(minus i (S n)) v u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2))))))) 
(ex3_4_intro B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(eq C (CHead x6 (Bind x5) x8) (CHead e1 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 
(CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2))))) x5 x6 x7 x8 
(refl_equal C (CHead x6 (Bind x5) x8)) (getl_intro n c2 (CHead x7 (Bind x5) 
x8) (CHead x2 (Flat f) x4) H12 (clear_flat x2 (CHead x7 (Bind x5) x8) H20 f 
x4)) H21)) e H19)))))))) H18)) (\lambda (H18: (ex4_5 B C C T T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C e 
(CHead e1 (Bind b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (u2: T).(clear x2 (CHead e2 (Bind b) u2))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 (minus i (S n)) v u1 u2)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))))).(ex4_5_ind B C C T T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(eq C e (CHead e1 (Bind 
b) u1))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (u2: T).(clear x2 (CHead e2 (Bind b) u2))))))) (\lambda (_: 
B).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
(minus i (S n)) v u1 u2)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))) 
(or4 (getl n c2 e) (ex3_4 B C T T (\lambda (b: B).(\lambda (e0: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e0 (Bind b) u)))))) (\lambda (b: 
B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e0 
(Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T (\lambda (b: 
B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C e (CHead e1 (Bind 
b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (u: 
T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2)))))) 
(ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda 
(u: T).(\lambda (_: T).(eq C e (CHead e1 (Bind b) u))))))) (\lambda (b: 
B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: T).(getl n 
c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda 
(_: T).(csubst0 (minus i (S n)) v e1 e2)))))))) (\lambda (x5: B).(\lambda 
(x6: C).(\lambda (x7: C).(\lambda (x8: T).(\lambda (x9: T).(\lambda (H19: (eq 
C e (CHead x6 (Bind x5) x8))).(\lambda (H20: (clear x2 (CHead x7 (Bind x5) 
x9))).(\lambda (H21: (subst0 (minus i (S n)) v x8 x9)).(\lambda (H22: 
(csubst0 (minus i (S n)) v x6 x7)).(eq_ind_r C (CHead x6 (Bind x5) x8) 
(\lambda (c: C).(or4 (getl n c2 c) (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e0 (Bind b) u)))))) 
(\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda (w: T).(getl n c2 
(CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: C).(\lambda (u: 
T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 B C C T 
(\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq C c 
(CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) (\lambda (_: 
B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u: T).(\lambda (_: T).(eq C c (CHead e1 (Bind b) u))))))) 
(\lambda (b: B).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (w: 
T).(getl n c2 (CHead e2 (Bind b) w))))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v 
u w)))))) (\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: 
T).(\lambda (_: T).(csubst0 (minus i (S n)) v e1 e2))))))))) (or4_intro3 
(getl n c2 (CHead x6 (Bind x5) x8)) (ex3_4 B C T T (\lambda (b: B).(\lambda 
(e0: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x6 (Bind x5) x8) (CHead 
e0 (Bind b) u)))))) (\lambda (b: B).(\lambda (e0: C).(\lambda (_: T).(\lambda 
(w: T).(getl n c2 (CHead e0 (Bind b) w)))))) (\lambda (_: B).(\lambda (_: 
C).(\lambda (u: T).(\lambda (w: T).(subst0 (minus i (S n)) v u w)))))) (ex3_4 
B C C T (\lambda (b: B).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(eq 
C (CHead x6 (Bind x5) x8) (CHead e1 (Bind b) u)))))) (\lambda (b: B).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u: T).(getl n c2 (CHead e2 (Bind b) u)))))) 
(\lambda (_: B).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(csubst0 
(minus i (S n)) v e1 e2)))))) (ex4_5 B C C T T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x6 (Bind x5) 
x8) (CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 (Bind b) w))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2))))))) (ex4_5_intro B C C T T (\lambda (b: B).(\lambda (e1: 
C).(\lambda (_: C).(\lambda (u: T).(\lambda (_: T).(eq C (CHead x6 (Bind x5) 
x8) (CHead e1 (Bind b) u))))))) (\lambda (b: B).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (_: T).(\lambda (w: T).(getl n c2 (CHead e2 (Bind b) w))))))) 
(\lambda (_: B).(\lambda (_: C).(\lambda (_: C).(\lambda (u: T).(\lambda (w: 
T).(subst0 (minus i (S n)) v u w)))))) (\lambda (_: B).(\lambda (e1: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 (minus i (S n)) 
v e1 e2)))))) x5 x6 x7 x8 x9 (refl_equal C (CHead x6 (Bind x5) x8)) 
(getl_intro n c2 (CHead x7 (Bind x5) x9) (CHead x2 (Flat f) x4) H12 
(clear_flat x2 (CHead x7 (Bind x5) x9) H20 f x4)) H21 H22)) e H19)))))))))) 
H18)) H17)))))))) x0 H8 H9 H10 H11))))))))))) H6)) H5))))) H2)))))))))).
(* COMMENTS
Initial nodes: 17179
END *)

theorem csubst0_getl_ge_back:
 \forall (i: nat).(\forall (n: nat).((le i n) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (e: C).((getl n c2 
e) \to (getl n c1 e)))))))))
\def
 \lambda (i: nat).(\lambda (n: nat).(\lambda (H: (le i n)).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (v: T).(\lambda (H0: (csubst0 i v c1 
c2)).(\lambda (e: C).(\lambda (H1: (getl n c2 e)).(let H2 \def (getl_gen_all 
c2 e n H1) in (ex2_ind C (\lambda (e0: C).(drop n O c2 e0)) (\lambda (e0: 
C).(clear e0 e)) (getl n c1 e) (\lambda (x: C).(\lambda (H3: (drop n O c2 
x)).(\lambda (H4: (clear x e)).(lt_eq_gt_e i n (getl n c1 e) (\lambda (H5: 
(lt i n)).(getl_intro n c1 e x (csubst0_drop_gt_back n i H5 c1 c2 v H0 x H3) 
H4)) (\lambda (H5: (eq nat i n)).(let H6 \def (eq_ind_r nat n (\lambda (n0: 
nat).(drop n0 O c2 x)) H3 i H5) in (let H7 \def (eq_ind_r nat n (\lambda (n0: 
nat).(le i n0)) H i H5) in (eq_ind nat i (\lambda (n0: nat).(getl n0 c1 e)) 
(let H8 \def (csubst0_drop_eq_back i c1 c2 v H0 x H6) in (or4_ind (drop i O 
c1 x) (ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C x (CHead e0 (Flat f) u2)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop i O c1 (CHead e0 
(Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (ex3_4 F C C T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (u: T).(eq C x (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop i O c1 
(CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2)))))) (ex4_5 F C C T T (\lambda (f: 
F).(\lambda (_: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C x 
(CHead e2 (Flat f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(drop i O c1 (CHead e1 (Flat f) u1))))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda 
(e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 O v e1 e2))))))) (getl i c1 
e) (\lambda (H9: (drop i O c1 x)).(getl_intro i c1 e x H9 H4)) (\lambda (H9: 
(ex3_4 F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: T).(\lambda (u2: 
T).(eq C x (CHead e0 (Flat f) u2)))))) (\lambda (f: F).(\lambda (e0: 
C).(\lambda (u1: T).(\lambda (_: T).(drop i O c1 (CHead e0 (Flat f) u1)))))) 
(\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v 
u1 u2))))))).(ex3_4_ind F C T T (\lambda (f: F).(\lambda (e0: C).(\lambda (_: 
T).(\lambda (u2: T).(eq C x (CHead e0 (Flat f) u2)))))) (\lambda (f: 
F).(\lambda (e0: C).(\lambda (u1: T).(\lambda (_: T).(drop i O c1 (CHead e0 
(Flat f) u1)))))) (\lambda (_: F).(\lambda (_: C).(\lambda (u1: T).(\lambda 
(u2: T).(subst0 O v u1 u2))))) (getl i c1 e) (\lambda (x0: F).(\lambda (x1: 
C).(\lambda (x2: T).(\lambda (x3: T).(\lambda (H10: (eq C x (CHead x1 (Flat 
x0) x3))).(\lambda (H11: (drop i O c1 (CHead x1 (Flat x0) x2))).(\lambda (_: 
(subst0 O v x2 x3)).(let H13 \def (eq_ind C x (\lambda (c: C).(clear c e)) H4 
(CHead x1 (Flat x0) x3) H10) in (getl_intro i c1 e (CHead x1 (Flat x0) x2) 
H11 (clear_flat x1 e (clear_gen_flat x0 x1 e x3 H13) x0 x2)))))))))) H9)) 
(\lambda (H9: (ex3_4 F C C T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: 
C).(\lambda (u: T).(eq C x (CHead e2 (Flat f) u)))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop i O c1 (CHead e1 
(Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(csubst0 O v e1 e2))))))).(ex3_4_ind F C C T (\lambda (f: F).(\lambda 
(_: C).(\lambda (e2: C).(\lambda (u: T).(eq C x (CHead e2 (Flat f) u)))))) 
(\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u: T).(drop i O c1 
(CHead e1 (Flat f) u)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: 
C).(\lambda (_: T).(csubst0 O v e1 e2))))) (getl i c1 e) (\lambda (x0: 
F).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (H10: (eq C x 
(CHead x2 (Flat x0) x3))).(\lambda (H11: (drop i O c1 (CHead x1 (Flat x0) 
x3))).(\lambda (H12: (csubst0 O v x1 x2)).(let H13 \def (eq_ind C x (\lambda 
(c: C).(clear c e)) H4 (CHead x2 (Flat x0) x3) H10) in (getl_intro i c1 e 
(CHead x1 (Flat x0) x3) H11 (clear_flat x1 e (csubst0_clear_O_back x1 x2 v 
H12 e (clear_gen_flat x0 x2 e x3 H13)) x0 x3)))))))))) H9)) (\lambda (H9: 
(ex4_5 F C C T T (\lambda (f: F).(\lambda (_: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (u2: T).(eq C x (CHead e2 (Flat f) u2))))))) (\lambda (f: 
F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(drop i 
O c1 (CHead e1 (Flat f) u1))))))) (\lambda (_: F).(\lambda (_: C).(\lambda 
(_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 O v u1 u2)))))) (\lambda (_: 
F).(\lambda (e1: C).(\lambda (e2: C).(\lambda (_: T).(\lambda (_: T).(csubst0 
O v e1 e2)))))))).(ex4_5_ind F C C T T (\lambda (f: F).(\lambda (_: 
C).(\lambda (e2: C).(\lambda (_: T).(\lambda (u2: T).(eq C x (CHead e2 (Flat 
f) u2))))))) (\lambda (f: F).(\lambda (e1: C).(\lambda (_: C).(\lambda (u1: 
T).(\lambda (_: T).(drop i O c1 (CHead e1 (Flat f) u1))))))) (\lambda (_: 
F).(\lambda (_: C).(\lambda (_: C).(\lambda (u1: T).(\lambda (u2: T).(subst0 
O v u1 u2)))))) (\lambda (_: F).(\lambda (e1: C).(\lambda (e2: C).(\lambda 
(_: T).(\lambda (_: T).(csubst0 O v e1 e2)))))) (getl i c1 e) (\lambda (x0: 
F).(\lambda (x1: C).(\lambda (x2: C).(\lambda (x3: T).(\lambda (x4: 
T).(\lambda (H10: (eq C x (CHead x2 (Flat x0) x4))).(\lambda (H11: (drop i O 
c1 (CHead x1 (Flat x0) x3))).(\lambda (_: (subst0 O v x3 x4)).(\lambda (H13: 
(csubst0 O v x1 x2)).(let H14 \def (eq_ind C x (\lambda (c: C).(clear c e)) 
H4 (CHead x2 (Flat x0) x4) H10) in (getl_intro i c1 e (CHead x1 (Flat x0) x3) 
H11 (clear_flat x1 e (csubst0_clear_O_back x1 x2 v H13 e (clear_gen_flat x0 
x2 e x4 H14)) x0 x3)))))))))))) H9)) H8)) n H5)))) (\lambda (H5: (lt n 
i)).(le_lt_false i n H H5 (getl n c1 e))))))) H2)))))))))).
(* COMMENTS
Initial nodes: 1525
END *)

theorem csubst0_getl_lt_back:
 \forall (n: nat).(\forall (i: nat).((lt n i) \to (\forall (c1: C).(\forall 
(c2: C).(\forall (v: T).((csubst0 i v c1 c2) \to (\forall (e2: C).((getl n c2 
e2) \to (or (getl n c1 e2) (ex2 C (\lambda (e1: C).(csubst0 (minus i n) v e1 
e2)) (\lambda (e1: C).(getl n c1 e1))))))))))))
\def
 \lambda (n: nat).(\lambda (i: nat).(\lambda (H: (lt n i)).(\lambda (c1: 
C).(\lambda (c2: C).(\lambda (v: T).(\lambda (H0: (csubst0 i v c1 
c2)).(\lambda (e2: C).(\lambda (H1: (getl n c2 e2)).(let H2 \def 
(getl_gen_all c2 e2 n H1) in (ex2_ind C (\lambda (e: C).(drop n O c2 e)) 
(\lambda (e: C).(clear e e2)) (or (getl n c1 e2) (ex2 C (\lambda (e1: 
C).(csubst0 (minus i n) v e1 e2)) (\lambda (e1: C).(getl n c1 e1)))) (\lambda 
(x: C).(\lambda (H3: (drop n O c2 x)).(\lambda (H4: (clear x e2)).(let H_x 
\def (csubst0_drop_lt_back n i H c1 c2 v H0 x H3) in (let H5 \def H_x in 
(or_ind (drop n O c1 x) (ex2 C (\lambda (e1: C).(csubst0 (minus i n) v e1 x)) 
(\lambda (e1: C).(drop n O c1 e1))) (or (getl n c1 e2) (ex2 C (\lambda (e1: 
C).(csubst0 (minus i n) v e1 e2)) (\lambda (e1: C).(getl n c1 e1)))) (\lambda 
(H6: (drop n O c1 x)).(or_introl (getl n c1 e2) (ex2 C (\lambda (e1: 
C).(csubst0 (minus i n) v e1 e2)) (\lambda (e1: C).(getl n c1 e1))) 
(getl_intro n c1 e2 x H6 H4))) (\lambda (H6: (ex2 C (\lambda (e1: C).(csubst0 
(minus i n) v e1 x)) (\lambda (e1: C).(drop n O c1 e1)))).(ex2_ind C (\lambda 
(e1: C).(csubst0 (minus i n) v e1 x)) (\lambda (e1: C).(drop n O c1 e1)) (or 
(getl n c1 e2) (ex2 C (\lambda (e1: C).(csubst0 (minus i n) v e1 e2)) 
(\lambda (e1: C).(getl n c1 e1)))) (\lambda (x0: C).(\lambda (H7: (csubst0 
(minus i n) v x0 x)).(\lambda (H8: (drop n O c1 x0)).(let H_x0 \def 
(csubst0_clear_trans x0 x v (minus i n) H7 e2 H4) in (let H9 \def H_x0 in 
(or_ind (clear x0 e2) (ex2 C (\lambda (e1: C).(csubst0 (minus i n) v e1 e2)) 
(\lambda (e1: C).(clear x0 e1))) (or (getl n c1 e2) (ex2 C (\lambda (e1: 
C).(csubst0 (minus i n) v e1 e2)) (\lambda (e1: C).(getl n c1 e1)))) (\lambda 
(H10: (clear x0 e2)).(or_introl (getl n c1 e2) (ex2 C (\lambda (e1: 
C).(csubst0 (minus i n) v e1 e2)) (\lambda (e1: C).(getl n c1 e1))) 
(getl_intro n c1 e2 x0 H8 H10))) (\lambda (H10: (ex2 C (\lambda (e1: 
C).(csubst0 (minus i n) v e1 e2)) (\lambda (e1: C).(clear x0 e1)))).(ex2_ind 
C (\lambda (e1: C).(csubst0 (minus i n) v e1 e2)) (\lambda (e1: C).(clear x0 
e1)) (or (getl n c1 e2) (ex2 C (\lambda (e1: C).(csubst0 (minus i n) v e1 
e2)) (\lambda (e1: C).(getl n c1 e1)))) (\lambda (x1: C).(\lambda (H11: 
(csubst0 (minus i n) v x1 e2)).(\lambda (H12: (clear x0 x1)).(or_intror (getl 
n c1 e2) (ex2 C (\lambda (e1: C).(csubst0 (minus i n) v e1 e2)) (\lambda (e1: 
C).(getl n c1 e1))) (ex_intro2 C (\lambda (e1: C).(csubst0 (minus i n) v e1 
e2)) (\lambda (e1: C).(getl n c1 e1)) x1 H11 (getl_intro n c1 x1 x0 H8 
H12)))))) H10)) H9)))))) H6)) H5)))))) H2)))))))))).
(* COMMENTS
Initial nodes: 801
END *)

