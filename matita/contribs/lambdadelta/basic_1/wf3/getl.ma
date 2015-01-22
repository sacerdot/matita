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

include "Basic-1/wf3/clear.ma".

include "Basic-1/ty3/dec.ma".

theorem wf3_getl_conf:
 \forall (b: B).(\forall (i: nat).(\forall (c1: C).(\forall (d1: C).(\forall 
(v: T).((getl i c1 (CHead d1 (Bind b) v)) \to (\forall (g: G).(\forall (c2: 
C).((wf3 g c1 c2) \to (\forall (w: T).((ty3 g d1 v w) \to (ex2 C (\lambda 
(d2: C).(getl i c2 (CHead d2 (Bind b) v))) (\lambda (d2: C).(wf3 g d1 
d2)))))))))))))
\def
 \lambda (b: B).(\lambda (i: nat).(nat_ind (\lambda (n: nat).(\forall (c1: 
C).(\forall (d1: C).(\forall (v: T).((getl n c1 (CHead d1 (Bind b) v)) \to 
(\forall (g: G).(\forall (c2: C).((wf3 g c1 c2) \to (\forall (w: T).((ty3 g 
d1 v w) \to (ex2 C (\lambda (d2: C).(getl n c2 (CHead d2 (Bind b) v))) 
(\lambda (d2: C).(wf3 g d1 d2))))))))))))) (\lambda (c1: C).(\lambda (d1: 
C).(\lambda (v: T).(\lambda (H: (getl O c1 (CHead d1 (Bind b) v))).(\lambda 
(g: G).(\lambda (c2: C).(\lambda (H0: (wf3 g c1 c2)).(\lambda (w: T).(\lambda 
(H1: (ty3 g d1 v w)).(let H_y \def (wf3_clear_conf c1 (CHead d1 (Bind b) v) 
(getl_gen_O c1 (CHead d1 (Bind b) v) H) g c2 H0) in (let H_x \def 
(wf3_gen_bind1 g d1 c2 v b H_y) in (let H2 \def H_x in (or_ind (ex3_2 C T 
(\lambda (c3: C).(\lambda (_: T).(eq C c2 (CHead c3 (Bind b) v)))) (\lambda 
(c3: C).(\lambda (_: T).(wf3 g d1 c3))) (\lambda (_: C).(\lambda (w0: T).(ty3 
g d1 v w0)))) (ex3 C (\lambda (c3: C).(eq C c2 (CHead c3 (Bind Void) (TSort 
O)))) (\lambda (c3: C).(wf3 g d1 c3)) (\lambda (_: C).(\forall (w0: T).((ty3 
g d1 v w0) \to False)))) (ex2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind 
b) v))) (\lambda (d2: C).(wf3 g d1 d2))) (\lambda (H3: (ex3_2 C T (\lambda 
(c3: C).(\lambda (_: T).(eq C c2 (CHead c3 (Bind b) v)))) (\lambda (c3: 
C).(\lambda (_: T).(wf3 g d1 c3))) (\lambda (_: C).(\lambda (w0: T).(ty3 g d1 
v w0))))).(ex3_2_ind C T (\lambda (c3: C).(\lambda (_: T).(eq C c2 (CHead c3 
(Bind b) v)))) (\lambda (c3: C).(\lambda (_: T).(wf3 g d1 c3))) (\lambda (_: 
C).(\lambda (w0: T).(ty3 g d1 v w0))) (ex2 C (\lambda (d2: C).(getl O c2 
(CHead d2 (Bind b) v))) (\lambda (d2: C).(wf3 g d1 d2))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H4: (eq C c2 (CHead x0 (Bind b) v))).(\lambda 
(H5: (wf3 g d1 x0)).(\lambda (_: (ty3 g d1 v x1)).(eq_ind_r C (CHead x0 (Bind 
b) v) (\lambda (c: C).(ex2 C (\lambda (d2: C).(getl O c (CHead d2 (Bind b) 
v))) (\lambda (d2: C).(wf3 g d1 d2)))) (ex_intro2 C (\lambda (d2: C).(getl O 
(CHead x0 (Bind b) v) (CHead d2 (Bind b) v))) (\lambda (d2: C).(wf3 g d1 d2)) 
x0 (getl_refl b x0 v) H5) c2 H4)))))) H3)) (\lambda (H3: (ex3 C (\lambda (c3: 
C).(eq C c2 (CHead c3 (Bind Void) (TSort O)))) (\lambda (c3: C).(wf3 g d1 
c3)) (\lambda (_: C).(\forall (w0: T).((ty3 g d1 v w0) \to 
False))))).(ex3_ind C (\lambda (c3: C).(eq C c2 (CHead c3 (Bind Void) (TSort 
O)))) (\lambda (c3: C).(wf3 g d1 c3)) (\lambda (_: C).(\forall (w0: T).((ty3 
g d1 v w0) \to False))) (ex2 C (\lambda (d2: C).(getl O c2 (CHead d2 (Bind b) 
v))) (\lambda (d2: C).(wf3 g d1 d2))) (\lambda (x0: C).(\lambda (H4: (eq C c2 
(CHead x0 (Bind Void) (TSort O)))).(\lambda (_: (wf3 g d1 x0)).(\lambda (H6: 
((\forall (w0: T).((ty3 g d1 v w0) \to False)))).(eq_ind_r C (CHead x0 (Bind 
Void) (TSort O)) (\lambda (c: C).(ex2 C (\lambda (d2: C).(getl O c (CHead d2 
(Bind b) v))) (\lambda (d2: C).(wf3 g d1 d2)))) (let H_x0 \def (H6 w H1) in 
(let H7 \def H_x0 in (False_ind (ex2 C (\lambda (d2: C).(getl O (CHead x0 
(Bind Void) (TSort O)) (CHead d2 (Bind b) v))) (\lambda (d2: C).(wf3 g d1 
d2))) H7))) c2 H4))))) H3)) H2))))))))))))) (\lambda (n: nat).(\lambda (H: 
((\forall (c1: C).(\forall (d1: C).(\forall (v: T).((getl n c1 (CHead d1 
(Bind b) v)) \to (\forall (g: G).(\forall (c2: C).((wf3 g c1 c2) \to (\forall 
(w: T).((ty3 g d1 v w) \to (ex2 C (\lambda (d2: C).(getl n c2 (CHead d2 (Bind 
b) v))) (\lambda (d2: C).(wf3 g d1 d2)))))))))))))).(\lambda (c1: C).(C_ind 
(\lambda (c: C).(\forall (d1: C).(\forall (v: T).((getl (S n) c (CHead d1 
(Bind b) v)) \to (\forall (g: G).(\forall (c2: C).((wf3 g c c2) \to (\forall 
(w: T).((ty3 g d1 v w) \to (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 
(Bind b) v))) (\lambda (d2: C).(wf3 g d1 d2)))))))))))) (\lambda (n0: 
nat).(\lambda (d1: C).(\lambda (v: T).(\lambda (H0: (getl (S n) (CSort n0) 
(CHead d1 (Bind b) v))).(\lambda (g: G).(\lambda (c2: C).(\lambda (_: (wf3 g 
(CSort n0) c2)).(\lambda (w: T).(\lambda (_: (ty3 g d1 v w)).(getl_gen_sort 
n0 (S n) (CHead d1 (Bind b) v) H0 (ex2 C (\lambda (d2: C).(getl (S n) c2 
(CHead d2 (Bind b) v))) (\lambda (d2: C).(wf3 g d1 d2))))))))))))) (\lambda 
(c: C).(\lambda (H0: ((\forall (d1: C).(\forall (v: T).((getl (S n) c (CHead 
d1 (Bind b) v)) \to (\forall (g: G).(\forall (c2: C).((wf3 g c c2) \to 
(\forall (w: T).((ty3 g d1 v w) \to (ex2 C (\lambda (d2: C).(getl (S n) c2 
(CHead d2 (Bind b) v))) (\lambda (d2: C).(wf3 g d1 d2))))))))))))).(\lambda 
(k: K).(\lambda (t: T).(\lambda (d1: C).(\lambda (v: T).(\lambda (H1: (getl 
(S n) (CHead c k t) (CHead d1 (Bind b) v))).(\lambda (g: G).(\lambda (c2: 
C).(\lambda (H2: (wf3 g (CHead c k t) c2)).(\lambda (w: T).(\lambda (H3: (ty3 
g d1 v w)).(K_ind (\lambda (k0: K).((wf3 g (CHead c k0 t) c2) \to ((getl (r 
k0 n) c (CHead d1 (Bind b) v)) \to (ex2 C (\lambda (d2: C).(getl (S n) c2 
(CHead d2 (Bind b) v))) (\lambda (d2: C).(wf3 g d1 d2)))))) (\lambda (b0: 
B).(\lambda (H4: (wf3 g (CHead c (Bind b0) t) c2)).(\lambda (H5: (getl (r 
(Bind b0) n) c (CHead d1 (Bind b) v))).(let H_x \def (wf3_gen_bind1 g c c2 t 
b0 H4) in (let H6 \def H_x in (or_ind (ex3_2 C T (\lambda (c3: C).(\lambda 
(_: T).(eq C c2 (CHead c3 (Bind b0) t)))) (\lambda (c3: C).(\lambda (_: 
T).(wf3 g c c3))) (\lambda (_: C).(\lambda (w0: T).(ty3 g c t w0)))) (ex3 C 
(\lambda (c3: C).(eq C c2 (CHead c3 (Bind Void) (TSort O)))) (\lambda (c3: 
C).(wf3 g c c3)) (\lambda (_: C).(\forall (w0: T).((ty3 g c t w0) \to 
False)))) (ex2 C (\lambda (d2: C).(getl (S n) c2 (CHead d2 (Bind b) v))) 
(\lambda (d2: C).(wf3 g d1 d2))) (\lambda (H7: (ex3_2 C T (\lambda (c3: 
C).(\lambda (_: T).(eq C c2 (CHead c3 (Bind b0) t)))) (\lambda (c3: 
C).(\lambda (_: T).(wf3 g c c3))) (\lambda (_: C).(\lambda (w0: T).(ty3 g c t 
w0))))).(ex3_2_ind C T (\lambda (c3: C).(\lambda (_: T).(eq C c2 (CHead c3 
(Bind b0) t)))) (\lambda (c3: C).(\lambda (_: T).(wf3 g c c3))) (\lambda (_: 
C).(\lambda (w0: T).(ty3 g c t w0))) (ex2 C (\lambda (d2: C).(getl (S n) c2 
(CHead d2 (Bind b) v))) (\lambda (d2: C).(wf3 g d1 d2))) (\lambda (x0: 
C).(\lambda (x1: T).(\lambda (H8: (eq C c2 (CHead x0 (Bind b0) t))).(\lambda 
(H9: (wf3 g c x0)).(\lambda (_: (ty3 g c t x1)).(eq_ind_r C (CHead x0 (Bind 
b0) t) (\lambda (c0: C).(ex2 C (\lambda (d2: C).(getl (S n) c0 (CHead d2 
(Bind b) v))) (\lambda (d2: C).(wf3 g d1 d2)))) (let H_x0 \def (H c d1 v H5 g 
x0 H9 w H3) in (let H11 \def H_x0 in (ex2_ind C (\lambda (d2: C).(getl n x0 
(CHead d2 (Bind b) v))) (\lambda (d2: C).(wf3 g d1 d2)) (ex2 C (\lambda (d2: 
C).(getl (S n) (CHead x0 (Bind b0) t) (CHead d2 (Bind b) v))) (\lambda (d2: 
C).(wf3 g d1 d2))) (\lambda (x: C).(\lambda (H12: (getl n x0 (CHead x (Bind 
b) v))).(\lambda (H13: (wf3 g d1 x)).(ex_intro2 C (\lambda (d2: C).(getl (S 
n) (CHead x0 (Bind b0) t) (CHead d2 (Bind b) v))) (\lambda (d2: C).(wf3 g d1 
d2)) x (getl_head (Bind b0) n x0 (CHead x (Bind b) v) H12 t) H13)))) H11))) 
c2 H8)))))) H7)) (\lambda (H7: (ex3 C (\lambda (c3: C).(eq C c2 (CHead c3 
(Bind Void) (TSort O)))) (\lambda (c3: C).(wf3 g c c3)) (\lambda (_: 
C).(\forall (w0: T).((ty3 g c t w0) \to False))))).(ex3_ind C (\lambda (c3: 
C).(eq C c2 (CHead c3 (Bind Void) (TSort O)))) (\lambda (c3: C).(wf3 g c c3)) 
(\lambda (_: C).(\forall (w0: T).((ty3 g c t w0) \to False))) (ex2 C (\lambda 
(d2: C).(getl (S n) c2 (CHead d2 (Bind b) v))) (\lambda (d2: C).(wf3 g d1 
d2))) (\lambda (x0: C).(\lambda (H8: (eq C c2 (CHead x0 (Bind Void) (TSort 
O)))).(\lambda (H9: (wf3 g c x0)).(\lambda (_: ((\forall (w0: T).((ty3 g c t 
w0) \to False)))).(eq_ind_r C (CHead x0 (Bind Void) (TSort O)) (\lambda (c0: 
C).(ex2 C (\lambda (d2: C).(getl (S n) c0 (CHead d2 (Bind b) v))) (\lambda 
(d2: C).(wf3 g d1 d2)))) (let H_x0 \def (H c d1 v H5 g x0 H9 w H3) in (let 
H11 \def H_x0 in (ex2_ind C (\lambda (d2: C).(getl n x0 (CHead d2 (Bind b) 
v))) (\lambda (d2: C).(wf3 g d1 d2)) (ex2 C (\lambda (d2: C).(getl (S n) 
(CHead x0 (Bind Void) (TSort O)) (CHead d2 (Bind b) v))) (\lambda (d2: 
C).(wf3 g d1 d2))) (\lambda (x: C).(\lambda (H12: (getl n x0 (CHead x (Bind 
b) v))).(\lambda (H13: (wf3 g d1 x)).(ex_intro2 C (\lambda (d2: C).(getl (S 
n) (CHead x0 (Bind Void) (TSort O)) (CHead d2 (Bind b) v))) (\lambda (d2: 
C).(wf3 g d1 d2)) x (getl_head (Bind Void) n x0 (CHead x (Bind b) v) H12 
(TSort O)) H13)))) H11))) c2 H8))))) H7)) H6)))))) (\lambda (f: F).(\lambda 
(H4: (wf3 g (CHead c (Flat f) t) c2)).(\lambda (H5: (getl (r (Flat f) n) c 
(CHead d1 (Bind b) v))).(let H_y \def (wf3_gen_flat1 g c c2 t f H4) in (H0 d1 
v H5 g c2 H_y w H3))))) k H2 (getl_gen_S k c (CHead d1 (Bind b) v) t n 
H1)))))))))))))) c1)))) i)).
(* COMMENTS
Initial nodes: 2531
END *)

theorem getl_wf3_trans:
 \forall (i: nat).(\forall (c1: C).(\forall (d1: C).((getl i c1 d1) \to 
(\forall (g: G).(\forall (d2: C).((wf3 g d1 d2) \to (ex2 C (\lambda (c2: 
C).(wf3 g c1 c2)) (\lambda (c2: C).(getl i c2 d2)))))))))
\def
 \lambda (i: nat).(nat_ind (\lambda (n: nat).(\forall (c1: C).(\forall (d1: 
C).((getl n c1 d1) \to (\forall (g: G).(\forall (d2: C).((wf3 g d1 d2) \to 
(ex2 C (\lambda (c2: C).(wf3 g c1 c2)) (\lambda (c2: C).(getl n c2 
d2)))))))))) (\lambda (c1: C).(\lambda (d1: C).(\lambda (H: (getl O c1 
d1)).(\lambda (g: G).(\lambda (d2: C).(\lambda (H0: (wf3 g d1 d2)).(let H_x 
\def (clear_wf3_trans c1 d1 (getl_gen_O c1 d1 H) g d2 H0) in (let H1 \def H_x 
in (ex2_ind C (\lambda (c2: C).(wf3 g c1 c2)) (\lambda (c2: C).(clear c2 d2)) 
(ex2 C (\lambda (c2: C).(wf3 g c1 c2)) (\lambda (c2: C).(getl O c2 d2))) 
(\lambda (x: C).(\lambda (H2: (wf3 g c1 x)).(\lambda (H3: (clear x 
d2)).(ex_intro2 C (\lambda (c2: C).(wf3 g c1 c2)) (\lambda (c2: C).(getl O c2 
d2)) x H2 (getl_intro O x d2 x (drop_refl x) H3))))) H1))))))))) (\lambda (n: 
nat).(\lambda (H: ((\forall (c1: C).(\forall (d1: C).((getl n c1 d1) \to 
(\forall (g: G).(\forall (d2: C).((wf3 g d1 d2) \to (ex2 C (\lambda (c2: 
C).(wf3 g c1 c2)) (\lambda (c2: C).(getl n c2 d2))))))))))).(\lambda (c1: 
C).(C_ind (\lambda (c: C).(\forall (d1: C).((getl (S n) c d1) \to (\forall 
(g: G).(\forall (d2: C).((wf3 g d1 d2) \to (ex2 C (\lambda (c2: C).(wf3 g c 
c2)) (\lambda (c2: C).(getl (S n) c2 d2))))))))) (\lambda (n0: nat).(\lambda 
(d1: C).(\lambda (H0: (getl (S n) (CSort n0) d1)).(\lambda (g: G).(\lambda 
(d2: C).(\lambda (_: (wf3 g d1 d2)).(getl_gen_sort n0 (S n) d1 H0 (ex2 C 
(\lambda (c2: C).(wf3 g (CSort n0) c2)) (\lambda (c2: C).(getl (S n) c2 
d2)))))))))) (\lambda (c: C).(\lambda (H0: ((\forall (d1: C).((getl (S n) c 
d1) \to (\forall (g: G).(\forall (d2: C).((wf3 g d1 d2) \to (ex2 C (\lambda 
(c2: C).(wf3 g c c2)) (\lambda (c2: C).(getl (S n) c2 d2)))))))))).(\lambda 
(k: K).(\lambda (t: T).(\lambda (d1: C).(\lambda (H1: (getl (S n) (CHead c k 
t) d1)).(\lambda (g: G).(\lambda (d2: C).(\lambda (H2: (wf3 g d1 d2)).(K_ind 
(\lambda (k0: K).((getl (r k0 n) c d1) \to (ex2 C (\lambda (c2: C).(wf3 g 
(CHead c k0 t) c2)) (\lambda (c2: C).(getl (S n) c2 d2))))) (\lambda (b: 
B).(\lambda (H3: (getl (r (Bind b) n) c d1)).(let H_x \def (H c d1 H3 g d2 
H2) in (let H4 \def H_x in (ex2_ind C (\lambda (c2: C).(wf3 g c c2)) (\lambda 
(c2: C).(getl n c2 d2)) (ex2 C (\lambda (c2: C).(wf3 g (CHead c (Bind b) t) 
c2)) (\lambda (c2: C).(getl (S n) c2 d2))) (\lambda (x: C).(\lambda (H5: (wf3 
g c x)).(\lambda (H6: (getl n x d2)).(let H_x0 \def (ty3_inference g c t) in 
(let H7 \def H_x0 in (or_ind (ex T (\lambda (t2: T).(ty3 g c t t2))) (\forall 
(t2: T).((ty3 g c t t2) \to False)) (ex2 C (\lambda (c2: C).(wf3 g (CHead c 
(Bind b) t) c2)) (\lambda (c2: C).(getl (S n) c2 d2))) (\lambda (H8: (ex T 
(\lambda (t2: T).(ty3 g c t t2)))).(ex_ind T (\lambda (t2: T).(ty3 g c t t2)) 
(ex2 C (\lambda (c2: C).(wf3 g (CHead c (Bind b) t) c2)) (\lambda (c2: 
C).(getl (S n) c2 d2))) (\lambda (x0: T).(\lambda (H9: (ty3 g c t 
x0)).(ex_intro2 C (\lambda (c2: C).(wf3 g (CHead c (Bind b) t) c2)) (\lambda 
(c2: C).(getl (S n) c2 d2)) (CHead x (Bind b) t) (wf3_bind g c x H5 t x0 H9 
b) (getl_head (Bind b) n x d2 H6 t)))) H8)) (\lambda (H8: ((\forall (t2: 
T).((ty3 g c t t2) \to False)))).(ex_intro2 C (\lambda (c2: C).(wf3 g (CHead 
c (Bind b) t) c2)) (\lambda (c2: C).(getl (S n) c2 d2)) (CHead x (Bind Void) 
(TSort O)) (wf3_void g c x H5 t H8 b) (getl_head (Bind Void) n x d2 H6 (TSort 
O)))) H7)))))) H4))))) (\lambda (f: F).(\lambda (H3: (getl (r (Flat f) n) c 
d1)).(let H_x \def (H0 d1 H3 g d2 H2) in (let H4 \def H_x in (ex2_ind C 
(\lambda (c2: C).(wf3 g c c2)) (\lambda (c2: C).(getl (S n) c2 d2)) (ex2 C 
(\lambda (c2: C).(wf3 g (CHead c (Flat f) t) c2)) (\lambda (c2: C).(getl (S 
n) c2 d2))) (\lambda (x: C).(\lambda (H5: (wf3 g c x)).(\lambda (H6: (getl (S 
n) x d2)).(ex_intro2 C (\lambda (c2: C).(wf3 g (CHead c (Flat f) t) c2)) 
(\lambda (c2: C).(getl (S n) c2 d2)) x (wf3_flat g c x H5 t f) H6)))) H4))))) 
k (getl_gen_S k c d1 t n H1))))))))))) c1)))) i).
(* COMMENTS
Initial nodes: 1139
END *)

