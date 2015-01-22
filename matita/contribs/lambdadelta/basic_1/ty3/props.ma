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

include "Basic-1/ty3/fwd.ma".

include "Basic-1/pc3/fwd.ma".

theorem ty3_lift:
 \forall (g: G).(\forall (e: C).(\forall (t1: T).(\forall (t2: T).((ty3 g e 
t1 t2) \to (\forall (c: C).(\forall (d: nat).(\forall (h: nat).((drop h d c 
e) \to (ty3 g c (lift h d t1) (lift h d t2))))))))))
\def
 \lambda (g: G).(\lambda (e: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (ty3 g e t1 t2)).(ty3_ind g (\lambda (c: C).(\lambda (t: T).(\lambda (t0: 
T).(\forall (c0: C).(\forall (d: nat).(\forall (h: nat).((drop h d c0 c) \to 
(ty3 g c0 (lift h d t) (lift h d t0))))))))) (\lambda (c: C).(\lambda (t0: 
T).(\lambda (t: T).(\lambda (_: (ty3 g c t0 t)).(\lambda (H1: ((\forall (c0: 
C).(\forall (d: nat).(\forall (h: nat).((drop h d c0 c) \to (ty3 g c0 (lift h 
d t0) (lift h d t)))))))).(\lambda (u: T).(\lambda (t3: T).(\lambda (_: (ty3 
g c u t3)).(\lambda (H3: ((\forall (c0: C).(\forall (d: nat).(\forall (h: 
nat).((drop h d c0 c) \to (ty3 g c0 (lift h d u) (lift h d 
t3)))))))).(\lambda (H4: (pc3 c t3 t0)).(\lambda (c0: C).(\lambda (d: 
nat).(\lambda (h: nat).(\lambda (H5: (drop h d c0 c)).(ty3_conv g c0 (lift h 
d t0) (lift h d t) (H1 c0 d h H5) (lift h d u) (lift h d t3) (H3 c0 d h H5) 
(pc3_lift c0 c h d H5 t3 t0 H4)))))))))))))))) (\lambda (c: C).(\lambda (m: 
nat).(\lambda (c0: C).(\lambda (d: nat).(\lambda (h: nat).(\lambda (_: (drop 
h d c0 c)).(eq_ind_r T (TSort m) (\lambda (t: T).(ty3 g c0 t (lift h d (TSort 
(next g m))))) (eq_ind_r T (TSort (next g m)) (\lambda (t: T).(ty3 g c0 
(TSort m) t)) (ty3_sort g c0 m) (lift h d (TSort (next g m))) (lift_sort 
(next g m) h d)) (lift h d (TSort m)) (lift_sort m h d)))))))) (\lambda (n: 
nat).(\lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (H0: (getl n c 
(CHead d (Bind Abbr) u))).(\lambda (t: T).(\lambda (H1: (ty3 g d u 
t)).(\lambda (H2: ((\forall (c0: C).(\forall (d0: nat).(\forall (h: 
nat).((drop h d0 c0 d) \to (ty3 g c0 (lift h d0 u) (lift h d0 
t)))))))).(\lambda (c0: C).(\lambda (d0: nat).(\lambda (h: nat).(\lambda (H3: 
(drop h d0 c0 c)).(lt_le_e n d0 (ty3 g c0 (lift h d0 (TLRef n)) (lift h d0 
(lift (S n) O t))) (\lambda (H4: (lt n d0)).(let H5 \def (drop_getl_trans_le 
n d0 (le_S_n n d0 (le_S (S n) d0 H4)) c0 c h H3 (CHead d (Bind Abbr) u) H0) 
in (ex3_2_ind C C (\lambda (e0: C).(\lambda (_: C).(drop n O c0 e0))) 
(\lambda (e0: C).(\lambda (e1: C).(drop h (minus d0 n) e0 e1))) (\lambda (_: 
C).(\lambda (e1: C).(clear e1 (CHead d (Bind Abbr) u)))) (ty3 g c0 (lift h d0 
(TLRef n)) (lift h d0 (lift (S n) O t))) (\lambda (x0: C).(\lambda (x1: 
C).(\lambda (H6: (drop n O c0 x0)).(\lambda (H7: (drop h (minus d0 n) x0 
x1)).(\lambda (H8: (clear x1 (CHead d (Bind Abbr) u))).(let H9 \def (eq_ind 
nat (minus d0 n) (\lambda (n0: nat).(drop h n0 x0 x1)) H7 (S (minus d0 (S 
n))) (minus_x_Sy d0 n H4)) in (let H10 \def (drop_clear_S x1 x0 h (minus d0 
(S n)) H9 Abbr d u H8) in (ex2_ind C (\lambda (c1: C).(clear x0 (CHead c1 
(Bind Abbr) (lift h (minus d0 (S n)) u)))) (\lambda (c1: C).(drop h (minus d0 
(S n)) c1 d)) (ty3 g c0 (lift h d0 (TLRef n)) (lift h d0 (lift (S n) O t))) 
(\lambda (x: C).(\lambda (H11: (clear x0 (CHead x (Bind Abbr) (lift h (minus 
d0 (S n)) u)))).(\lambda (H12: (drop h (minus d0 (S n)) x d)).(eq_ind_r T 
(TLRef n) (\lambda (t0: T).(ty3 g c0 t0 (lift h d0 (lift (S n) O t)))) 
(eq_ind nat (plus (S n) (minus d0 (S n))) (\lambda (n0: nat).(ty3 g c0 (TLRef 
n) (lift h n0 (lift (S n) O t)))) (eq_ind_r T (lift (S n) O (lift h (minus d0 
(S n)) t)) (\lambda (t0: T).(ty3 g c0 (TLRef n) t0)) (eq_ind nat d0 (\lambda 
(_: nat).(ty3 g c0 (TLRef n) (lift (S n) O (lift h (minus d0 (S n)) t)))) 
(ty3_abbr g n c0 x (lift h (minus d0 (S n)) u) (getl_intro n c0 (CHead x 
(Bind Abbr) (lift h (minus d0 (S n)) u)) x0 H6 H11) (lift h (minus d0 (S n)) 
t) (H2 x (minus d0 (S n)) h H12)) (plus (S n) (minus d0 (S n))) 
(le_plus_minus (S n) d0 H4)) (lift h (plus (S n) (minus d0 (S n))) (lift (S 
n) O t)) (lift_d t h (S n) (minus d0 (S n)) O (le_O_n (minus d0 (S n))))) d0 
(le_plus_minus_r (S n) d0 H4)) (lift h d0 (TLRef n)) (lift_lref_lt n h d0 
H4))))) H10)))))))) H5))) (\lambda (H4: (le d0 n)).(eq_ind_r T (TLRef (plus n 
h)) (\lambda (t0: T).(ty3 g c0 t0 (lift h d0 (lift (S n) O t)))) (eq_ind nat 
(S n) (\lambda (_: nat).(ty3 g c0 (TLRef (plus n h)) (lift h d0 (lift (S n) O 
t)))) (eq_ind_r T (lift (plus h (S n)) O t) (\lambda (t0: T).(ty3 g c0 (TLRef 
(plus n h)) t0)) (eq_ind_r nat (plus (S n) h) (\lambda (n0: nat).(ty3 g c0 
(TLRef (plus n h)) (lift n0 O t))) (ty3_abbr g (plus n h) c0 d u 
(drop_getl_trans_ge n c0 c d0 h H3 (CHead d (Bind Abbr) u) H0 H4) t H1) (plus 
h (S n)) (plus_sym h (S n))) (lift h d0 (lift (S n) O t)) (lift_free t (S n) 
h O d0 (le_S d0 n H4) (le_O_n d0))) (plus n (S O)) (eq_ind_r nat (plus (S O) 
n) (\lambda (n0: nat).(eq nat (S n) n0)) (refl_equal nat (plus (S O) n)) 
(plus n (S O)) (plus_sym n (S O)))) (lift h d0 (TLRef n)) (lift_lref_ge n h 
d0 H4)))))))))))))))) (\lambda (n: nat).(\lambda (c: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (H0: (getl n c (CHead d (Bind Abst) u))).(\lambda 
(t: T).(\lambda (H1: (ty3 g d u t)).(\lambda (H2: ((\forall (c0: C).(\forall 
(d0: nat).(\forall (h: nat).((drop h d0 c0 d) \to (ty3 g c0 (lift h d0 u) 
(lift h d0 t)))))))).(\lambda (c0: C).(\lambda (d0: nat).(\lambda (h: 
nat).(\lambda (H3: (drop h d0 c0 c)).(lt_le_e n d0 (ty3 g c0 (lift h d0 
(TLRef n)) (lift h d0 (lift (S n) O u))) (\lambda (H4: (lt n d0)).(let H5 
\def (drop_getl_trans_le n d0 (le_S_n n d0 (le_S (S n) d0 H4)) c0 c h H3 
(CHead d (Bind Abst) u) H0) in (ex3_2_ind C C (\lambda (e0: C).(\lambda (_: 
C).(drop n O c0 e0))) (\lambda (e0: C).(\lambda (e1: C).(drop h (minus d0 n) 
e0 e1))) (\lambda (_: C).(\lambda (e1: C).(clear e1 (CHead d (Bind Abst) 
u)))) (ty3 g c0 (lift h d0 (TLRef n)) (lift h d0 (lift (S n) O u))) (\lambda 
(x0: C).(\lambda (x1: C).(\lambda (H6: (drop n O c0 x0)).(\lambda (H7: (drop 
h (minus d0 n) x0 x1)).(\lambda (H8: (clear x1 (CHead d (Bind Abst) u))).(let 
H9 \def (eq_ind nat (minus d0 n) (\lambda (n0: nat).(drop h n0 x0 x1)) H7 (S 
(minus d0 (S n))) (minus_x_Sy d0 n H4)) in (let H10 \def (drop_clear_S x1 x0 
h (minus d0 (S n)) H9 Abst d u H8) in (ex2_ind C (\lambda (c1: C).(clear x0 
(CHead c1 (Bind Abst) (lift h (minus d0 (S n)) u)))) (\lambda (c1: C).(drop h 
(minus d0 (S n)) c1 d)) (ty3 g c0 (lift h d0 (TLRef n)) (lift h d0 (lift (S 
n) O u))) (\lambda (x: C).(\lambda (H11: (clear x0 (CHead x (Bind Abst) (lift 
h (minus d0 (S n)) u)))).(\lambda (H12: (drop h (minus d0 (S n)) x 
d)).(eq_ind_r T (TLRef n) (\lambda (t0: T).(ty3 g c0 t0 (lift h d0 (lift (S 
n) O u)))) (eq_ind nat (plus (S n) (minus d0 (S n))) (\lambda (n0: nat).(ty3 
g c0 (TLRef n) (lift h n0 (lift (S n) O u)))) (eq_ind_r T (lift (S n) O (lift 
h (minus d0 (S n)) u)) (\lambda (t0: T).(ty3 g c0 (TLRef n) t0)) (eq_ind nat 
d0 (\lambda (_: nat).(ty3 g c0 (TLRef n) (lift (S n) O (lift h (minus d0 (S 
n)) u)))) (ty3_abst g n c0 x (lift h (minus d0 (S n)) u) (getl_intro n c0 
(CHead x (Bind Abst) (lift h (minus d0 (S n)) u)) x0 H6 H11) (lift h (minus 
d0 (S n)) t) (H2 x (minus d0 (S n)) h H12)) (plus (S n) (minus d0 (S n))) 
(le_plus_minus (S n) d0 H4)) (lift h (plus (S n) (minus d0 (S n))) (lift (S 
n) O u)) (lift_d u h (S n) (minus d0 (S n)) O (le_O_n (minus d0 (S n))))) d0 
(le_plus_minus_r (S n) d0 H4)) (lift h d0 (TLRef n)) (lift_lref_lt n h d0 
H4))))) H10)))))))) H5))) (\lambda (H4: (le d0 n)).(eq_ind_r T (TLRef (plus n 
h)) (\lambda (t0: T).(ty3 g c0 t0 (lift h d0 (lift (S n) O u)))) (eq_ind nat 
(S n) (\lambda (_: nat).(ty3 g c0 (TLRef (plus n h)) (lift h d0 (lift (S n) O 
u)))) (eq_ind_r T (lift (plus h (S n)) O u) (\lambda (t0: T).(ty3 g c0 (TLRef 
(plus n h)) t0)) (eq_ind_r nat (plus (S n) h) (\lambda (n0: nat).(ty3 g c0 
(TLRef (plus n h)) (lift n0 O u))) (ty3_abst g (plus n h) c0 d u 
(drop_getl_trans_ge n c0 c d0 h H3 (CHead d (Bind Abst) u) H0 H4) t H1) (plus 
h (S n)) (plus_sym h (S n))) (lift h d0 (lift (S n) O u)) (lift_free u (S n) 
h O d0 (le_S d0 n H4) (le_O_n d0))) (plus n (S O)) (eq_ind_r nat (plus (S O) 
n) (\lambda (n0: nat).(eq nat (S n) n0)) (refl_equal nat (plus (S O) n)) 
(plus n (S O)) (plus_sym n (S O)))) (lift h d0 (TLRef n)) (lift_lref_ge n h 
d0 H4)))))))))))))))) (\lambda (c: C).(\lambda (u: T).(\lambda (t: 
T).(\lambda (_: (ty3 g c u t)).(\lambda (H1: ((\forall (c0: C).(\forall (d: 
nat).(\forall (h: nat).((drop h d c0 c) \to (ty3 g c0 (lift h d u) (lift h d 
t)))))))).(\lambda (b: B).(\lambda (t0: T).(\lambda (t3: T).(\lambda (_: (ty3 
g (CHead c (Bind b) u) t0 t3)).(\lambda (H3: ((\forall (c0: C).(\forall (d: 
nat).(\forall (h: nat).((drop h d c0 (CHead c (Bind b) u)) \to (ty3 g c0 
(lift h d t0) (lift h d t3)))))))).(\lambda (c0: C).(\lambda (d: 
nat).(\lambda (h: nat).(\lambda (H4: (drop h d c0 c)).(eq_ind_r T (THead 
(Bind b) (lift h d u) (lift h (s (Bind b) d) t0)) (\lambda (t4: T).(ty3 g c0 
t4 (lift h d (THead (Bind b) u t3)))) (eq_ind_r T (THead (Bind b) (lift h d 
u) (lift h (s (Bind b) d) t3)) (\lambda (t4: T).(ty3 g c0 (THead (Bind b) 
(lift h d u) (lift h (s (Bind b) d) t0)) t4)) (ty3_bind g c0 (lift h d u) 
(lift h d t) (H1 c0 d h H4) b (lift h (S d) t0) (lift h (S d) t3) (H3 (CHead 
c0 (Bind b) (lift h d u)) (S d) h (drop_skip_bind h d c0 c H4 b u))) (lift h 
d (THead (Bind b) u t3)) (lift_head (Bind b) u t3 h d)) (lift h d (THead 
(Bind b) u t0)) (lift_head (Bind b) u t0 h d)))))))))))))))) (\lambda (c: 
C).(\lambda (w: T).(\lambda (u: T).(\lambda (_: (ty3 g c w u)).(\lambda (H1: 
((\forall (c0: C).(\forall (d: nat).(\forall (h: nat).((drop h d c0 c) \to 
(ty3 g c0 (lift h d w) (lift h d u)))))))).(\lambda (v: T).(\lambda (t: 
T).(\lambda (_: (ty3 g c v (THead (Bind Abst) u t))).(\lambda (H3: ((\forall 
(c0: C).(\forall (d: nat).(\forall (h: nat).((drop h d c0 c) \to (ty3 g c0 
(lift h d v) (lift h d (THead (Bind Abst) u t))))))))).(\lambda (c0: 
C).(\lambda (d: nat).(\lambda (h: nat).(\lambda (H4: (drop h d c0 
c)).(eq_ind_r T (THead (Flat Appl) (lift h d w) (lift h (s (Flat Appl) d) v)) 
(\lambda (t0: T).(ty3 g c0 t0 (lift h d (THead (Flat Appl) w (THead (Bind 
Abst) u t))))) (eq_ind_r T (THead (Flat Appl) (lift h d w) (lift h (s (Flat 
Appl) d) (THead (Bind Abst) u t))) (\lambda (t0: T).(ty3 g c0 (THead (Flat 
Appl) (lift h d w) (lift h (s (Flat Appl) d) v)) t0)) (eq_ind_r T (THead 
(Bind Abst) (lift h (s (Flat Appl) d) u) (lift h (s (Bind Abst) (s (Flat 
Appl) d)) t)) (\lambda (t0: T).(ty3 g c0 (THead (Flat Appl) (lift h d w) 
(lift h (s (Flat Appl) d) v)) (THead (Flat Appl) (lift h d w) t0))) (ty3_appl 
g c0 (lift h d w) (lift h d u) (H1 c0 d h H4) (lift h d v) (lift h (S d) t) 
(eq_ind T (lift h d (THead (Bind Abst) u t)) (\lambda (t0: T).(ty3 g c0 (lift 
h d v) t0)) (H3 c0 d h H4) (THead (Bind Abst) (lift h d u) (lift h (S d) t)) 
(lift_bind Abst u t h d))) (lift h (s (Flat Appl) d) (THead (Bind Abst) u t)) 
(lift_head (Bind Abst) u t h (s (Flat Appl) d))) (lift h d (THead (Flat Appl) 
w (THead (Bind Abst) u t))) (lift_head (Flat Appl) w (THead (Bind Abst) u t) 
h d)) (lift h d (THead (Flat Appl) w v)) (lift_head (Flat Appl) w v h 
d))))))))))))))) (\lambda (c: C).(\lambda (t0: T).(\lambda (t3: T).(\lambda 
(_: (ty3 g c t0 t3)).(\lambda (H1: ((\forall (c0: C).(\forall (d: 
nat).(\forall (h: nat).((drop h d c0 c) \to (ty3 g c0 (lift h d t0) (lift h d 
t3)))))))).(\lambda (t4: T).(\lambda (_: (ty3 g c t3 t4)).(\lambda (H3: 
((\forall (c0: C).(\forall (d: nat).(\forall (h: nat).((drop h d c0 c) \to 
(ty3 g c0 (lift h d t3) (lift h d t4)))))))).(\lambda (c0: C).(\lambda (d: 
nat).(\lambda (h: nat).(\lambda (H4: (drop h d c0 c)).(eq_ind_r T (THead 
(Flat Cast) (lift h d t3) (lift h (s (Flat Cast) d) t0)) (\lambda (t: T).(ty3 
g c0 t (lift h d (THead (Flat Cast) t4 t3)))) (eq_ind_r T (THead (Flat Cast) 
(lift h d t4) (lift h (s (Flat Cast) d) t3)) (\lambda (t: T).(ty3 g c0 (THead 
(Flat Cast) (lift h d t3) (lift h (s (Flat Cast) d) t0)) t)) (ty3_cast g c0 
(lift h (s (Flat Cast) d) t0) (lift h (s (Flat Cast) d) t3) (H1 c0 (s (Flat 
Cast) d) h H4) (lift h d t4) (H3 c0 d h H4)) (lift h d (THead (Flat Cast) t4 
t3)) (lift_head (Flat Cast) t4 t3 h d)) (lift h d (THead (Flat Cast) t3 t0)) 
(lift_head (Flat Cast) t3 t0 h d)))))))))))))) e t1 t2 H))))).
(* COMMENTS
Initial nodes: 4253
END *)

theorem ty3_correct:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t2: T).((ty3 g c 
t1 t2) \to (ex T (\lambda (t: T).(ty3 g c t2 t)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (ty3 g c t1 t2)).(ty3_ind g (\lambda (c0: C).(\lambda (_: T).(\lambda 
(t0: T).(ex T (\lambda (t3: T).(ty3 g c0 t0 t3)))))) (\lambda (c0: 
C).(\lambda (t0: T).(\lambda (t: T).(\lambda (H0: (ty3 g c0 t0 t)).(\lambda 
(_: (ex T (\lambda (t3: T).(ty3 g c0 t t3)))).(\lambda (u: T).(\lambda (t3: 
T).(\lambda (_: (ty3 g c0 u t3)).(\lambda (_: (ex T (\lambda (t4: T).(ty3 g 
c0 t3 t4)))).(\lambda (_: (pc3 c0 t3 t0)).(ex_intro T (\lambda (t4: T).(ty3 g 
c0 t0 t4)) t H0))))))))))) (\lambda (c0: C).(\lambda (m: nat).(ex_intro T 
(\lambda (t: T).(ty3 g c0 (TSort (next g m)) t)) (TSort (next g (next g m))) 
(ty3_sort g c0 (next g m))))) (\lambda (n: nat).(\lambda (c0: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (H0: (getl n c0 (CHead d (Bind Abbr) 
u))).(\lambda (t: T).(\lambda (_: (ty3 g d u t)).(\lambda (H2: (ex T (\lambda 
(t0: T).(ty3 g d t t0)))).(let H3 \def H2 in (ex_ind T (\lambda (t0: T).(ty3 
g d t t0)) (ex T (\lambda (t0: T).(ty3 g c0 (lift (S n) O t) t0))) (\lambda 
(x: T).(\lambda (H4: (ty3 g d t x)).(ex_intro T (\lambda (t0: T).(ty3 g c0 
(lift (S n) O t) t0)) (lift (S n) O x) (ty3_lift g d t x H4 c0 O (S n) 
(getl_drop Abbr c0 d u n H0))))) H3)))))))))) (\lambda (n: nat).(\lambda (c0: 
C).(\lambda (d: C).(\lambda (u: T).(\lambda (H0: (getl n c0 (CHead d (Bind 
Abst) u))).(\lambda (t: T).(\lambda (H1: (ty3 g d u t)).(\lambda (_: (ex T 
(\lambda (t0: T).(ty3 g d t t0)))).(ex_intro T (\lambda (t0: T).(ty3 g c0 
(lift (S n) O u) t0)) (lift (S n) O t) (ty3_lift g d u t H1 c0 O (S n) 
(getl_drop Abst c0 d u n H0))))))))))) (\lambda (c0: C).(\lambda (u: 
T).(\lambda (t: T).(\lambda (H0: (ty3 g c0 u t)).(\lambda (_: (ex T (\lambda 
(t0: T).(ty3 g c0 t t0)))).(\lambda (b: B).(\lambda (t0: T).(\lambda (t3: 
T).(\lambda (_: (ty3 g (CHead c0 (Bind b) u) t0 t3)).(\lambda (H3: (ex T 
(\lambda (t4: T).(ty3 g (CHead c0 (Bind b) u) t3 t4)))).(let H4 \def H3 in 
(ex_ind T (\lambda (t4: T).(ty3 g (CHead c0 (Bind b) u) t3 t4)) (ex T 
(\lambda (t4: T).(ty3 g c0 (THead (Bind b) u t3) t4))) (\lambda (x: 
T).(\lambda (H5: (ty3 g (CHead c0 (Bind b) u) t3 x)).(ex_intro T (\lambda 
(t4: T).(ty3 g c0 (THead (Bind b) u t3) t4)) (THead (Bind b) u x) (ty3_bind g 
c0 u t H0 b t3 x H5)))) H4)))))))))))) (\lambda (c0: C).(\lambda (w: 
T).(\lambda (u: T).(\lambda (H0: (ty3 g c0 w u)).(\lambda (H1: (ex T (\lambda 
(t: T).(ty3 g c0 u t)))).(\lambda (v: T).(\lambda (t: T).(\lambda (_: (ty3 g 
c0 v (THead (Bind Abst) u t))).(\lambda (H3: (ex T (\lambda (t0: T).(ty3 g c0 
(THead (Bind Abst) u t) t0)))).(let H4 \def H1 in (ex_ind T (\lambda (t0: 
T).(ty3 g c0 u t0)) (ex T (\lambda (t0: T).(ty3 g c0 (THead (Flat Appl) w 
(THead (Bind Abst) u t)) t0))) (\lambda (x: T).(\lambda (_: (ty3 g c0 u 
x)).(let H6 \def H3 in (ex_ind T (\lambda (t0: T).(ty3 g c0 (THead (Bind 
Abst) u t) t0)) (ex T (\lambda (t0: T).(ty3 g c0 (THead (Flat Appl) w (THead 
(Bind Abst) u t)) t0))) (\lambda (x0: T).(\lambda (H7: (ty3 g c0 (THead (Bind 
Abst) u t) x0)).(ex3_2_ind T T (\lambda (t3: T).(\lambda (_: T).(pc3 c0 
(THead (Bind Abst) u t3) x0))) (\lambda (_: T).(\lambda (t0: T).(ty3 g c0 u 
t0))) (\lambda (t3: T).(\lambda (_: T).(ty3 g (CHead c0 (Bind Abst) u) t 
t3))) (ex T (\lambda (t0: T).(ty3 g c0 (THead (Flat Appl) w (THead (Bind 
Abst) u t)) t0))) (\lambda (x1: T).(\lambda (x2: T).(\lambda (_: (pc3 c0 
(THead (Bind Abst) u x1) x0)).(\lambda (H9: (ty3 g c0 u x2)).(\lambda (H10: 
(ty3 g (CHead c0 (Bind Abst) u) t x1)).(ex_intro T (\lambda (t0: T).(ty3 g c0 
(THead (Flat Appl) w (THead (Bind Abst) u t)) t0)) (THead (Flat Appl) w 
(THead (Bind Abst) u x1)) (ty3_appl g c0 w u H0 (THead (Bind Abst) u t) x1 
(ty3_bind g c0 u x2 H9 Abst t x1 H10)))))))) (ty3_gen_bind g Abst c0 u t x0 
H7)))) H6)))) H4))))))))))) (\lambda (c0: C).(\lambda (t0: T).(\lambda (t3: 
T).(\lambda (_: (ty3 g c0 t0 t3)).(\lambda (_: (ex T (\lambda (t: T).(ty3 g 
c0 t3 t)))).(\lambda (t4: T).(\lambda (H2: (ty3 g c0 t3 t4)).(\lambda (H3: 
(ex T (\lambda (t: T).(ty3 g c0 t4 t)))).(let H4 \def H3 in (ex_ind T 
(\lambda (t: T).(ty3 g c0 t4 t)) (ex T (\lambda (t: T).(ty3 g c0 (THead (Flat 
Cast) t4 t3) t))) (\lambda (x: T).(\lambda (H5: (ty3 g c0 t4 x)).(ex_intro T 
(\lambda (t: T).(ty3 g c0 (THead (Flat Cast) t4 t3) t)) (THead (Flat Cast) x 
t4) (ty3_cast g c0 t3 t4 H2 x H5)))) H4)))))))))) c t1 t2 H))))).
(* COMMENTS
Initial nodes: 1333
END *)

theorem ty3_unique:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t1: T).((ty3 g c u 
t1) \to (\forall (t2: T).((ty3 g c u t2) \to (pc3 c t1 t2)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda (H: 
(ty3 g c u t1)).(ty3_ind g (\lambda (c0: C).(\lambda (t: T).(\lambda (t0: 
T).(\forall (t2: T).((ty3 g c0 t t2) \to (pc3 c0 t0 t2)))))) (\lambda (c0: 
C).(\lambda (t2: T).(\lambda (t: T).(\lambda (_: (ty3 g c0 t2 t)).(\lambda 
(_: ((\forall (t3: T).((ty3 g c0 t2 t3) \to (pc3 c0 t t3))))).(\lambda (u0: 
T).(\lambda (t0: T).(\lambda (_: (ty3 g c0 u0 t0)).(\lambda (H3: ((\forall 
(t3: T).((ty3 g c0 u0 t3) \to (pc3 c0 t0 t3))))).(\lambda (H4: (pc3 c0 t0 
t2)).(\lambda (t3: T).(\lambda (H5: (ty3 g c0 u0 t3)).(pc3_t t0 c0 t2 (pc3_s 
c0 t2 t0 H4) t3 (H3 t3 H5)))))))))))))) (\lambda (c0: C).(\lambda (m: 
nat).(\lambda (t2: T).(\lambda (H0: (ty3 g c0 (TSort m) t2)).(ty3_gen_sort g 
c0 t2 m H0))))) (\lambda (n: nat).(\lambda (c0: C).(\lambda (d: C).(\lambda 
(u0: T).(\lambda (H0: (getl n c0 (CHead d (Bind Abbr) u0))).(\lambda (t: 
T).(\lambda (_: (ty3 g d u0 t)).(\lambda (H2: ((\forall (t2: T).((ty3 g d u0 
t2) \to (pc3 d t t2))))).(\lambda (t2: T).(\lambda (H3: (ty3 g c0 (TLRef n) 
t2)).(or_ind (ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t0: 
T).(pc3 c0 (lift (S n) O t0) t2)))) (\lambda (e: C).(\lambda (u1: T).(\lambda 
(_: T).(getl n c0 (CHead e (Bind Abbr) u1))))) (\lambda (e: C).(\lambda (u1: 
T).(\lambda (t0: T).(ty3 g e u1 t0))))) (ex3_3 C T T (\lambda (_: C).(\lambda 
(u1: T).(\lambda (_: T).(pc3 c0 (lift (S n) O u1) t2)))) (\lambda (e: 
C).(\lambda (u1: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) u1))))) 
(\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(ty3 g e u1 t0))))) (pc3 c0 
(lift (S n) O t) t2) (\lambda (H4: (ex3_3 C T T (\lambda (_: C).(\lambda (_: 
T).(\lambda (t0: T).(pc3 c0 (lift (S n) O t0) t2)))) (\lambda (e: C).(\lambda 
(u1: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abbr) u1))))) (\lambda (e: 
C).(\lambda (u1: T).(\lambda (t0: T).(ty3 g e u1 t0)))))).(ex3_3_ind C T T 
(\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift (S n) O t0) 
t2)))) (\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(getl n c0 (CHead e 
(Bind Abbr) u1))))) (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(ty3 g 
e u1 t0)))) (pc3 c0 (lift (S n) O t) t2) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (x2: T).(\lambda (H5: (pc3 c0 (lift (S n) O x2) t2)).(\lambda 
(H6: (getl n c0 (CHead x0 (Bind Abbr) x1))).(\lambda (H7: (ty3 g x0 x1 
x2)).(let H8 \def (eq_ind C (CHead d (Bind Abbr) u0) (\lambda (c1: C).(getl n 
c0 c1)) H0 (CHead x0 (Bind Abbr) x1) (getl_mono c0 (CHead d (Bind Abbr) u0) n 
H0 (CHead x0 (Bind Abbr) x1) H6)) in (let H9 \def (f_equal C C (\lambda (e: 
C).(match e in C return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | 
(CHead c1 _ _) \Rightarrow c1])) (CHead d (Bind Abbr) u0) (CHead x0 (Bind 
Abbr) x1) (getl_mono c0 (CHead d (Bind Abbr) u0) n H0 (CHead x0 (Bind Abbr) 
x1) H6)) in ((let H10 \def (f_equal C T (\lambda (e: C).(match e in C return 
(\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | (CHead _ _ t0) 
\Rightarrow t0])) (CHead d (Bind Abbr) u0) (CHead x0 (Bind Abbr) x1) 
(getl_mono c0 (CHead d (Bind Abbr) u0) n H0 (CHead x0 (Bind Abbr) x1) H6)) in 
(\lambda (H11: (eq C d x0)).(let H12 \def (eq_ind_r T x1 (\lambda (t0: 
T).(getl n c0 (CHead x0 (Bind Abbr) t0))) H8 u0 H10) in (let H13 \def 
(eq_ind_r T x1 (\lambda (t0: T).(ty3 g x0 t0 x2)) H7 u0 H10) in (let H14 \def 
(eq_ind_r C x0 (\lambda (c1: C).(getl n c0 (CHead c1 (Bind Abbr) u0))) H12 d 
H11) in (let H15 \def (eq_ind_r C x0 (\lambda (c1: C).(ty3 g c1 u0 x2)) H13 d 
H11) in (pc3_t (lift (S n) O x2) c0 (lift (S n) O t) (pc3_lift c0 d (S n) O 
(getl_drop Abbr c0 d u0 n H14) t x2 (H2 x2 H15)) t2 H5))))))) H9))))))))) 
H4)) (\lambda (H4: (ex3_3 C T T (\lambda (_: C).(\lambda (u1: T).(\lambda (_: 
T).(pc3 c0 (lift (S n) O u1) t2)))) (\lambda (e: C).(\lambda (u1: T).(\lambda 
(_: T).(getl n c0 (CHead e (Bind Abst) u1))))) (\lambda (e: C).(\lambda (u1: 
T).(\lambda (t0: T).(ty3 g e u1 t0)))))).(ex3_3_ind C T T (\lambda (_: 
C).(\lambda (u1: T).(\lambda (_: T).(pc3 c0 (lift (S n) O u1) t2)))) (\lambda 
(e: C).(\lambda (u1: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abst) 
u1))))) (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(ty3 g e u1 t0)))) 
(pc3 c0 (lift (S n) O t) t2) (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: 
T).(\lambda (_: (pc3 c0 (lift (S n) O x1) t2)).(\lambda (H6: (getl n c0 
(CHead x0 (Bind Abst) x1))).(\lambda (_: (ty3 g x0 x1 x2)).(let H8 \def 
(eq_ind C (CHead d (Bind Abbr) u0) (\lambda (c1: C).(getl n c0 c1)) H0 (CHead 
x0 (Bind Abst) x1) (getl_mono c0 (CHead d (Bind Abbr) u0) n H0 (CHead x0 
(Bind Abst) x1) H6)) in (let H9 \def (eq_ind C (CHead d (Bind Abbr) u0) 
(\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b) \Rightarrow (match b in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow True | Abst \Rightarrow False | Void 
\Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead x0 (Bind Abst) 
x1) (getl_mono c0 (CHead d (Bind Abbr) u0) n H0 (CHead x0 (Bind Abst) x1) 
H6)) in (False_ind (pc3 c0 (lift (S n) O t) t2) H9))))))))) H4)) 
(ty3_gen_lref g c0 t2 n H3)))))))))))) (\lambda (n: nat).(\lambda (c0: 
C).(\lambda (d: C).(\lambda (u0: T).(\lambda (H0: (getl n c0 (CHead d (Bind 
Abst) u0))).(\lambda (t: T).(\lambda (_: (ty3 g d u0 t)).(\lambda (_: 
((\forall (t2: T).((ty3 g d u0 t2) \to (pc3 d t t2))))).(\lambda (t2: 
T).(\lambda (H3: (ty3 g c0 (TLRef n) t2)).(or_ind (ex3_3 C T T (\lambda (_: 
C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift (S n) O t0) t2)))) (\lambda 
(e: C).(\lambda (u1: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abbr) 
u1))))) (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(ty3 g e u1 t0))))) 
(ex3_3 C T T (\lambda (_: C).(\lambda (u1: T).(\lambda (_: T).(pc3 c0 (lift 
(S n) O u1) t2)))) (\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(getl n 
c0 (CHead e (Bind Abst) u1))))) (\lambda (e: C).(\lambda (u1: T).(\lambda 
(t0: T).(ty3 g e u1 t0))))) (pc3 c0 (lift (S n) O u0) t2) (\lambda (H4: 
(ex3_3 C T T (\lambda (_: C).(\lambda (_: T).(\lambda (t0: T).(pc3 c0 (lift 
(S n) O t0) t2)))) (\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(getl n 
c0 (CHead e (Bind Abbr) u1))))) (\lambda (e: C).(\lambda (u1: T).(\lambda 
(t0: T).(ty3 g e u1 t0)))))).(ex3_3_ind C T T (\lambda (_: C).(\lambda (_: 
T).(\lambda (t0: T).(pc3 c0 (lift (S n) O t0) t2)))) (\lambda (e: C).(\lambda 
(u1: T).(\lambda (_: T).(getl n c0 (CHead e (Bind Abbr) u1))))) (\lambda (e: 
C).(\lambda (u1: T).(\lambda (t0: T).(ty3 g e u1 t0)))) (pc3 c0 (lift (S n) O 
u0) t2) (\lambda (x0: C).(\lambda (x1: T).(\lambda (x2: T).(\lambda (_: (pc3 
c0 (lift (S n) O x2) t2)).(\lambda (H6: (getl n c0 (CHead x0 (Bind Abbr) 
x1))).(\lambda (_: (ty3 g x0 x1 x2)).(let H8 \def (eq_ind C (CHead d (Bind 
Abst) u0) (\lambda (c1: C).(getl n c0 c1)) H0 (CHead x0 (Bind Abbr) x1) 
(getl_mono c0 (CHead d (Bind Abst) u0) n H0 (CHead x0 (Bind Abbr) x1) H6)) in 
(let H9 \def (eq_ind C (CHead d (Bind Abst) u0) (\lambda (ee: C).(match ee in 
C return (\lambda (_: C).Prop) with [(CSort _) \Rightarrow False | (CHead _ k 
_) \Rightarrow (match k in K return (\lambda (_: K).Prop) with [(Bind b) 
\Rightarrow (match b in B return (\lambda (_: B).Prop) with [Abbr \Rightarrow 
False | Abst \Rightarrow True | Void \Rightarrow False]) | (Flat _) 
\Rightarrow False])])) I (CHead x0 (Bind Abbr) x1) (getl_mono c0 (CHead d 
(Bind Abst) u0) n H0 (CHead x0 (Bind Abbr) x1) H6)) in (False_ind (pc3 c0 
(lift (S n) O u0) t2) H9))))))))) H4)) (\lambda (H4: (ex3_3 C T T (\lambda 
(_: C).(\lambda (u1: T).(\lambda (_: T).(pc3 c0 (lift (S n) O u1) t2)))) 
(\lambda (e: C).(\lambda (u1: T).(\lambda (_: T).(getl n c0 (CHead e (Bind 
Abst) u1))))) (\lambda (e: C).(\lambda (u1: T).(\lambda (t0: T).(ty3 g e u1 
t0)))))).(ex3_3_ind C T T (\lambda (_: C).(\lambda (u1: T).(\lambda (_: 
T).(pc3 c0 (lift (S n) O u1) t2)))) (\lambda (e: C).(\lambda (u1: T).(\lambda 
(_: T).(getl n c0 (CHead e (Bind Abst) u1))))) (\lambda (e: C).(\lambda (u1: 
T).(\lambda (t0: T).(ty3 g e u1 t0)))) (pc3 c0 (lift (S n) O u0) t2) (\lambda 
(x0: C).(\lambda (x1: T).(\lambda (x2: T).(\lambda (H5: (pc3 c0 (lift (S n) O 
x1) t2)).(\lambda (H6: (getl n c0 (CHead x0 (Bind Abst) x1))).(\lambda (H7: 
(ty3 g x0 x1 x2)).(let H8 \def (eq_ind C (CHead d (Bind Abst) u0) (\lambda 
(c1: C).(getl n c0 c1)) H0 (CHead x0 (Bind Abst) x1) (getl_mono c0 (CHead d 
(Bind Abst) u0) n H0 (CHead x0 (Bind Abst) x1) H6)) in (let H9 \def (f_equal 
C C (\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow d | (CHead c1 _ _) \Rightarrow c1])) (CHead d (Bind Abst) u0) 
(CHead x0 (Bind Abst) x1) (getl_mono c0 (CHead d (Bind Abst) u0) n H0 (CHead 
x0 (Bind Abst) x1) H6)) in ((let H10 \def (f_equal C T (\lambda (e: C).(match 
e in C return (\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | (CHead _ _ 
t0) \Rightarrow t0])) (CHead d (Bind Abst) u0) (CHead x0 (Bind Abst) x1) 
(getl_mono c0 (CHead d (Bind Abst) u0) n H0 (CHead x0 (Bind Abst) x1) H6)) in 
(\lambda (H11: (eq C d x0)).(let H12 \def (eq_ind_r T x1 (\lambda (t0: 
T).(getl n c0 (CHead x0 (Bind Abst) t0))) H8 u0 H10) in (let H13 \def 
(eq_ind_r T x1 (\lambda (t0: T).(ty3 g x0 t0 x2)) H7 u0 H10) in (let H14 \def 
(eq_ind_r T x1 (\lambda (t0: T).(pc3 c0 (lift (S n) O t0) t2)) H5 u0 H10) in 
(let H15 \def (eq_ind_r C x0 (\lambda (c1: C).(getl n c0 (CHead c1 (Bind 
Abst) u0))) H12 d H11) in (let H16 \def (eq_ind_r C x0 (\lambda (c1: C).(ty3 
g c1 u0 x2)) H13 d H11) in H14))))))) H9))))))))) H4)) (ty3_gen_lref g c0 t2 
n H3)))))))))))) (\lambda (c0: C).(\lambda (u0: T).(\lambda (t: T).(\lambda 
(_: (ty3 g c0 u0 t)).(\lambda (_: ((\forall (t2: T).((ty3 g c0 u0 t2) \to 
(pc3 c0 t t2))))).(\lambda (b: B).(\lambda (t0: T).(\lambda (t2: T).(\lambda 
(_: (ty3 g (CHead c0 (Bind b) u0) t0 t2)).(\lambda (H3: ((\forall (t3: 
T).((ty3 g (CHead c0 (Bind b) u0) t0 t3) \to (pc3 (CHead c0 (Bind b) u0) t2 
t3))))).(\lambda (t3: T).(\lambda (H4: (ty3 g c0 (THead (Bind b) u0 t0) 
t3)).(ex3_2_ind T T (\lambda (t4: T).(\lambda (_: T).(pc3 c0 (THead (Bind b) 
u0 t4) t3))) (\lambda (_: T).(\lambda (t5: T).(ty3 g c0 u0 t5))) (\lambda 
(t4: T).(\lambda (_: T).(ty3 g (CHead c0 (Bind b) u0) t0 t4))) (pc3 c0 (THead 
(Bind b) u0 t2) t3) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H5: (pc3 c0 
(THead (Bind b) u0 x0) t3)).(\lambda (_: (ty3 g c0 u0 x1)).(\lambda (H7: (ty3 
g (CHead c0 (Bind b) u0) t0 x0)).(pc3_t (THead (Bind b) u0 x0) c0 (THead 
(Bind b) u0 t2) (pc3_head_2 c0 u0 t2 x0 (Bind b) (H3 x0 H7)) t3 H5)))))) 
(ty3_gen_bind g b c0 u0 t0 t3 H4)))))))))))))) (\lambda (c0: C).(\lambda (w: 
T).(\lambda (u0: T).(\lambda (_: (ty3 g c0 w u0)).(\lambda (_: ((\forall (t2: 
T).((ty3 g c0 w t2) \to (pc3 c0 u0 t2))))).(\lambda (v: T).(\lambda (t: 
T).(\lambda (_: (ty3 g c0 v (THead (Bind Abst) u0 t))).(\lambda (H3: 
((\forall (t2: T).((ty3 g c0 v t2) \to (pc3 c0 (THead (Bind Abst) u0 t) 
t2))))).(\lambda (t2: T).(\lambda (H4: (ty3 g c0 (THead (Flat Appl) w v) 
t2)).(ex3_2_ind T T (\lambda (u1: T).(\lambda (t0: T).(pc3 c0 (THead (Flat 
Appl) w (THead (Bind Abst) u1 t0)) t2))) (\lambda (u1: T).(\lambda (t0: 
T).(ty3 g c0 v (THead (Bind Abst) u1 t0)))) (\lambda (u1: T).(\lambda (_: 
T).(ty3 g c0 w u1))) (pc3 c0 (THead (Flat Appl) w (THead (Bind Abst) u0 t)) 
t2) (\lambda (x0: T).(\lambda (x1: T).(\lambda (H5: (pc3 c0 (THead (Flat 
Appl) w (THead (Bind Abst) x0 x1)) t2)).(\lambda (H6: (ty3 g c0 v (THead 
(Bind Abst) x0 x1))).(\lambda (_: (ty3 g c0 w x0)).(pc3_t (THead (Flat Appl) 
w (THead (Bind Abst) x0 x1)) c0 (THead (Flat Appl) w (THead (Bind Abst) u0 
t)) (pc3_thin_dx c0 (THead (Bind Abst) u0 t) (THead (Bind Abst) x0 x1) (H3 
(THead (Bind Abst) x0 x1) H6) w Appl) t2 H5)))))) (ty3_gen_appl g c0 w v t2 
H4))))))))))))) (\lambda (c0: C).(\lambda (t0: T).(\lambda (t2: T).(\lambda 
(_: (ty3 g c0 t0 t2)).(\lambda (_: ((\forall (t3: T).((ty3 g c0 t0 t3) \to 
(pc3 c0 t2 t3))))).(\lambda (t3: T).(\lambda (_: (ty3 g c0 t2 t3)).(\lambda 
(H3: ((\forall (t4: T).((ty3 g c0 t2 t4) \to (pc3 c0 t3 t4))))).(\lambda (t4: 
T).(\lambda (H4: (ty3 g c0 (THead (Flat Cast) t2 t0) t4)).(ex3_ind T (\lambda 
(t5: T).(pc3 c0 (THead (Flat Cast) t5 t2) t4)) (\lambda (_: T).(ty3 g c0 t0 
t2)) (\lambda (t5: T).(ty3 g c0 t2 t5)) (pc3 c0 (THead (Flat Cast) t3 t2) t4) 
(\lambda (x0: T).(\lambda (H5: (pc3 c0 (THead (Flat Cast) x0 t2) 
t4)).(\lambda (_: (ty3 g c0 t0 t2)).(\lambda (H7: (ty3 g c0 t2 x0)).(pc3_t 
(THead (Flat Cast) x0 t2) c0 (THead (Flat Cast) t3 t2) (pc3_head_1 c0 t3 x0 
(H3 x0 H7) (Flat Cast) t2) t4 H5))))) (ty3_gen_cast g c0 t0 t2 t4 
H4)))))))))))) c u t1 H))))).
(* COMMENTS
Initial nodes: 3459
END *)

theorem ty3_gen_abst_abst:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t1: T).(\forall 
(t2: T).((ty3 g c (THead (Bind Abst) u t1) (THead (Bind Abst) u t2)) \to (ex2 
T (\lambda (w: T).(ty3 g c u w)) (\lambda (_: T).(ty3 g (CHead c (Bind Abst) 
u) t1 t2))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (t1: T).(\lambda 
(t2: T).(\lambda (H: (ty3 g c (THead (Bind Abst) u t1) (THead (Bind Abst) u 
t2))).(ex_ind T (\lambda (t: T).(ty3 g c (THead (Bind Abst) u t2) t)) (ex2 T 
(\lambda (w: T).(ty3 g c u w)) (\lambda (_: T).(ty3 g (CHead c (Bind Abst) u) 
t1 t2))) (\lambda (x: T).(\lambda (H0: (ty3 g c (THead (Bind Abst) u t2) 
x)).(ex3_2_ind T T (\lambda (t3: T).(\lambda (_: T).(pc3 c (THead (Bind Abst) 
u t3) x))) (\lambda (_: T).(\lambda (t: T).(ty3 g c u t))) (\lambda (t3: 
T).(\lambda (_: T).(ty3 g (CHead c (Bind Abst) u) t2 t3))) (ex2 T (\lambda 
(w: T).(ty3 g c u w)) (\lambda (_: T).(ty3 g (CHead c (Bind Abst) u) t1 t2))) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (_: (pc3 c (THead (Bind Abst) u 
x0) x)).(\lambda (_: (ty3 g c u x1)).(\lambda (H3: (ty3 g (CHead c (Bind 
Abst) u) t2 x0)).(ex3_2_ind T T (\lambda (t3: T).(\lambda (_: T).(pc3 c 
(THead (Bind Abst) u t3) (THead (Bind Abst) u t2)))) (\lambda (_: T).(\lambda 
(t: T).(ty3 g c u t))) (\lambda (t3: T).(\lambda (_: T).(ty3 g (CHead c (Bind 
Abst) u) t1 t3))) (ex2 T (\lambda (w: T).(ty3 g c u w)) (\lambda (_: T).(ty3 
g (CHead c (Bind Abst) u) t1 t2))) (\lambda (x2: T).(\lambda (x3: T).(\lambda 
(H4: (pc3 c (THead (Bind Abst) u x2) (THead (Bind Abst) u t2))).(\lambda (H5: 
(ty3 g c u x3)).(\lambda (H6: (ty3 g (CHead c (Bind Abst) u) t1 x2)).(let H_y 
\def (pc3_gen_abst_shift c u x2 t2 H4) in (ex_intro2 T (\lambda (w: T).(ty3 g 
c u w)) (\lambda (_: T).(ty3 g (CHead c (Bind Abst) u) t1 t2)) x3 H5 
(ty3_conv g (CHead c (Bind Abst) u) t2 x0 H3 t1 x2 H6 H_y)))))))) 
(ty3_gen_bind g Abst c u t1 (THead (Bind Abst) u t2) H))))))) (ty3_gen_bind g 
Abst c u t2 x H0)))) (ty3_correct g c (THead (Bind Abst) u t1) (THead (Bind 
Abst) u t2) H))))))).
(* COMMENTS
Initial nodes: 571
END *)

theorem ty3_typecheck:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (v: T).((ty3 g c t 
v) \to (ex T (\lambda (u: T).(ty3 g c (THead (Flat Cast) v t) u)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (v: T).(\lambda (H: 
(ty3 g c t v)).(ex_ind T (\lambda (t0: T).(ty3 g c v t0)) (ex T (\lambda (u: 
T).(ty3 g c (THead (Flat Cast) v t) u))) (\lambda (x: T).(\lambda (H0: (ty3 g 
c v x)).(ex_intro T (\lambda (u: T).(ty3 g c (THead (Flat Cast) v t) u)) 
(THead (Flat Cast) x v) (ty3_cast g c t v H x H0)))) (ty3_correct g c t v 
H)))))).
(* COMMENTS
Initial nodes: 131
END *)

theorem ty3_getl_subst0:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (u: T).((ty3 g c t 
u) \to (\forall (v0: T).(\forall (t0: T).(\forall (i: nat).((subst0 i v0 t 
t0) \to (\forall (b: B).(\forall (d: C).(\forall (v: T).((getl i c (CHead d 
(Bind b) v)) \to (ex T (\lambda (w: T).(ty3 g d v w)))))))))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (u: T).(\lambda (H: 
(ty3 g c t u)).(ty3_ind g (\lambda (c0: C).(\lambda (t0: T).(\lambda (_: 
T).(\forall (v0: T).(\forall (t2: T).(\forall (i: nat).((subst0 i v0 t0 t2) 
\to (\forall (b: B).(\forall (d: C).(\forall (v: T).((getl i c0 (CHead d 
(Bind b) v)) \to (ex T (\lambda (w: T).(ty3 g d v w)))))))))))))) (\lambda 
(c0: C).(\lambda (t2: T).(\lambda (t0: T).(\lambda (_: (ty3 g c0 t2 
t0)).(\lambda (_: ((\forall (v0: T).(\forall (t1: T).(\forall (i: 
nat).((subst0 i v0 t2 t1) \to (\forall (b: B).(\forall (d: C).(\forall (v: 
T).((getl i c0 (CHead d (Bind b) v)) \to (ex T (\lambda (w: T).(ty3 g d v 
w))))))))))))).(\lambda (u0: T).(\lambda (t1: T).(\lambda (_: (ty3 g c0 u0 
t1)).(\lambda (H3: ((\forall (v0: T).(\forall (t3: T).(\forall (i: 
nat).((subst0 i v0 u0 t3) \to (\forall (b: B).(\forall (d: C).(\forall (v: 
T).((getl i c0 (CHead d (Bind b) v)) \to (ex T (\lambda (w: T).(ty3 g d v 
w))))))))))))).(\lambda (_: (pc3 c0 t1 t2)).(\lambda (v0: T).(\lambda (t3: 
T).(\lambda (i: nat).(\lambda (H5: (subst0 i v0 u0 t3)).(\lambda (b: 
B).(\lambda (d: C).(\lambda (v: T).(\lambda (H6: (getl i c0 (CHead d (Bind b) 
v))).(H3 v0 t3 i H5 b d v H6))))))))))))))))))) (\lambda (c0: C).(\lambda (m: 
nat).(\lambda (v0: T).(\lambda (t0: T).(\lambda (i: nat).(\lambda (H0: 
(subst0 i v0 (TSort m) t0)).(\lambda (b: B).(\lambda (d: C).(\lambda (v: 
T).(\lambda (_: (getl i c0 (CHead d (Bind b) v))).(subst0_gen_sort v0 t0 i m 
H0 (ex T (\lambda (w: T).(ty3 g d v w)))))))))))))) (\lambda (n: 
nat).(\lambda (c0: C).(\lambda (d: C).(\lambda (u0: T).(\lambda (H0: (getl n 
c0 (CHead d (Bind Abbr) u0))).(\lambda (t0: T).(\lambda (H1: (ty3 g d u0 
t0)).(\lambda (_: ((\forall (v0: T).(\forall (t1: T).(\forall (i: 
nat).((subst0 i v0 u0 t1) \to (\forall (b: B).(\forall (d0: C).(\forall (v: 
T).((getl i d (CHead d0 (Bind b) v)) \to (ex T (\lambda (w: T).(ty3 g d0 v 
w))))))))))))).(\lambda (v0: T).(\lambda (t1: T).(\lambda (i: nat).(\lambda 
(H3: (subst0 i v0 (TLRef n) t1)).(\lambda (b: B).(\lambda (d0: C).(\lambda 
(v: T).(\lambda (H4: (getl i c0 (CHead d0 (Bind b) v))).(land_ind (eq nat n 
i) (eq T t1 (lift (S n) O v0)) (ex T (\lambda (w: T).(ty3 g d0 v w))) 
(\lambda (H5: (eq nat n i)).(\lambda (_: (eq T t1 (lift (S n) O v0))).(let H7 
\def (eq_ind_r nat i (\lambda (n0: nat).(getl n0 c0 (CHead d0 (Bind b) v))) 
H4 n H5) in (let H8 \def (eq_ind C (CHead d (Bind Abbr) u0) (\lambda (c1: 
C).(getl n c0 c1)) H0 (CHead d0 (Bind b) v) (getl_mono c0 (CHead d (Bind 
Abbr) u0) n H0 (CHead d0 (Bind b) v) H7)) in (let H9 \def (f_equal C C 
(\lambda (e: C).(match e in C return (\lambda (_: C).C) with [(CSort _) 
\Rightarrow d | (CHead c1 _ _) \Rightarrow c1])) (CHead d (Bind Abbr) u0) 
(CHead d0 (Bind b) v) (getl_mono c0 (CHead d (Bind Abbr) u0) n H0 (CHead d0 
(Bind b) v) H7)) in ((let H10 \def (f_equal C B (\lambda (e: C).(match e in C 
return (\lambda (_: C).B) with [(CSort _) \Rightarrow Abbr | (CHead _ k _) 
\Rightarrow (match k in K return (\lambda (_: K).B) with [(Bind b0) 
\Rightarrow b0 | (Flat _) \Rightarrow Abbr])])) (CHead d (Bind Abbr) u0) 
(CHead d0 (Bind b) v) (getl_mono c0 (CHead d (Bind Abbr) u0) n H0 (CHead d0 
(Bind b) v) H7)) in ((let H11 \def (f_equal C T (\lambda (e: C).(match e in C 
return (\lambda (_: C).T) with [(CSort _) \Rightarrow u0 | (CHead _ _ t2) 
\Rightarrow t2])) (CHead d (Bind Abbr) u0) (CHead d0 (Bind b) v) (getl_mono 
c0 (CHead d (Bind Abbr) u0) n H0 (CHead d0 (Bind b) v) H7)) in (\lambda (H12: 
(eq B Abbr b)).(\lambda (H13: (eq C d d0)).(let H14 \def (eq_ind_r T v 
(\lambda (t2: T).(getl n c0 (CHead d0 (Bind b) t2))) H8 u0 H11) in (eq_ind T 
u0 (\lambda (t2: T).(ex T (\lambda (w: T).(ty3 g d0 t2 w)))) (let H15 \def 
(eq_ind_r C d0 (\lambda (c1: C).(getl n c0 (CHead c1 (Bind b) u0))) H14 d 
H13) in (eq_ind C d (\lambda (c1: C).(ex T (\lambda (w: T).(ty3 g c1 u0 w)))) 
(let H16 \def (eq_ind_r B b (\lambda (b0: B).(getl n c0 (CHead d (Bind b0) 
u0))) H15 Abbr H12) in (ex_intro T (\lambda (w: T).(ty3 g d u0 w)) t0 H1)) d0 
H13)) v H11))))) H10)) H9)))))) (subst0_gen_lref v0 t1 i n 
H3)))))))))))))))))) (\lambda (n: nat).(\lambda (c0: C).(\lambda (d: 
C).(\lambda (u0: T).(\lambda (H0: (getl n c0 (CHead d (Bind Abst) 
u0))).(\lambda (t0: T).(\lambda (H1: (ty3 g d u0 t0)).(\lambda (_: ((\forall 
(v0: T).(\forall (t1: T).(\forall (i: nat).((subst0 i v0 u0 t1) \to (\forall 
(b: B).(\forall (d0: C).(\forall (v: T).((getl i d (CHead d0 (Bind b) v)) \to 
(ex T (\lambda (w: T).(ty3 g d0 v w))))))))))))).(\lambda (v0: T).(\lambda 
(t1: T).(\lambda (i: nat).(\lambda (H3: (subst0 i v0 (TLRef n) t1)).(\lambda 
(b: B).(\lambda (d0: C).(\lambda (v: T).(\lambda (H4: (getl i c0 (CHead d0 
(Bind b) v))).(land_ind (eq nat n i) (eq T t1 (lift (S n) O v0)) (ex T 
(\lambda (w: T).(ty3 g d0 v w))) (\lambda (H5: (eq nat n i)).(\lambda (_: (eq 
T t1 (lift (S n) O v0))).(let H7 \def (eq_ind_r nat i (\lambda (n0: 
nat).(getl n0 c0 (CHead d0 (Bind b) v))) H4 n H5) in (let H8 \def (eq_ind C 
(CHead d (Bind Abst) u0) (\lambda (c1: C).(getl n c0 c1)) H0 (CHead d0 (Bind 
b) v) (getl_mono c0 (CHead d (Bind Abst) u0) n H0 (CHead d0 (Bind b) v) H7)) 
in (let H9 \def (f_equal C C (\lambda (e: C).(match e in C return (\lambda 
(_: C).C) with [(CSort _) \Rightarrow d | (CHead c1 _ _) \Rightarrow c1])) 
(CHead d (Bind Abst) u0) (CHead d0 (Bind b) v) (getl_mono c0 (CHead d (Bind 
Abst) u0) n H0 (CHead d0 (Bind b) v) H7)) in ((let H10 \def (f_equal C B 
(\lambda (e: C).(match e in C return (\lambda (_: C).B) with [(CSort _) 
\Rightarrow Abst | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).B) with [(Bind b0) \Rightarrow b0 | (Flat _) \Rightarrow Abst])])) 
(CHead d (Bind Abst) u0) (CHead d0 (Bind b) v) (getl_mono c0 (CHead d (Bind 
Abst) u0) n H0 (CHead d0 (Bind b) v) H7)) in ((let H11 \def (f_equal C T 
(\lambda (e: C).(match e in C return (\lambda (_: C).T) with [(CSort _) 
\Rightarrow u0 | (CHead _ _ t2) \Rightarrow t2])) (CHead d (Bind Abst) u0) 
(CHead d0 (Bind b) v) (getl_mono c0 (CHead d (Bind Abst) u0) n H0 (CHead d0 
(Bind b) v) H7)) in (\lambda (H12: (eq B Abst b)).(\lambda (H13: (eq C d 
d0)).(let H14 \def (eq_ind_r T v (\lambda (t2: T).(getl n c0 (CHead d0 (Bind 
b) t2))) H8 u0 H11) in (eq_ind T u0 (\lambda (t2: T).(ex T (\lambda (w: 
T).(ty3 g d0 t2 w)))) (let H15 \def (eq_ind_r C d0 (\lambda (c1: C).(getl n 
c0 (CHead c1 (Bind b) u0))) H14 d H13) in (eq_ind C d (\lambda (c1: C).(ex T 
(\lambda (w: T).(ty3 g c1 u0 w)))) (let H16 \def (eq_ind_r B b (\lambda (b0: 
B).(getl n c0 (CHead d (Bind b0) u0))) H15 Abst H12) in (ex_intro T (\lambda 
(w: T).(ty3 g d u0 w)) t0 H1)) d0 H13)) v H11))))) H10)) H9)))))) 
(subst0_gen_lref v0 t1 i n H3)))))))))))))))))) (\lambda (c0: C).(\lambda 
(u0: T).(\lambda (t0: T).(\lambda (_: (ty3 g c0 u0 t0)).(\lambda (H1: 
((\forall (v0: T).(\forall (t1: T).(\forall (i: nat).((subst0 i v0 u0 t1) \to 
(\forall (b: B).(\forall (d: C).(\forall (v: T).((getl i c0 (CHead d (Bind b) 
v)) \to (ex T (\lambda (w: T).(ty3 g d v w))))))))))))).(\lambda (b: 
B).(\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (ty3 g (CHead c0 (Bind b) 
u0) t1 t2)).(\lambda (H3: ((\forall (v0: T).(\forall (t3: T).(\forall (i: 
nat).((subst0 i v0 t1 t3) \to (\forall (b0: B).(\forall (d: C).(\forall (v: 
T).((getl i (CHead c0 (Bind b) u0) (CHead d (Bind b0) v)) \to (ex T (\lambda 
(w: T).(ty3 g d v w))))))))))))).(\lambda (v0: T).(\lambda (t3: T).(\lambda 
(i: nat).(\lambda (H4: (subst0 i v0 (THead (Bind b) u0 t1) t3)).(\lambda (b0: 
B).(\lambda (d: C).(\lambda (v: T).(\lambda (H5: (getl i c0 (CHead d (Bind 
b0) v))).(or3_ind (ex2 T (\lambda (u2: T).(eq T t3 (THead (Bind b) u2 t1))) 
(\lambda (u2: T).(subst0 i v0 u0 u2))) (ex2 T (\lambda (t4: T).(eq T t3 
(THead (Bind b) u0 t4))) (\lambda (t4: T).(subst0 (s (Bind b) i) v0 t1 t4))) 
(ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead (Bind b) u2 
t4)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i v0 u0 u2))) (\lambda (_: 
T).(\lambda (t4: T).(subst0 (s (Bind b) i) v0 t1 t4)))) (ex T (\lambda (w: 
T).(ty3 g d v w))) (\lambda (H6: (ex2 T (\lambda (u2: T).(eq T t3 (THead 
(Bind b) u2 t1))) (\lambda (u2: T).(subst0 i v0 u0 u2)))).(ex2_ind T (\lambda 
(u2: T).(eq T t3 (THead (Bind b) u2 t1))) (\lambda (u2: T).(subst0 i v0 u0 
u2)) (ex T (\lambda (w: T).(ty3 g d v w))) (\lambda (x: T).(\lambda (_: (eq T 
t3 (THead (Bind b) x t1))).(\lambda (H8: (subst0 i v0 u0 x)).(H1 v0 x i H8 b0 
d v H5)))) H6)) (\lambda (H6: (ex2 T (\lambda (t4: T).(eq T t3 (THead (Bind 
b) u0 t4))) (\lambda (t4: T).(subst0 (s (Bind b) i) v0 t1 t4)))).(ex2_ind T 
(\lambda (t4: T).(eq T t3 (THead (Bind b) u0 t4))) (\lambda (t4: T).(subst0 
(s (Bind b) i) v0 t1 t4)) (ex T (\lambda (w: T).(ty3 g d v w))) (\lambda (x: 
T).(\lambda (_: (eq T t3 (THead (Bind b) u0 x))).(\lambda (H8: (subst0 (s 
(Bind b) i) v0 t1 x)).(H3 v0 x (S i) H8 b0 d v (getl_head (Bind b) i c0 
(CHead d (Bind b0) v) H5 u0))))) H6)) (\lambda (H6: (ex3_2 T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Bind b) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i v0 u0 u2))) (\lambda (_: T).(\lambda (t4: 
T).(subst0 (s (Bind b) i) v0 t1 t4))))).(ex3_2_ind T T (\lambda (u2: 
T).(\lambda (t4: T).(eq T t3 (THead (Bind b) u2 t4)))) (\lambda (u2: 
T).(\lambda (_: T).(subst0 i v0 u0 u2))) (\lambda (_: T).(\lambda (t4: 
T).(subst0 (s (Bind b) i) v0 t1 t4))) (ex T (\lambda (w: T).(ty3 g d v w))) 
(\lambda (x0: T).(\lambda (x1: T).(\lambda (_: (eq T t3 (THead (Bind b) x0 
x1))).(\lambda (H8: (subst0 i v0 u0 x0)).(\lambda (_: (subst0 (s (Bind b) i) 
v0 t1 x1)).(H1 v0 x0 i H8 b0 d v H5)))))) H6)) (subst0_gen_head (Bind b) v0 
u0 t1 t3 i H4)))))))))))))))))))) (\lambda (c0: C).(\lambda (w: T).(\lambda 
(u0: T).(\lambda (_: (ty3 g c0 w u0)).(\lambda (H1: ((\forall (v0: 
T).(\forall (t0: T).(\forall (i: nat).((subst0 i v0 w t0) \to (\forall (b: 
B).(\forall (d: C).(\forall (v: T).((getl i c0 (CHead d (Bind b) v)) \to (ex 
T (\lambda (w0: T).(ty3 g d v w0))))))))))))).(\lambda (v: T).(\lambda (t0: 
T).(\lambda (_: (ty3 g c0 v (THead (Bind Abst) u0 t0))).(\lambda (H3: 
((\forall (v0: T).(\forall (t1: T).(\forall (i: nat).((subst0 i v0 v t1) \to 
(\forall (b: B).(\forall (d: C).(\forall (v1: T).((getl i c0 (CHead d (Bind 
b) v1)) \to (ex T (\lambda (w0: T).(ty3 g d v1 w0))))))))))))).(\lambda (v0: 
T).(\lambda (t1: T).(\lambda (i: nat).(\lambda (H4: (subst0 i v0 (THead (Flat 
Appl) w v) t1)).(\lambda (b: B).(\lambda (d: C).(\lambda (v1: T).(\lambda 
(H5: (getl i c0 (CHead d (Bind b) v1))).(or3_ind (ex2 T (\lambda (u2: T).(eq 
T t1 (THead (Flat Appl) u2 v))) (\lambda (u2: T).(subst0 i v0 w u2))) (ex2 T 
(\lambda (t2: T).(eq T t1 (THead (Flat Appl) w t2))) (\lambda (t2: T).(subst0 
(s (Flat Appl) i) v0 v t2))) (ex3_2 T T (\lambda (u2: T).(\lambda (t2: T).(eq 
T t1 (THead (Flat Appl) u2 t2)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i 
v0 w u2))) (\lambda (_: T).(\lambda (t2: T).(subst0 (s (Flat Appl) i) v0 v 
t2)))) (ex T (\lambda (w0: T).(ty3 g d v1 w0))) (\lambda (H6: (ex2 T (\lambda 
(u2: T).(eq T t1 (THead (Flat Appl) u2 v))) (\lambda (u2: T).(subst0 i v0 w 
u2)))).(ex2_ind T (\lambda (u2: T).(eq T t1 (THead (Flat Appl) u2 v))) 
(\lambda (u2: T).(subst0 i v0 w u2)) (ex T (\lambda (w0: T).(ty3 g d v1 w0))) 
(\lambda (x: T).(\lambda (_: (eq T t1 (THead (Flat Appl) x v))).(\lambda (H8: 
(subst0 i v0 w x)).(H1 v0 x i H8 b d v1 H5)))) H6)) (\lambda (H6: (ex2 T 
(\lambda (t2: T).(eq T t1 (THead (Flat Appl) w t2))) (\lambda (t2: T).(subst0 
(s (Flat Appl) i) v0 v t2)))).(ex2_ind T (\lambda (t2: T).(eq T t1 (THead 
(Flat Appl) w t2))) (\lambda (t2: T).(subst0 (s (Flat Appl) i) v0 v t2)) (ex 
T (\lambda (w0: T).(ty3 g d v1 w0))) (\lambda (x: T).(\lambda (_: (eq T t1 
(THead (Flat Appl) w x))).(\lambda (H8: (subst0 (s (Flat Appl) i) v0 v 
x)).(H3 v0 x (s (Flat Appl) i) H8 b d v1 H5)))) H6)) (\lambda (H6: (ex3_2 T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T t1 (THead (Flat Appl) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i v0 w u2))) (\lambda (_: 
T).(\lambda (t2: T).(subst0 (s (Flat Appl) i) v0 v t2))))).(ex3_2_ind T T 
(\lambda (u2: T).(\lambda (t2: T).(eq T t1 (THead (Flat Appl) u2 t2)))) 
(\lambda (u2: T).(\lambda (_: T).(subst0 i v0 w u2))) (\lambda (_: 
T).(\lambda (t2: T).(subst0 (s (Flat Appl) i) v0 v t2))) (ex T (\lambda (w0: 
T).(ty3 g d v1 w0))) (\lambda (x0: T).(\lambda (x1: T).(\lambda (_: (eq T t1 
(THead (Flat Appl) x0 x1))).(\lambda (_: (subst0 i v0 w x0)).(\lambda (H9: 
(subst0 (s (Flat Appl) i) v0 v x1)).(H3 v0 x1 (s (Flat Appl) i) H9 b d v1 
H5)))))) H6)) (subst0_gen_head (Flat Appl) v0 w v t1 i H4))))))))))))))))))) 
(\lambda (c0: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda (_: (ty3 g c0 t1 
t2)).(\lambda (H1: ((\forall (v0: T).(\forall (t0: T).(\forall (i: 
nat).((subst0 i v0 t1 t0) \to (\forall (b: B).(\forall (d: C).(\forall (v: 
T).((getl i c0 (CHead d (Bind b) v)) \to (ex T (\lambda (w: T).(ty3 g d v 
w))))))))))))).(\lambda (t0: T).(\lambda (_: (ty3 g c0 t2 t0)).(\lambda (H3: 
((\forall (v0: T).(\forall (t3: T).(\forall (i: nat).((subst0 i v0 t2 t3) \to 
(\forall (b: B).(\forall (d: C).(\forall (v: T).((getl i c0 (CHead d (Bind b) 
v)) \to (ex T (\lambda (w: T).(ty3 g d v w))))))))))))).(\lambda (v0: 
T).(\lambda (t3: T).(\lambda (i: nat).(\lambda (H4: (subst0 i v0 (THead (Flat 
Cast) t2 t1) t3)).(\lambda (b: B).(\lambda (d: C).(\lambda (v: T).(\lambda 
(H5: (getl i c0 (CHead d (Bind b) v))).(or3_ind (ex2 T (\lambda (u2: T).(eq T 
t3 (THead (Flat Cast) u2 t1))) (\lambda (u2: T).(subst0 i v0 t2 u2))) (ex2 T 
(\lambda (t4: T).(eq T t3 (THead (Flat Cast) t2 t4))) (\lambda (t4: 
T).(subst0 (s (Flat Cast) i) v0 t1 t4))) (ex3_2 T T (\lambda (u2: T).(\lambda 
(t4: T).(eq T t3 (THead (Flat Cast) u2 t4)))) (\lambda (u2: T).(\lambda (_: 
T).(subst0 i v0 t2 u2))) (\lambda (_: T).(\lambda (t4: T).(subst0 (s (Flat 
Cast) i) v0 t1 t4)))) (ex T (\lambda (w: T).(ty3 g d v w))) (\lambda (H6: 
(ex2 T (\lambda (u2: T).(eq T t3 (THead (Flat Cast) u2 t1))) (\lambda (u2: 
T).(subst0 i v0 t2 u2)))).(ex2_ind T (\lambda (u2: T).(eq T t3 (THead (Flat 
Cast) u2 t1))) (\lambda (u2: T).(subst0 i v0 t2 u2)) (ex T (\lambda (w: 
T).(ty3 g d v w))) (\lambda (x: T).(\lambda (_: (eq T t3 (THead (Flat Cast) x 
t1))).(\lambda (H8: (subst0 i v0 t2 x)).(H3 v0 x i H8 b d v H5)))) H6)) 
(\lambda (H6: (ex2 T (\lambda (t4: T).(eq T t3 (THead (Flat Cast) t2 t4))) 
(\lambda (t4: T).(subst0 (s (Flat Cast) i) v0 t1 t4)))).(ex2_ind T (\lambda 
(t4: T).(eq T t3 (THead (Flat Cast) t2 t4))) (\lambda (t4: T).(subst0 (s 
(Flat Cast) i) v0 t1 t4)) (ex T (\lambda (w: T).(ty3 g d v w))) (\lambda (x: 
T).(\lambda (_: (eq T t3 (THead (Flat Cast) t2 x))).(\lambda (H8: (subst0 (s 
(Flat Cast) i) v0 t1 x)).(H1 v0 x (s (Flat Cast) i) H8 b d v H5)))) H6)) 
(\lambda (H6: (ex3_2 T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead 
(Flat Cast) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i v0 t2 u2))) 
(\lambda (_: T).(\lambda (t4: T).(subst0 (s (Flat Cast) i) v0 t1 
t4))))).(ex3_2_ind T T (\lambda (u2: T).(\lambda (t4: T).(eq T t3 (THead 
(Flat Cast) u2 t4)))) (\lambda (u2: T).(\lambda (_: T).(subst0 i v0 t2 u2))) 
(\lambda (_: T).(\lambda (t4: T).(subst0 (s (Flat Cast) i) v0 t1 t4))) (ex T 
(\lambda (w: T).(ty3 g d v w))) (\lambda (x0: T).(\lambda (x1: T).(\lambda 
(_: (eq T t3 (THead (Flat Cast) x0 x1))).(\lambda (H8: (subst0 i v0 t2 
x0)).(\lambda (_: (subst0 (s (Flat Cast) i) v0 t1 x1)).(H3 v0 x0 i H8 b d v 
H5)))))) H6)) (subst0_gen_head (Flat Cast) v0 t2 t1 t3 i H4)))))))))))))))))) 
c t u H))))).
(* COMMENTS
Initial nodes: 4343
END *)

