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

include "Basic-1/sty0/defs.ma".

include "Basic-1/getl/drop.ma".

theorem sty0_lift:
 \forall (g: G).(\forall (e: C).(\forall (t1: T).(\forall (t2: T).((sty0 g e 
t1 t2) \to (\forall (c: C).(\forall (h: nat).(\forall (d: nat).((drop h d c 
e) \to (sty0 g c (lift h d t1) (lift h d t2))))))))))
\def
 \lambda (g: G).(\lambda (e: C).(\lambda (t1: T).(\lambda (t2: T).(\lambda 
(H: (sty0 g e t1 t2)).(sty0_ind g (\lambda (c: C).(\lambda (t: T).(\lambda 
(t0: T).(\forall (c0: C).(\forall (h: nat).(\forall (d: nat).((drop h d c0 c) 
\to (sty0 g c0 (lift h d t) (lift h d t0))))))))) (\lambda (c: C).(\lambda 
(n: nat).(\lambda (c0: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (_: 
(drop h d c0 c)).(eq_ind_r T (TSort n) (\lambda (t: T).(sty0 g c0 t (lift h d 
(TSort (next g n))))) (eq_ind_r T (TSort (next g n)) (\lambda (t: T).(sty0 g 
c0 (TSort n) t)) (sty0_sort g c0 n) (lift h d (TSort (next g n))) (lift_sort 
(next g n) h d)) (lift h d (TSort n)) (lift_sort n h d)))))))) (\lambda (c: 
C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: nat).(\lambda (H0: (getl i c 
(CHead d (Bind Abbr) v))).(\lambda (w: T).(\lambda (H1: (sty0 g d v 
w)).(\lambda (H2: ((\forall (c0: C).(\forall (h: nat).(\forall (d0: 
nat).((drop h d0 c0 d) \to (sty0 g c0 (lift h d0 v) (lift h d0 
w)))))))).(\lambda (c0: C).(\lambda (h: nat).(\lambda (d0: nat).(\lambda (H3: 
(drop h d0 c0 c)).(lt_le_e i d0 (sty0 g c0 (lift h d0 (TLRef i)) (lift h d0 
(lift (S i) O w))) (\lambda (H4: (lt i d0)).(let H5 \def (drop_getl_trans_le 
i d0 (le_S_n i d0 (le_S (S i) d0 H4)) c0 c h H3 (CHead d (Bind Abbr) v) H0) 
in (ex3_2_ind C C (\lambda (e0: C).(\lambda (_: C).(drop i O c0 e0))) 
(\lambda (e0: C).(\lambda (e1: C).(drop h (minus d0 i) e0 e1))) (\lambda (_: 
C).(\lambda (e1: C).(clear e1 (CHead d (Bind Abbr) v)))) (sty0 g c0 (lift h 
d0 (TLRef i)) (lift h d0 (lift (S i) O w))) (\lambda (x0: C).(\lambda (x1: 
C).(\lambda (H6: (drop i O c0 x0)).(\lambda (H7: (drop h (minus d0 i) x0 
x1)).(\lambda (H8: (clear x1 (CHead d (Bind Abbr) v))).(let H9 \def (eq_ind 
nat (minus d0 i) (\lambda (n: nat).(drop h n x0 x1)) H7 (S (minus d0 (S i))) 
(minus_x_Sy d0 i H4)) in (let H10 \def (drop_clear_S x1 x0 h (minus d0 (S i)) 
H9 Abbr d v H8) in (ex2_ind C (\lambda (c1: C).(clear x0 (CHead c1 (Bind 
Abbr) (lift h (minus d0 (S i)) v)))) (\lambda (c1: C).(drop h (minus d0 (S 
i)) c1 d)) (sty0 g c0 (lift h d0 (TLRef i)) (lift h d0 (lift (S i) O w))) 
(\lambda (x: C).(\lambda (H11: (clear x0 (CHead x (Bind Abbr) (lift h (minus 
d0 (S i)) v)))).(\lambda (H12: (drop h (minus d0 (S i)) x d)).(eq_ind_r T 
(TLRef i) (\lambda (t: T).(sty0 g c0 t (lift h d0 (lift (S i) O w)))) (eq_ind 
nat (plus (S i) (minus d0 (S i))) (\lambda (n: nat).(sty0 g c0 (TLRef i) 
(lift h n (lift (S i) O w)))) (eq_ind_r T (lift (S i) O (lift h (minus d0 (S 
i)) w)) (\lambda (t: T).(sty0 g c0 (TLRef i) t)) (eq_ind nat d0 (\lambda (_: 
nat).(sty0 g c0 (TLRef i) (lift (S i) O (lift h (minus d0 (S i)) w)))) 
(sty0_abbr g c0 x (lift h (minus d0 (S i)) v) i (getl_intro i c0 (CHead x 
(Bind Abbr) (lift h (minus d0 (S i)) v)) x0 H6 H11) (lift h (minus d0 (S i)) 
w) (H2 x h (minus d0 (S i)) H12)) (plus (S i) (minus d0 (S i))) 
(le_plus_minus (S i) d0 H4)) (lift h (plus (S i) (minus d0 (S i))) (lift (S 
i) O w)) (lift_d w h (S i) (minus d0 (S i)) O (le_O_n (minus d0 (S i))))) d0 
(le_plus_minus_r (S i) d0 H4)) (lift h d0 (TLRef i)) (lift_lref_lt i h d0 
H4))))) H10)))))))) H5))) (\lambda (H4: (le d0 i)).(eq_ind_r T (TLRef (plus i 
h)) (\lambda (t: T).(sty0 g c0 t (lift h d0 (lift (S i) O w)))) (eq_ind nat 
(S i) (\lambda (_: nat).(sty0 g c0 (TLRef (plus i h)) (lift h d0 (lift (S i) 
O w)))) (eq_ind_r T (lift (plus h (S i)) O w) (\lambda (t: T).(sty0 g c0 
(TLRef (plus i h)) t)) (eq_ind_r nat (plus (S i) h) (\lambda (n: nat).(sty0 g 
c0 (TLRef (plus i h)) (lift n O w))) (sty0_abbr g c0 d v (plus i h) 
(drop_getl_trans_ge i c0 c d0 h H3 (CHead d (Bind Abbr) v) H0 H4) w H1) (plus 
h (S i)) (plus_sym h (S i))) (lift h d0 (lift (S i) O w)) (lift_free w (S i) 
h O d0 (le_S d0 i H4) (le_O_n d0))) (plus i (S O)) (eq_ind_r nat (plus (S O) 
i) (\lambda (n: nat).(eq nat (S i) n)) (refl_equal nat (plus (S O) i)) (plus 
i (S O)) (plus_sym i (S O)))) (lift h d0 (TLRef i)) (lift_lref_ge i h d0 
H4)))))))))))))))) (\lambda (c: C).(\lambda (d: C).(\lambda (v: T).(\lambda 
(i: nat).(\lambda (H0: (getl i c (CHead d (Bind Abst) v))).(\lambda (w: 
T).(\lambda (H1: (sty0 g d v w)).(\lambda (H2: ((\forall (c0: C).(\forall (h: 
nat).(\forall (d0: nat).((drop h d0 c0 d) \to (sty0 g c0 (lift h d0 v) (lift 
h d0 w)))))))).(\lambda (c0: C).(\lambda (h: nat).(\lambda (d0: nat).(\lambda 
(H3: (drop h d0 c0 c)).(lt_le_e i d0 (sty0 g c0 (lift h d0 (TLRef i)) (lift h 
d0 (lift (S i) O v))) (\lambda (H4: (lt i d0)).(let H5 \def 
(drop_getl_trans_le i d0 (le_S_n i d0 (le_S (S i) d0 H4)) c0 c h H3 (CHead d 
(Bind Abst) v) H0) in (ex3_2_ind C C (\lambda (e0: C).(\lambda (_: C).(drop i 
O c0 e0))) (\lambda (e0: C).(\lambda (e1: C).(drop h (minus d0 i) e0 e1))) 
(\lambda (_: C).(\lambda (e1: C).(clear e1 (CHead d (Bind Abst) v)))) (sty0 g 
c0 (lift h d0 (TLRef i)) (lift h d0 (lift (S i) O v))) (\lambda (x0: 
C).(\lambda (x1: C).(\lambda (H6: (drop i O c0 x0)).(\lambda (H7: (drop h 
(minus d0 i) x0 x1)).(\lambda (H8: (clear x1 (CHead d (Bind Abst) v))).(let 
H9 \def (eq_ind nat (minus d0 i) (\lambda (n: nat).(drop h n x0 x1)) H7 (S 
(minus d0 (S i))) (minus_x_Sy d0 i H4)) in (let H10 \def (drop_clear_S x1 x0 
h (minus d0 (S i)) H9 Abst d v H8) in (ex2_ind C (\lambda (c1: C).(clear x0 
(CHead c1 (Bind Abst) (lift h (minus d0 (S i)) v)))) (\lambda (c1: C).(drop h 
(minus d0 (S i)) c1 d)) (sty0 g c0 (lift h d0 (TLRef i)) (lift h d0 (lift (S 
i) O v))) (\lambda (x: C).(\lambda (H11: (clear x0 (CHead x (Bind Abst) (lift 
h (minus d0 (S i)) v)))).(\lambda (H12: (drop h (minus d0 (S i)) x 
d)).(eq_ind_r T (TLRef i) (\lambda (t: T).(sty0 g c0 t (lift h d0 (lift (S i) 
O v)))) (eq_ind nat (plus (S i) (minus d0 (S i))) (\lambda (n: nat).(sty0 g 
c0 (TLRef i) (lift h n (lift (S i) O v)))) (eq_ind_r T (lift (S i) O (lift h 
(minus d0 (S i)) v)) (\lambda (t: T).(sty0 g c0 (TLRef i) t)) (eq_ind nat d0 
(\lambda (_: nat).(sty0 g c0 (TLRef i) (lift (S i) O (lift h (minus d0 (S i)) 
v)))) (sty0_abst g c0 x (lift h (minus d0 (S i)) v) i (getl_intro i c0 (CHead 
x (Bind Abst) (lift h (minus d0 (S i)) v)) x0 H6 H11) (lift h (minus d0 (S 
i)) w) (H2 x h (minus d0 (S i)) H12)) (plus (S i) (minus d0 (S i))) 
(le_plus_minus (S i) d0 H4)) (lift h (plus (S i) (minus d0 (S i))) (lift (S 
i) O v)) (lift_d v h (S i) (minus d0 (S i)) O (le_O_n (minus d0 (S i))))) d0 
(le_plus_minus_r (S i) d0 H4)) (lift h d0 (TLRef i)) (lift_lref_lt i h d0 
H4))))) H10)))))))) H5))) (\lambda (H4: (le d0 i)).(eq_ind_r T (TLRef (plus i 
h)) (\lambda (t: T).(sty0 g c0 t (lift h d0 (lift (S i) O v)))) (eq_ind nat 
(S i) (\lambda (_: nat).(sty0 g c0 (TLRef (plus i h)) (lift h d0 (lift (S i) 
O v)))) (eq_ind_r T (lift (plus h (S i)) O v) (\lambda (t: T).(sty0 g c0 
(TLRef (plus i h)) t)) (eq_ind_r nat (plus (S i) h) (\lambda (n: nat).(sty0 g 
c0 (TLRef (plus i h)) (lift n O v))) (sty0_abst g c0 d v (plus i h) 
(drop_getl_trans_ge i c0 c d0 h H3 (CHead d (Bind Abst) v) H0 H4) w H1) (plus 
h (S i)) (plus_sym h (S i))) (lift h d0 (lift (S i) O v)) (lift_free v (S i) 
h O d0 (le_S d0 i H4) (le_O_n d0))) (plus i (S O)) (eq_ind_r nat (plus (S O) 
i) (\lambda (n: nat).(eq nat (S i) n)) (refl_equal nat (plus (S O) i)) (plus 
i (S O)) (plus_sym i (S O)))) (lift h d0 (TLRef i)) (lift_lref_ge i h d0 
H4)))))))))))))))) (\lambda (b: B).(\lambda (c: C).(\lambda (v: T).(\lambda 
(t3: T).(\lambda (t4: T).(\lambda (_: (sty0 g (CHead c (Bind b) v) t3 
t4)).(\lambda (H1: ((\forall (c0: C).(\forall (h: nat).(\forall (d: 
nat).((drop h d c0 (CHead c (Bind b) v)) \to (sty0 g c0 (lift h d t3) (lift h 
d t4)))))))).(\lambda (c0: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda 
(H2: (drop h d c0 c)).(eq_ind_r T (THead (Bind b) (lift h d v) (lift h (s 
(Bind b) d) t3)) (\lambda (t: T).(sty0 g c0 t (lift h d (THead (Bind b) v 
t4)))) (eq_ind_r T (THead (Bind b) (lift h d v) (lift h (s (Bind b) d) t4)) 
(\lambda (t: T).(sty0 g c0 (THead (Bind b) (lift h d v) (lift h (s (Bind b) 
d) t3)) t)) (sty0_bind g b c0 (lift h d v) (lift h (S d) t3) (lift h (S d) 
t4) (H1 (CHead c0 (Bind b) (lift h d v)) h (S d) (drop_skip_bind h d c0 c H2 
b v))) (lift h d (THead (Bind b) v t4)) (lift_head (Bind b) v t4 h d)) (lift 
h d (THead (Bind b) v t3)) (lift_head (Bind b) v t3 h d))))))))))))) (\lambda 
(c: C).(\lambda (v: T).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (sty0 g 
c t3 t4)).(\lambda (H1: ((\forall (c0: C).(\forall (h: nat).(\forall (d: 
nat).((drop h d c0 c) \to (sty0 g c0 (lift h d t3) (lift h d 
t4)))))))).(\lambda (c0: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H2: 
(drop h d c0 c)).(eq_ind_r T (THead (Flat Appl) (lift h d v) (lift h (s (Flat 
Appl) d) t3)) (\lambda (t: T).(sty0 g c0 t (lift h d (THead (Flat Appl) v 
t4)))) (eq_ind_r T (THead (Flat Appl) (lift h d v) (lift h (s (Flat Appl) d) 
t4)) (\lambda (t: T).(sty0 g c0 (THead (Flat Appl) (lift h d v) (lift h (s 
(Flat Appl) d) t3)) t)) (sty0_appl g c0 (lift h d v) (lift h (s (Flat Appl) 
d) t3) (lift h (s (Flat Appl) d) t4) (H1 c0 h (s (Flat Appl) d) H2)) (lift h 
d (THead (Flat Appl) v t4)) (lift_head (Flat Appl) v t4 h d)) (lift h d 
(THead (Flat Appl) v t3)) (lift_head (Flat Appl) v t3 h d)))))))))))) 
(\lambda (c: C).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (sty0 g c v1 
v2)).(\lambda (H1: ((\forall (c0: C).(\forall (h: nat).(\forall (d: 
nat).((drop h d c0 c) \to (sty0 g c0 (lift h d v1) (lift h d 
v2)))))))).(\lambda (t3: T).(\lambda (t4: T).(\lambda (_: (sty0 g c t3 
t4)).(\lambda (H3: ((\forall (c0: C).(\forall (h: nat).(\forall (d: 
nat).((drop h d c0 c) \to (sty0 g c0 (lift h d t3) (lift h d 
t4)))))))).(\lambda (c0: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H4: 
(drop h d c0 c)).(eq_ind_r T (THead (Flat Cast) (lift h d v1) (lift h (s 
(Flat Cast) d) t3)) (\lambda (t: T).(sty0 g c0 t (lift h d (THead (Flat Cast) 
v2 t4)))) (eq_ind_r T (THead (Flat Cast) (lift h d v2) (lift h (s (Flat Cast) 
d) t4)) (\lambda (t: T).(sty0 g c0 (THead (Flat Cast) (lift h d v1) (lift h 
(s (Flat Cast) d) t3)) t)) (sty0_cast g c0 (lift h d v1) (lift h d v2) (H1 c0 
h d H4) (lift h (s (Flat Cast) d) t3) (lift h (s (Flat Cast) d) t4) (H3 c0 h 
(s (Flat Cast) d) H4)) (lift h d (THead (Flat Cast) v2 t4)) (lift_head (Flat 
Cast) v2 t4 h d)) (lift h d (THead (Flat Cast) v1 t3)) (lift_head (Flat Cast) 
v1 t3 h d))))))))))))))) e t1 t2 H))))).
(* COMMENTS
Initial nodes: 3677
END *)

theorem sty0_correct:
 \forall (g: G).(\forall (c: C).(\forall (t1: T).(\forall (t: T).((sty0 g c 
t1 t) \to (ex T (\lambda (t2: T).(sty0 g c t t2)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t1: T).(\lambda (t: T).(\lambda (H: 
(sty0 g c t1 t)).(sty0_ind g (\lambda (c0: C).(\lambda (_: T).(\lambda (t2: 
T).(ex T (\lambda (t3: T).(sty0 g c0 t2 t3)))))) (\lambda (c0: C).(\lambda 
(n: nat).(ex_intro T (\lambda (t2: T).(sty0 g c0 (TSort (next g n)) t2)) 
(TSort (next g (next g n))) (sty0_sort g c0 (next g n))))) (\lambda (c0: 
C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: nat).(\lambda (H0: (getl i c0 
(CHead d (Bind Abbr) v))).(\lambda (w: T).(\lambda (_: (sty0 g d v 
w)).(\lambda (H2: (ex T (\lambda (t2: T).(sty0 g d w t2)))).(let H3 \def H2 
in (ex_ind T (\lambda (t2: T).(sty0 g d w t2)) (ex T (\lambda (t2: T).(sty0 g 
c0 (lift (S i) O w) t2))) (\lambda (x: T).(\lambda (H4: (sty0 g d w 
x)).(ex_intro T (\lambda (t2: T).(sty0 g c0 (lift (S i) O w) t2)) (lift (S i) 
O x) (sty0_lift g d w x H4 c0 (S i) O (getl_drop Abbr c0 d v i H0))))) 
H3)))))))))) (\lambda (c0: C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: 
nat).(\lambda (H0: (getl i c0 (CHead d (Bind Abst) v))).(\lambda (w: 
T).(\lambda (H1: (sty0 g d v w)).(\lambda (H2: (ex T (\lambda (t2: T).(sty0 g 
d w t2)))).(let H3 \def H2 in (ex_ind T (\lambda (t2: T).(sty0 g d w t2)) (ex 
T (\lambda (t2: T).(sty0 g c0 (lift (S i) O v) t2))) (\lambda (x: T).(\lambda 
(_: (sty0 g d w x)).(ex_intro T (\lambda (t2: T).(sty0 g c0 (lift (S i) O v) 
t2)) (lift (S i) O w) (sty0_lift g d v w H1 c0 (S i) O (getl_drop Abst c0 d v 
i H0))))) H3)))))))))) (\lambda (b: B).(\lambda (c0: C).(\lambda (v: 
T).(\lambda (t2: T).(\lambda (t3: T).(\lambda (_: (sty0 g (CHead c0 (Bind b) 
v) t2 t3)).(\lambda (H1: (ex T (\lambda (t4: T).(sty0 g (CHead c0 (Bind b) v) 
t3 t4)))).(let H2 \def H1 in (ex_ind T (\lambda (t4: T).(sty0 g (CHead c0 
(Bind b) v) t3 t4)) (ex T (\lambda (t4: T).(sty0 g c0 (THead (Bind b) v t3) 
t4))) (\lambda (x: T).(\lambda (H3: (sty0 g (CHead c0 (Bind b) v) t3 
x)).(ex_intro T (\lambda (t4: T).(sty0 g c0 (THead (Bind b) v t3) t4)) (THead 
(Bind b) v x) (sty0_bind g b c0 v t3 x H3)))) H2))))))))) (\lambda (c0: 
C).(\lambda (v: T).(\lambda (t2: T).(\lambda (t3: T).(\lambda (_: (sty0 g c0 
t2 t3)).(\lambda (H1: (ex T (\lambda (t4: T).(sty0 g c0 t3 t4)))).(let H2 
\def H1 in (ex_ind T (\lambda (t4: T).(sty0 g c0 t3 t4)) (ex T (\lambda (t4: 
T).(sty0 g c0 (THead (Flat Appl) v t3) t4))) (\lambda (x: T).(\lambda (H3: 
(sty0 g c0 t3 x)).(ex_intro T (\lambda (t4: T).(sty0 g c0 (THead (Flat Appl) 
v t3) t4)) (THead (Flat Appl) v x) (sty0_appl g c0 v t3 x H3)))) H2)))))))) 
(\lambda (c0: C).(\lambda (v1: T).(\lambda (v2: T).(\lambda (_: (sty0 g c0 v1 
v2)).(\lambda (H1: (ex T (\lambda (t2: T).(sty0 g c0 v2 t2)))).(\lambda (t2: 
T).(\lambda (t3: T).(\lambda (_: (sty0 g c0 t2 t3)).(\lambda (H3: (ex T 
(\lambda (t4: T).(sty0 g c0 t3 t4)))).(let H4 \def H1 in (ex_ind T (\lambda 
(t4: T).(sty0 g c0 v2 t4)) (ex T (\lambda (t4: T).(sty0 g c0 (THead (Flat 
Cast) v2 t3) t4))) (\lambda (x: T).(\lambda (H5: (sty0 g c0 v2 x)).(let H6 
\def H3 in (ex_ind T (\lambda (t4: T).(sty0 g c0 t3 t4)) (ex T (\lambda (t4: 
T).(sty0 g c0 (THead (Flat Cast) v2 t3) t4))) (\lambda (x0: T).(\lambda (H7: 
(sty0 g c0 t3 x0)).(ex_intro T (\lambda (t4: T).(sty0 g c0 (THead (Flat Cast) 
v2 t3) t4)) (THead (Flat Cast) x x0) (sty0_cast g c0 v2 x H5 t3 x0 H7)))) 
H6)))) H4))))))))))) c t1 t H))))).
(* COMMENTS
Initial nodes: 991
END *)

