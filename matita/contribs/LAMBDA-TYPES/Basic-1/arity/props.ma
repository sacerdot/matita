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

include "Basic-1/arity/fwd.ma".

theorem node_inh:
 \forall (g: G).(\forall (n: nat).(\forall (k: nat).(ex_2 C T (\lambda (c: 
C).(\lambda (t: T).(arity g c t (ASort k n)))))))
\def
 \lambda (g: G).(\lambda (n: nat).(\lambda (k: nat).(nat_ind (\lambda (n0: 
nat).(ex_2 C T (\lambda (c: C).(\lambda (t: T).(arity g c t (ASort n0 n)))))) 
(ex_2_intro C T (\lambda (c: C).(\lambda (t: T).(arity g c t (ASort O n)))) 
(CSort O) (TSort n) (arity_sort g (CSort O) n)) (\lambda (n0: nat).(\lambda 
(H: (ex_2 C T (\lambda (c: C).(\lambda (t: T).(arity g c t (ASort n0 
n)))))).(let H0 \def H in (ex_2_ind C T (\lambda (c: C).(\lambda (t: 
T).(arity g c t (ASort n0 n)))) (ex_2 C T (\lambda (c: C).(\lambda (t: 
T).(arity g c t (ASort (S n0) n))))) (\lambda (x0: C).(\lambda (x1: 
T).(\lambda (H1: (arity g x0 x1 (ASort n0 n))).(ex_2_intro C T (\lambda (c: 
C).(\lambda (t: T).(arity g c t (ASort (S n0) n)))) (CHead x0 (Bind Abst) x1) 
(TLRef O) (arity_abst g (CHead x0 (Bind Abst) x1) x0 x1 O (getl_refl Abst x0 
x1) (ASort (S n0) n) H1))))) H0)))) k))).
(* COMMENTS
Initial nodes: 253
END *)

theorem arity_lift:
 \forall (g: G).(\forall (c2: C).(\forall (t: T).(\forall (a: A).((arity g c2 
t a) \to (\forall (c1: C).(\forall (h: nat).(\forall (d: nat).((drop h d c1 
c2) \to (arity g c1 (lift h d t) a)))))))))
\def
 \lambda (g: G).(\lambda (c2: C).(\lambda (t: T).(\lambda (a: A).(\lambda (H: 
(arity g c2 t a)).(arity_ind g (\lambda (c: C).(\lambda (t0: T).(\lambda (a0: 
A).(\forall (c1: C).(\forall (h: nat).(\forall (d: nat).((drop h d c1 c) \to 
(arity g c1 (lift h d t0) a0)))))))) (\lambda (c: C).(\lambda (n: 
nat).(\lambda (c1: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (_: (drop 
h d c1 c)).(eq_ind_r T (TSort n) (\lambda (t0: T).(arity g c1 t0 (ASort O 
n))) (arity_sort g c1 n) (lift h d (TSort n)) (lift_sort n h d)))))))) 
(\lambda (c: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda 
(H0: (getl i c (CHead d (Bind Abbr) u))).(\lambda (a0: A).(\lambda (H1: 
(arity g d u a0)).(\lambda (H2: ((\forall (c1: C).(\forall (h: nat).(\forall 
(d0: nat).((drop h d0 c1 d) \to (arity g c1 (lift h d0 u) a0))))))).(\lambda 
(c1: C).(\lambda (h: nat).(\lambda (d0: nat).(\lambda (H3: (drop h d0 c1 
c)).(lt_le_e i d0 (arity g c1 (lift h d0 (TLRef i)) a0) (\lambda (H4: (lt i 
d0)).(eq_ind_r T (TLRef i) (\lambda (t0: T).(arity g c1 t0 a0)) (let H5 \def 
(drop_getl_trans_le i d0 (le_S_n i d0 (le_S (S i) d0 H4)) c1 c h H3 (CHead d 
(Bind Abbr) u) H0) in (ex3_2_ind C C (\lambda (e0: C).(\lambda (_: C).(drop i 
O c1 e0))) (\lambda (e0: C).(\lambda (e1: C).(drop h (minus d0 i) e0 e1))) 
(\lambda (_: C).(\lambda (e1: C).(clear e1 (CHead d (Bind Abbr) u)))) (arity 
g c1 (TLRef i) a0) (\lambda (x0: C).(\lambda (x1: C).(\lambda (H6: (drop i O 
c1 x0)).(\lambda (H7: (drop h (minus d0 i) x0 x1)).(\lambda (H8: (clear x1 
(CHead d (Bind Abbr) u))).(let H9 \def (eq_ind nat (minus d0 i) (\lambda (n: 
nat).(drop h n x0 x1)) H7 (S (minus d0 (S i))) (minus_x_Sy d0 i H4)) in (let 
H10 \def (drop_clear_S x1 x0 h (minus d0 (S i)) H9 Abbr d u H8) in (ex2_ind C 
(\lambda (c3: C).(clear x0 (CHead c3 (Bind Abbr) (lift h (minus d0 (S i)) 
u)))) (\lambda (c3: C).(drop h (minus d0 (S i)) c3 d)) (arity g c1 (TLRef i) 
a0) (\lambda (x: C).(\lambda (H11: (clear x0 (CHead x (Bind Abbr) (lift h 
(minus d0 (S i)) u)))).(\lambda (H12: (drop h (minus d0 (S i)) x 
d)).(arity_abbr g c1 x (lift h (minus d0 (S i)) u) i (getl_intro i c1 (CHead 
x (Bind Abbr) (lift h (minus d0 (S i)) u)) x0 H6 H11) a0 (H2 x h (minus d0 (S 
i)) H12))))) H10)))))))) H5)) (lift h d0 (TLRef i)) (lift_lref_lt i h d0 
H4))) (\lambda (H4: (le d0 i)).(eq_ind_r T (TLRef (plus i h)) (\lambda (t0: 
T).(arity g c1 t0 a0)) (arity_abbr g c1 d u (plus i h) (drop_getl_trans_ge i 
c1 c d0 h H3 (CHead d (Bind Abbr) u) H0 H4) a0 H1) (lift h d0 (TLRef i)) 
(lift_lref_ge i h d0 H4)))))))))))))))) (\lambda (c: C).(\lambda (d: 
C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl i c (CHead d (Bind 
Abst) u))).(\lambda (a0: A).(\lambda (H1: (arity g d u (asucc g 
a0))).(\lambda (H2: ((\forall (c1: C).(\forall (h: nat).(\forall (d0: 
nat).((drop h d0 c1 d) \to (arity g c1 (lift h d0 u) (asucc g 
a0)))))))).(\lambda (c1: C).(\lambda (h: nat).(\lambda (d0: nat).(\lambda 
(H3: (drop h d0 c1 c)).(lt_le_e i d0 (arity g c1 (lift h d0 (TLRef i)) a0) 
(\lambda (H4: (lt i d0)).(eq_ind_r T (TLRef i) (\lambda (t0: T).(arity g c1 
t0 a0)) (let H5 \def (drop_getl_trans_le i d0 (le_S_n i d0 (le_S (S i) d0 
H4)) c1 c h H3 (CHead d (Bind Abst) u) H0) in (ex3_2_ind C C (\lambda (e0: 
C).(\lambda (_: C).(drop i O c1 e0))) (\lambda (e0: C).(\lambda (e1: C).(drop 
h (minus d0 i) e0 e1))) (\lambda (_: C).(\lambda (e1: C).(clear e1 (CHead d 
(Bind Abst) u)))) (arity g c1 (TLRef i) a0) (\lambda (x0: C).(\lambda (x1: 
C).(\lambda (H6: (drop i O c1 x0)).(\lambda (H7: (drop h (minus d0 i) x0 
x1)).(\lambda (H8: (clear x1 (CHead d (Bind Abst) u))).(let H9 \def (eq_ind 
nat (minus d0 i) (\lambda (n: nat).(drop h n x0 x1)) H7 (S (minus d0 (S i))) 
(minus_x_Sy d0 i H4)) in (let H10 \def (drop_clear_S x1 x0 h (minus d0 (S i)) 
H9 Abst d u H8) in (ex2_ind C (\lambda (c3: C).(clear x0 (CHead c3 (Bind 
Abst) (lift h (minus d0 (S i)) u)))) (\lambda (c3: C).(drop h (minus d0 (S 
i)) c3 d)) (arity g c1 (TLRef i) a0) (\lambda (x: C).(\lambda (H11: (clear x0 
(CHead x (Bind Abst) (lift h (minus d0 (S i)) u)))).(\lambda (H12: (drop h 
(minus d0 (S i)) x d)).(arity_abst g c1 x (lift h (minus d0 (S i)) u) i 
(getl_intro i c1 (CHead x (Bind Abst) (lift h (minus d0 (S i)) u)) x0 H6 H11) 
a0 (H2 x h (minus d0 (S i)) H12))))) H10)))))))) H5)) (lift h d0 (TLRef i)) 
(lift_lref_lt i h d0 H4))) (\lambda (H4: (le d0 i)).(eq_ind_r T (TLRef (plus 
i h)) (\lambda (t0: T).(arity g c1 t0 a0)) (arity_abst g c1 d u (plus i h) 
(drop_getl_trans_ge i c1 c d0 h H3 (CHead d (Bind Abst) u) H0 H4) a0 H1) 
(lift h d0 (TLRef i)) (lift_lref_ge i h d0 H4)))))))))))))))) (\lambda (b: 
B).(\lambda (H0: (not (eq B b Abst))).(\lambda (c: C).(\lambda (u: 
T).(\lambda (a1: A).(\lambda (_: (arity g c u a1)).(\lambda (H2: ((\forall 
(c1: C).(\forall (h: nat).(\forall (d: nat).((drop h d c1 c) \to (arity g c1 
(lift h d u) a1))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity 
g (CHead c (Bind b) u) t0 a2)).(\lambda (H4: ((\forall (c1: C).(\forall (h: 
nat).(\forall (d: nat).((drop h d c1 (CHead c (Bind b) u)) \to (arity g c1 
(lift h d t0) a2))))))).(\lambda (c1: C).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H5: (drop h d c1 c)).(eq_ind_r T (THead (Bind b) (lift h d u) 
(lift h (s (Bind b) d) t0)) (\lambda (t1: T).(arity g c1 t1 a2)) (arity_bind 
g b H0 c1 (lift h d u) a1 (H2 c1 h d H5) (lift h (s (Bind b) d) t0) a2 (H4 
(CHead c1 (Bind b) (lift h d u)) h (s (Bind b) d) (drop_skip_bind h d c1 c H5 
b u))) (lift h d (THead (Bind b) u t0)) (lift_head (Bind b) u t0 h 
d))))))))))))))))) (\lambda (c: C).(\lambda (u: T).(\lambda (a1: A).(\lambda 
(_: (arity g c u (asucc g a1))).(\lambda (H1: ((\forall (c1: C).(\forall (h: 
nat).(\forall (d: nat).((drop h d c1 c) \to (arity g c1 (lift h d u) (asucc g 
a1)))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity g (CHead c 
(Bind Abst) u) t0 a2)).(\lambda (H3: ((\forall (c1: C).(\forall (h: 
nat).(\forall (d: nat).((drop h d c1 (CHead c (Bind Abst) u)) \to (arity g c1 
(lift h d t0) a2))))))).(\lambda (c1: C).(\lambda (h: nat).(\lambda (d: 
nat).(\lambda (H4: (drop h d c1 c)).(eq_ind_r T (THead (Bind Abst) (lift h d 
u) (lift h (s (Bind Abst) d) t0)) (\lambda (t1: T).(arity g c1 t1 (AHead a1 
a2))) (arity_head g c1 (lift h d u) a1 (H1 c1 h d H4) (lift h (s (Bind Abst) 
d) t0) a2 (H3 (CHead c1 (Bind Abst) (lift h d u)) h (s (Bind Abst) d) 
(drop_skip_bind h d c1 c H4 Abst u))) (lift h d (THead (Bind Abst) u t0)) 
(lift_head (Bind Abst) u t0 h d))))))))))))))) (\lambda (c: C).(\lambda (u: 
T).(\lambda (a1: A).(\lambda (_: (arity g c u a1)).(\lambda (H1: ((\forall 
(c1: C).(\forall (h: nat).(\forall (d: nat).((drop h d c1 c) \to (arity g c1 
(lift h d u) a1))))))).(\lambda (t0: T).(\lambda (a2: A).(\lambda (_: (arity 
g c t0 (AHead a1 a2))).(\lambda (H3: ((\forall (c1: C).(\forall (h: 
nat).(\forall (d: nat).((drop h d c1 c) \to (arity g c1 (lift h d t0) (AHead 
a1 a2)))))))).(\lambda (c1: C).(\lambda (h: nat).(\lambda (d: nat).(\lambda 
(H4: (drop h d c1 c)).(eq_ind_r T (THead (Flat Appl) (lift h d u) (lift h (s 
(Flat Appl) d) t0)) (\lambda (t1: T).(arity g c1 t1 a2)) (arity_appl g c1 
(lift h d u) a1 (H1 c1 h d H4) (lift h (s (Flat Appl) d) t0) a2 (H3 c1 h (s 
(Flat Appl) d) H4)) (lift h d (THead (Flat Appl) u t0)) (lift_head (Flat 
Appl) u t0 h d))))))))))))))) (\lambda (c: C).(\lambda (u: T).(\lambda (a0: 
A).(\lambda (_: (arity g c u (asucc g a0))).(\lambda (H1: ((\forall (c1: 
C).(\forall (h: nat).(\forall (d: nat).((drop h d c1 c) \to (arity g c1 (lift 
h d u) (asucc g a0)))))))).(\lambda (t0: T).(\lambda (_: (arity g c t0 
a0)).(\lambda (H3: ((\forall (c1: C).(\forall (h: nat).(\forall (d: 
nat).((drop h d c1 c) \to (arity g c1 (lift h d t0) a0))))))).(\lambda (c1: 
C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H4: (drop h d c1 
c)).(eq_ind_r T (THead (Flat Cast) (lift h d u) (lift h (s (Flat Cast) d) 
t0)) (\lambda (t1: T).(arity g c1 t1 a0)) (arity_cast g c1 (lift h d u) a0 
(H1 c1 h d H4) (lift h (s (Flat Cast) d) t0) (H3 c1 h (s (Flat Cast) d) H4)) 
(lift h d (THead (Flat Cast) u t0)) (lift_head (Flat Cast) u t0 h 
d)))))))))))))) (\lambda (c: C).(\lambda (t0: T).(\lambda (a1: A).(\lambda 
(_: (arity g c t0 a1)).(\lambda (H1: ((\forall (c1: C).(\forall (h: 
nat).(\forall (d: nat).((drop h d c1 c) \to (arity g c1 (lift h d t0) 
a1))))))).(\lambda (a2: A).(\lambda (H2: (leq g a1 a2)).(\lambda (c1: 
C).(\lambda (h: nat).(\lambda (d: nat).(\lambda (H3: (drop h d c1 
c)).(arity_repl g c1 (lift h d t0) a1 (H1 c1 h d H3) a2 H2)))))))))))) c2 t a 
H))))).
(* COMMENTS
Initial nodes: 2661
END *)

theorem arity_mono:
 \forall (g: G).(\forall (c: C).(\forall (t: T).(\forall (a1: A).((arity g c 
t a1) \to (\forall (a2: A).((arity g c t a2) \to (leq g a1 a2)))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (t: T).(\lambda (a1: A).(\lambda (H: 
(arity g c t a1)).(arity_ind g (\lambda (c0: C).(\lambda (t0: T).(\lambda (a: 
A).(\forall (a2: A).((arity g c0 t0 a2) \to (leq g a a2)))))) (\lambda (c0: 
C).(\lambda (n: nat).(\lambda (a2: A).(\lambda (H0: (arity g c0 (TSort n) 
a2)).(leq_sym g a2 (ASort O n) (arity_gen_sort g c0 n a2 H0)))))) (\lambda 
(c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl 
i c0 (CHead d (Bind Abbr) u))).(\lambda (a: A).(\lambda (_: (arity g d u 
a)).(\lambda (H2: ((\forall (a2: A).((arity g d u a2) \to (leq g a 
a2))))).(\lambda (a2: A).(\lambda (H3: (arity g c0 (TLRef i) a2)).(let H4 
\def (arity_gen_lref g c0 i a2 H3) in (or_ind (ex2_2 C T (\lambda (d0: 
C).(\lambda (u0: T).(getl i c0 (CHead d0 (Bind Abbr) u0)))) (\lambda (d0: 
C).(\lambda (u0: T).(arity g d0 u0 a2)))) (ex2_2 C T (\lambda (d0: 
C).(\lambda (u0: T).(getl i c0 (CHead d0 (Bind Abst) u0)))) (\lambda (d0: 
C).(\lambda (u0: T).(arity g d0 u0 (asucc g a2))))) (leq g a a2) (\lambda 
(H5: (ex2_2 C T (\lambda (d0: C).(\lambda (u0: T).(getl i c0 (CHead d0 (Bind 
Abbr) u0)))) (\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 
a2))))).(ex2_2_ind C T (\lambda (d0: C).(\lambda (u0: T).(getl i c0 (CHead d0 
(Bind Abbr) u0)))) (\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 a2))) 
(leq g a a2) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: (getl i c0 
(CHead x0 (Bind Abbr) x1))).(\lambda (H7: (arity g x0 x1 a2)).(let H8 \def 
(eq_ind C (CHead d (Bind Abbr) u) (\lambda (c1: C).(getl i c0 c1)) H0 (CHead 
x0 (Bind Abbr) x1) (getl_mono c0 (CHead d (Bind Abbr) u) i H0 (CHead x0 (Bind 
Abbr) x1) H6)) in (let H9 \def (f_equal C C (\lambda (e: C).(match e in C 
return (\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c1 _ _) 
\Rightarrow c1])) (CHead d (Bind Abbr) u) (CHead x0 (Bind Abbr) x1) 
(getl_mono c0 (CHead d (Bind Abbr) u) i H0 (CHead x0 (Bind Abbr) x1) H6)) in 
((let H10 \def (f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: 
C).T) with [(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) (CHead 
d (Bind Abbr) u) (CHead x0 (Bind Abbr) x1) (getl_mono c0 (CHead d (Bind Abbr) 
u) i H0 (CHead x0 (Bind Abbr) x1) H6)) in (\lambda (H11: (eq C d x0)).(let 
H12 \def (eq_ind_r T x1 (\lambda (t0: T).(getl i c0 (CHead x0 (Bind Abbr) 
t0))) H8 u H10) in (let H13 \def (eq_ind_r T x1 (\lambda (t0: T).(arity g x0 
t0 a2)) H7 u H10) in (let H14 \def (eq_ind_r C x0 (\lambda (c1: C).(getl i c0 
(CHead c1 (Bind Abbr) u))) H12 d H11) in (let H15 \def (eq_ind_r C x0 
(\lambda (c1: C).(arity g c1 u a2)) H13 d H11) in (H2 a2 H15))))))) H9))))))) 
H5)) (\lambda (H5: (ex2_2 C T (\lambda (d0: C).(\lambda (u0: T).(getl i c0 
(CHead d0 (Bind Abst) u0)))) (\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 
(asucc g a2)))))).(ex2_2_ind C T (\lambda (d0: C).(\lambda (u0: T).(getl i c0 
(CHead d0 (Bind Abst) u0)))) (\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 
(asucc g a2)))) (leq g a a2) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: 
(getl i c0 (CHead x0 (Bind Abst) x1))).(\lambda (_: (arity g x0 x1 (asucc g 
a2))).(let H8 \def (eq_ind C (CHead d (Bind Abbr) u) (\lambda (c1: C).(getl i 
c0 c1)) H0 (CHead x0 (Bind Abst) x1) (getl_mono c0 (CHead d (Bind Abbr) u) i 
H0 (CHead x0 (Bind Abst) x1) H6)) in (let H9 \def (eq_ind C (CHead d (Bind 
Abbr) u) (\lambda (ee: C).(match ee in C return (\lambda (_: C).Prop) with 
[(CSort _) \Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return 
(\lambda (_: K).Prop) with [(Bind b) \Rightarrow (match b in B return 
(\lambda (_: B).Prop) with [Abbr \Rightarrow True | Abst \Rightarrow False | 
Void \Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead x0 (Bind 
Abst) x1) (getl_mono c0 (CHead d (Bind Abbr) u) i H0 (CHead x0 (Bind Abst) 
x1) H6)) in (False_ind (leq g a a2) H9))))))) H5)) H4)))))))))))) (\lambda 
(c0: C).(\lambda (d: C).(\lambda (u: T).(\lambda (i: nat).(\lambda (H0: (getl 
i c0 (CHead d (Bind Abst) u))).(\lambda (a: A).(\lambda (_: (arity g d u 
(asucc g a))).(\lambda (H2: ((\forall (a2: A).((arity g d u a2) \to (leq g 
(asucc g a) a2))))).(\lambda (a2: A).(\lambda (H3: (arity g c0 (TLRef i) 
a2)).(let H4 \def (arity_gen_lref g c0 i a2 H3) in (or_ind (ex2_2 C T 
(\lambda (d0: C).(\lambda (u0: T).(getl i c0 (CHead d0 (Bind Abbr) u0)))) 
(\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 a2)))) (ex2_2 C T (\lambda 
(d0: C).(\lambda (u0: T).(getl i c0 (CHead d0 (Bind Abst) u0)))) (\lambda 
(d0: C).(\lambda (u0: T).(arity g d0 u0 (asucc g a2))))) (leq g a a2) 
(\lambda (H5: (ex2_2 C T (\lambda (d0: C).(\lambda (u0: T).(getl i c0 (CHead 
d0 (Bind Abbr) u0)))) (\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 
a2))))).(ex2_2_ind C T (\lambda (d0: C).(\lambda (u0: T).(getl i c0 (CHead d0 
(Bind Abbr) u0)))) (\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 a2))) 
(leq g a a2) (\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: (getl i c0 
(CHead x0 (Bind Abbr) x1))).(\lambda (_: (arity g x0 x1 a2)).(let H8 \def 
(eq_ind C (CHead d (Bind Abst) u) (\lambda (c1: C).(getl i c0 c1)) H0 (CHead 
x0 (Bind Abbr) x1) (getl_mono c0 (CHead d (Bind Abst) u) i H0 (CHead x0 (Bind 
Abbr) x1) H6)) in (let H9 \def (eq_ind C (CHead d (Bind Abst) u) (\lambda 
(ee: C).(match ee in C return (\lambda (_: C).Prop) with [(CSort _) 
\Rightarrow False | (CHead _ k _) \Rightarrow (match k in K return (\lambda 
(_: K).Prop) with [(Bind b) \Rightarrow (match b in B return (\lambda (_: 
B).Prop) with [Abbr \Rightarrow False | Abst \Rightarrow True | Void 
\Rightarrow False]) | (Flat _) \Rightarrow False])])) I (CHead x0 (Bind Abbr) 
x1) (getl_mono c0 (CHead d (Bind Abst) u) i H0 (CHead x0 (Bind Abbr) x1) H6)) 
in (False_ind (leq g a a2) H9))))))) H5)) (\lambda (H5: (ex2_2 C T (\lambda 
(d0: C).(\lambda (u0: T).(getl i c0 (CHead d0 (Bind Abst) u0)))) (\lambda 
(d0: C).(\lambda (u0: T).(arity g d0 u0 (asucc g a2)))))).(ex2_2_ind C T 
(\lambda (d0: C).(\lambda (u0: T).(getl i c0 (CHead d0 (Bind Abst) u0)))) 
(\lambda (d0: C).(\lambda (u0: T).(arity g d0 u0 (asucc g a2)))) (leq g a a2) 
(\lambda (x0: C).(\lambda (x1: T).(\lambda (H6: (getl i c0 (CHead x0 (Bind 
Abst) x1))).(\lambda (H7: (arity g x0 x1 (asucc g a2))).(let H8 \def (eq_ind 
C (CHead d (Bind Abst) u) (\lambda (c1: C).(getl i c0 c1)) H0 (CHead x0 (Bind 
Abst) x1) (getl_mono c0 (CHead d (Bind Abst) u) i H0 (CHead x0 (Bind Abst) 
x1) H6)) in (let H9 \def (f_equal C C (\lambda (e: C).(match e in C return 
(\lambda (_: C).C) with [(CSort _) \Rightarrow d | (CHead c1 _ _) \Rightarrow 
c1])) (CHead d (Bind Abst) u) (CHead x0 (Bind Abst) x1) (getl_mono c0 (CHead 
d (Bind Abst) u) i H0 (CHead x0 (Bind Abst) x1) H6)) in ((let H10 \def 
(f_equal C T (\lambda (e: C).(match e in C return (\lambda (_: C).T) with 
[(CSort _) \Rightarrow u | (CHead _ _ t0) \Rightarrow t0])) (CHead d (Bind 
Abst) u) (CHead x0 (Bind Abst) x1) (getl_mono c0 (CHead d (Bind Abst) u) i H0 
(CHead x0 (Bind Abst) x1) H6)) in (\lambda (H11: (eq C d x0)).(let H12 \def 
(eq_ind_r T x1 (\lambda (t0: T).(getl i c0 (CHead x0 (Bind Abst) t0))) H8 u 
H10) in (let H13 \def (eq_ind_r T x1 (\lambda (t0: T).(arity g x0 t0 (asucc g 
a2))) H7 u H10) in (let H14 \def (eq_ind_r C x0 (\lambda (c1: C).(getl i c0 
(CHead c1 (Bind Abst) u))) H12 d H11) in (let H15 \def (eq_ind_r C x0 
(\lambda (c1: C).(arity g c1 u (asucc g a2))) H13 d H11) in (asucc_inj g a a2 
(H2 (asucc g a2) H15)))))))) H9))))))) H5)) H4)))))))))))) (\lambda (b: 
B).(\lambda (H0: (not (eq B b Abst))).(\lambda (c0: C).(\lambda (u: 
T).(\lambda (a2: A).(\lambda (_: (arity g c0 u a2)).(\lambda (_: ((\forall 
(a3: A).((arity g c0 u a3) \to (leq g a2 a3))))).(\lambda (t0: T).(\lambda 
(a3: A).(\lambda (_: (arity g (CHead c0 (Bind b) u) t0 a3)).(\lambda (H4: 
((\forall (a4: A).((arity g (CHead c0 (Bind b) u) t0 a4) \to (leq g a3 
a4))))).(\lambda (a0: A).(\lambda (H5: (arity g c0 (THead (Bind b) u t0) 
a0)).(let H6 \def (arity_gen_bind b H0 g c0 u t0 a0 H5) in (ex2_ind A 
(\lambda (a4: A).(arity g c0 u a4)) (\lambda (_: A).(arity g (CHead c0 (Bind 
b) u) t0 a0)) (leq g a3 a0) (\lambda (x: A).(\lambda (_: (arity g c0 u 
x)).(\lambda (H8: (arity g (CHead c0 (Bind b) u) t0 a0)).(H4 a0 H8)))) 
H6))))))))))))))) (\lambda (c0: C).(\lambda (u: T).(\lambda (a2: A).(\lambda 
(_: (arity g c0 u (asucc g a2))).(\lambda (H1: ((\forall (a3: A).((arity g c0 
u a3) \to (leq g (asucc g a2) a3))))).(\lambda (t0: T).(\lambda (a3: 
A).(\lambda (_: (arity g (CHead c0 (Bind Abst) u) t0 a3)).(\lambda (H3: 
((\forall (a4: A).((arity g (CHead c0 (Bind Abst) u) t0 a4) \to (leq g a3 
a4))))).(\lambda (a0: A).(\lambda (H4: (arity g c0 (THead (Bind Abst) u t0) 
a0)).(let H5 \def (arity_gen_abst g c0 u t0 a0 H4) in (ex3_2_ind A A (\lambda 
(a4: A).(\lambda (a5: A).(eq A a0 (AHead a4 a5)))) (\lambda (a4: A).(\lambda 
(_: A).(arity g c0 u (asucc g a4)))) (\lambda (_: A).(\lambda (a5: A).(arity 
g (CHead c0 (Bind Abst) u) t0 a5))) (leq g (AHead a2 a3) a0) (\lambda (x0: 
A).(\lambda (x1: A).(\lambda (H6: (eq A a0 (AHead x0 x1))).(\lambda (H7: 
(arity g c0 u (asucc g x0))).(\lambda (H8: (arity g (CHead c0 (Bind Abst) u) 
t0 x1)).(eq_ind_r A (AHead x0 x1) (\lambda (a: A).(leq g (AHead a2 a3) a)) 
(leq_head g a2 x0 (asucc_inj g a2 x0 (H1 (asucc g x0) H7)) a3 x1 (H3 x1 H8)) 
a0 H6)))))) H5))))))))))))) (\lambda (c0: C).(\lambda (u: T).(\lambda (a2: 
A).(\lambda (_: (arity g c0 u a2)).(\lambda (_: ((\forall (a3: A).((arity g 
c0 u a3) \to (leq g a2 a3))))).(\lambda (t0: T).(\lambda (a3: A).(\lambda (_: 
(arity g c0 t0 (AHead a2 a3))).(\lambda (H3: ((\forall (a4: A).((arity g c0 
t0 a4) \to (leq g (AHead a2 a3) a4))))).(\lambda (a0: A).(\lambda (H4: (arity 
g c0 (THead (Flat Appl) u t0) a0)).(let H5 \def (arity_gen_appl g c0 u t0 a0 
H4) in (ex2_ind A (\lambda (a4: A).(arity g c0 u a4)) (\lambda (a4: A).(arity 
g c0 t0 (AHead a4 a0))) (leq g a3 a0) (\lambda (x: A).(\lambda (_: (arity g 
c0 u x)).(\lambda (H7: (arity g c0 t0 (AHead x a0))).(ahead_inj_snd g a2 a3 x 
a0 (H3 (AHead x a0) H7))))) H5))))))))))))) (\lambda (c0: C).(\lambda (u: 
T).(\lambda (a: A).(\lambda (_: (arity g c0 u (asucc g a))).(\lambda (_: 
((\forall (a2: A).((arity g c0 u a2) \to (leq g (asucc g a) a2))))).(\lambda 
(t0: T).(\lambda (_: (arity g c0 t0 a)).(\lambda (H3: ((\forall (a2: 
A).((arity g c0 t0 a2) \to (leq g a a2))))).(\lambda (a2: A).(\lambda (H4: 
(arity g c0 (THead (Flat Cast) u t0) a2)).(let H5 \def (arity_gen_cast g c0 u 
t0 a2 H4) in (land_ind (arity g c0 u (asucc g a2)) (arity g c0 t0 a2) (leq g 
a a2) (\lambda (_: (arity g c0 u (asucc g a2))).(\lambda (H7: (arity g c0 t0 
a2)).(H3 a2 H7))) H5)))))))))))) (\lambda (c0: C).(\lambda (t0: T).(\lambda 
(a2: A).(\lambda (_: (arity g c0 t0 a2)).(\lambda (H1: ((\forall (a3: 
A).((arity g c0 t0 a3) \to (leq g a2 a3))))).(\lambda (a3: A).(\lambda (H2: 
(leq g a2 a3)).(\lambda (a0: A).(\lambda (H3: (arity g c0 t0 a0)).(leq_trans 
g a3 a2 (leq_sym g a2 a3 H2) a0 (H1 a0 H3))))))))))) c t a1 H))))).
(* COMMENTS
Initial nodes: 2947
END *)

theorem arity_repellent:
 \forall (g: G).(\forall (c: C).(\forall (w: T).(\forall (t: T).(\forall (a1: 
A).((arity g (CHead c (Bind Abst) w) t a1) \to (\forall (a2: A).((arity g c 
(THead (Bind Abst) w t) a2) \to ((leq g a1 a2) \to (\forall (P: 
Prop).P)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (w: T).(\lambda (t: T).(\lambda (a1: 
A).(\lambda (H: (arity g (CHead c (Bind Abst) w) t a1)).(\lambda (a2: 
A).(\lambda (H0: (arity g c (THead (Bind Abst) w t) a2)).(\lambda (H1: (leq g 
a1 a2)).(\lambda (P: Prop).(let H_y \def (arity_repl g (CHead c (Bind Abst) 
w) t a1 H a2 H1) in (let H2 \def (arity_gen_abst g c w t a2 H0) in (ex3_2_ind 
A A (\lambda (a3: A).(\lambda (a4: A).(eq A a2 (AHead a3 a4)))) (\lambda (a3: 
A).(\lambda (_: A).(arity g c w (asucc g a3)))) (\lambda (_: A).(\lambda (a4: 
A).(arity g (CHead c (Bind Abst) w) t a4))) P (\lambda (x0: A).(\lambda (x1: 
A).(\lambda (H3: (eq A a2 (AHead x0 x1))).(\lambda (_: (arity g c w (asucc g 
x0))).(\lambda (H5: (arity g (CHead c (Bind Abst) w) t x1)).(let H6 \def 
(eq_ind A a2 (\lambda (a: A).(arity g (CHead c (Bind Abst) w) t a)) H_y 
(AHead x0 x1) H3) in (leq_ahead_false_2 g x1 x0 (arity_mono g (CHead c (Bind 
Abst) w) t (AHead x0 x1) H6 x1 H5) P))))))) H2)))))))))))).
(* COMMENTS
Initial nodes: 283
END *)

theorem arity_appls_cast:
 \forall (g: G).(\forall (c: C).(\forall (u: T).(\forall (t: T).(\forall (vs: 
TList).(\forall (a: A).((arity g c (THeads (Flat Appl) vs u) (asucc g a)) \to 
((arity g c (THeads (Flat Appl) vs t) a) \to (arity g c (THeads (Flat Appl) 
vs (THead (Flat Cast) u t)) a))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (u: T).(\lambda (t: T).(\lambda (vs: 
TList).(TList_ind (\lambda (t0: TList).(\forall (a: A).((arity g c (THeads 
(Flat Appl) t0 u) (asucc g a)) \to ((arity g c (THeads (Flat Appl) t0 t) a) 
\to (arity g c (THeads (Flat Appl) t0 (THead (Flat Cast) u t)) a))))) 
(\lambda (a: A).(\lambda (H: (arity g c u (asucc g a))).(\lambda (H0: (arity 
g c t a)).(arity_cast g c u a H t H0)))) (\lambda (t0: T).(\lambda (t1: 
TList).(\lambda (H: ((\forall (a: A).((arity g c (THeads (Flat Appl) t1 u) 
(asucc g a)) \to ((arity g c (THeads (Flat Appl) t1 t) a) \to (arity g c 
(THeads (Flat Appl) t1 (THead (Flat Cast) u t)) a)))))).(\lambda (a: 
A).(\lambda (H0: (arity g c (THead (Flat Appl) t0 (THeads (Flat Appl) t1 u)) 
(asucc g a))).(\lambda (H1: (arity g c (THead (Flat Appl) t0 (THeads (Flat 
Appl) t1 t)) a)).(let H2 \def (arity_gen_appl g c t0 (THeads (Flat Appl) t1 
t) a H1) in (ex2_ind A (\lambda (a1: A).(arity g c t0 a1)) (\lambda (a1: 
A).(arity g c (THeads (Flat Appl) t1 t) (AHead a1 a))) (arity g c (THead 
(Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Flat Cast) u t))) a) (\lambda 
(x: A).(\lambda (H3: (arity g c t0 x)).(\lambda (H4: (arity g c (THeads (Flat 
Appl) t1 t) (AHead x a))).(let H5 \def (arity_gen_appl g c t0 (THeads (Flat 
Appl) t1 u) (asucc g a) H0) in (ex2_ind A (\lambda (a1: A).(arity g c t0 a1)) 
(\lambda (a1: A).(arity g c (THeads (Flat Appl) t1 u) (AHead a1 (asucc g 
a)))) (arity g c (THead (Flat Appl) t0 (THeads (Flat Appl) t1 (THead (Flat 
Cast) u t))) a) (\lambda (x0: A).(\lambda (H6: (arity g c t0 x0)).(\lambda 
(H7: (arity g c (THeads (Flat Appl) t1 u) (AHead x0 (asucc g 
a)))).(arity_appl g c t0 x H3 (THeads (Flat Appl) t1 (THead (Flat Cast) u t)) 
a (H (AHead x a) (arity_repl g c (THeads (Flat Appl) t1 u) (AHead x (asucc g 
a)) (arity_repl g c (THeads (Flat Appl) t1 u) (AHead x0 (asucc g a)) H7 
(AHead x (asucc g a)) (leq_head g x0 x (arity_mono g c t0 x0 H6 x H3) (asucc 
g a) (asucc g a) (leq_refl g (asucc g a)))) (asucc g (AHead x a)) (leq_refl g 
(asucc g (AHead x a)))) H4))))) H5))))) H2)))))))) vs))))).
(* COMMENTS
Initial nodes: 707
END *)

theorem arity_appls_abbr:
 \forall (g: G).(\forall (c: C).(\forall (d: C).(\forall (v: T).(\forall (i: 
nat).((getl i c (CHead d (Bind Abbr) v)) \to (\forall (vs: TList).(\forall 
(a: A).((arity g c (THeads (Flat Appl) vs (lift (S i) O v)) a) \to (arity g c 
(THeads (Flat Appl) vs (TLRef i)) a)))))))))
\def
 \lambda (g: G).(\lambda (c: C).(\lambda (d: C).(\lambda (v: T).(\lambda (i: 
nat).(\lambda (H: (getl i c (CHead d (Bind Abbr) v))).(\lambda (vs: 
TList).(TList_ind (\lambda (t: TList).(\forall (a: A).((arity g c (THeads 
(Flat Appl) t (lift (S i) O v)) a) \to (arity g c (THeads (Flat Appl) t 
(TLRef i)) a)))) (\lambda (a: A).(\lambda (H0: (arity g c (lift (S i) O v) 
a)).(arity_abbr g c d v i H a (arity_gen_lift g c v a (S i) O H0 d (getl_drop 
Abbr c d v i H))))) (\lambda (t: T).(\lambda (t0: TList).(\lambda (H0: 
((\forall (a: A).((arity g c (THeads (Flat Appl) t0 (lift (S i) O v)) a) \to 
(arity g c (THeads (Flat Appl) t0 (TLRef i)) a))))).(\lambda (a: A).(\lambda 
(H1: (arity g c (THead (Flat Appl) t (THeads (Flat Appl) t0 (lift (S i) O 
v))) a)).(let H2 \def (arity_gen_appl g c t (THeads (Flat Appl) t0 (lift (S 
i) O v)) a H1) in (ex2_ind A (\lambda (a1: A).(arity g c t a1)) (\lambda (a1: 
A).(arity g c (THeads (Flat Appl) t0 (lift (S i) O v)) (AHead a1 a))) (arity 
g c (THead (Flat Appl) t (THeads (Flat Appl) t0 (TLRef i))) a) (\lambda (x: 
A).(\lambda (H3: (arity g c t x)).(\lambda (H4: (arity g c (THeads (Flat 
Appl) t0 (lift (S i) O v)) (AHead x a))).(arity_appl g c t x H3 (THeads (Flat 
Appl) t0 (TLRef i)) a (H0 (AHead x a) H4))))) H2))))))) vs))))))).
(* COMMENTS
Initial nodes: 425
END *)

theorem arity_appls_bind:
 \forall (g: G).(\forall (b: B).((not (eq B b Abst)) \to (\forall (c: 
C).(\forall (v: T).(\forall (a1: A).((arity g c v a1) \to (\forall (t: 
T).(\forall (vs: TList).(\forall (a2: A).((arity g (CHead c (Bind b) v) 
(THeads (Flat Appl) (lifts (S O) O vs) t) a2) \to (arity g c (THeads (Flat 
Appl) vs (THead (Bind b) v t)) a2)))))))))))
\def
 \lambda (g: G).(\lambda (b: B).(\lambda (H: (not (eq B b Abst))).(\lambda 
(c: C).(\lambda (v: T).(\lambda (a1: A).(\lambda (H0: (arity g c v 
a1)).(\lambda (t: T).(\lambda (vs: TList).(TList_ind (\lambda (t0: 
TList).(\forall (a2: A).((arity g (CHead c (Bind b) v) (THeads (Flat Appl) 
(lifts (S O) O t0) t) a2) \to (arity g c (THeads (Flat Appl) t0 (THead (Bind 
b) v t)) a2)))) (\lambda (a2: A).(\lambda (H1: (arity g (CHead c (Bind b) v) 
t a2)).(arity_bind g b H c v a1 H0 t a2 H1))) (\lambda (t0: T).(\lambda (t1: 
TList).(\lambda (H1: ((\forall (a2: A).((arity g (CHead c (Bind b) v) (THeads 
(Flat Appl) (lifts (S O) O t1) t) a2) \to (arity g c (THeads (Flat Appl) t1 
(THead (Bind b) v t)) a2))))).(\lambda (a2: A).(\lambda (H2: (arity g (CHead 
c (Bind b) v) (THead (Flat Appl) (lift (S O) O t0) (THeads (Flat Appl) (lifts 
(S O) O t1) t)) a2)).(let H3 \def (arity_gen_appl g (CHead c (Bind b) v) 
(lift (S O) O t0) (THeads (Flat Appl) (lifts (S O) O t1) t) a2 H2) in 
(ex2_ind A (\lambda (a3: A).(arity g (CHead c (Bind b) v) (lift (S O) O t0) 
a3)) (\lambda (a3: A).(arity g (CHead c (Bind b) v) (THeads (Flat Appl) 
(lifts (S O) O t1) t) (AHead a3 a2))) (arity g c (THead (Flat Appl) t0 
(THeads (Flat Appl) t1 (THead (Bind b) v t))) a2) (\lambda (x: A).(\lambda 
(H4: (arity g (CHead c (Bind b) v) (lift (S O) O t0) x)).(\lambda (H5: (arity 
g (CHead c (Bind b) v) (THeads (Flat Appl) (lifts (S O) O t1) t) (AHead x 
a2))).(arity_appl g c t0 x (arity_gen_lift g (CHead c (Bind b) v) t0 x (S O) 
O H4 c (drop_drop (Bind b) O c c (drop_refl c) v)) (THeads (Flat Appl) t1 
(THead (Bind b) v t)) a2 (H1 (AHead x a2) H5))))) H3))))))) vs))))))))).
(* COMMENTS
Initial nodes: 567
END *)

