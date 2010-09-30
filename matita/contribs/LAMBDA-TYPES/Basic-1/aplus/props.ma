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

include "Basic-1/aplus/defs.ma".

include "Basic-1/next_plus/props.ma".

theorem aplus_reg_r:
 \forall (g: G).(\forall (a1: A).(\forall (a2: A).(\forall (h1: nat).(\forall 
(h2: nat).((eq A (aplus g a1 h1) (aplus g a2 h2)) \to (\forall (h: nat).(eq A 
(aplus g a1 (plus h h1)) (aplus g a2 (plus h h2)))))))))
\def
 \lambda (g: G).(\lambda (a1: A).(\lambda (a2: A).(\lambda (h1: nat).(\lambda 
(h2: nat).(\lambda (H: (eq A (aplus g a1 h1) (aplus g a2 h2))).(\lambda (h: 
nat).(nat_ind (\lambda (n: nat).(eq A (aplus g a1 (plus n h1)) (aplus g a2 
(plus n h2)))) H (\lambda (n: nat).(\lambda (H0: (eq A (aplus g a1 (plus n 
h1)) (aplus g a2 (plus n h2)))).(f_equal2 G A A asucc g g (aplus g a1 (plus n 
h1)) (aplus g a2 (plus n h2)) (refl_equal G g) H0))) h))))))).
(* COMMENTS
Initial nodes: 143
END *)

theorem aplus_assoc:
 \forall (g: G).(\forall (a: A).(\forall (h1: nat).(\forall (h2: nat).(eq A 
(aplus g (aplus g a h1) h2) (aplus g a (plus h1 h2))))))
\def
 \lambda (g: G).(\lambda (a: A).(\lambda (h1: nat).(nat_ind (\lambda (n: 
nat).(\forall (h2: nat).(eq A (aplus g (aplus g a n) h2) (aplus g a (plus n 
h2))))) (\lambda (h2: nat).(refl_equal A (aplus g a h2))) (\lambda (n: 
nat).(\lambda (_: ((\forall (h2: nat).(eq A (aplus g (aplus g a n) h2) (aplus 
g a (plus n h2)))))).(\lambda (h2: nat).(nat_ind (\lambda (n0: nat).(eq A 
(aplus g (asucc g (aplus g a n)) n0) (asucc g (aplus g a (plus n n0))))) 
(eq_ind nat n (\lambda (n0: nat).(eq A (asucc g (aplus g a n)) (asucc g 
(aplus g a n0)))) (refl_equal A (asucc g (aplus g a n))) (plus n O) (plus_n_O 
n)) (\lambda (n0: nat).(\lambda (H0: (eq A (aplus g (asucc g (aplus g a n)) 
n0) (asucc g (aplus g a (plus n n0))))).(eq_ind nat (S (plus n n0)) (\lambda 
(n1: nat).(eq A (asucc g (aplus g (asucc g (aplus g a n)) n0)) (asucc g 
(aplus g a n1)))) (f_equal2 G A A asucc g g (aplus g (asucc g (aplus g a n)) 
n0) (asucc g (aplus g a (plus n n0))) (refl_equal G g) H0) (plus n (S n0)) 
(plus_n_Sm n n0)))) h2)))) h1))).
(* COMMENTS
Initial nodes: 361
END *)

theorem aplus_asucc:
 \forall (g: G).(\forall (h: nat).(\forall (a: A).(eq A (aplus g (asucc g a) 
h) (asucc g (aplus g a h)))))
\def
 \lambda (g: G).(\lambda (h: nat).(\lambda (a: A).(eq_ind_r A (aplus g a 
(plus (S O) h)) (\lambda (a0: A).(eq A a0 (asucc g (aplus g a h)))) 
(refl_equal A (asucc g (aplus g a h))) (aplus g (aplus g a (S O)) h) 
(aplus_assoc g a (S O) h)))).
(* COMMENTS
Initial nodes: 87
END *)

theorem aplus_sort_O_S_simpl:
 \forall (g: G).(\forall (n: nat).(\forall (k: nat).(eq A (aplus g (ASort O 
n) (S k)) (aplus g (ASort O (next g n)) k))))
\def
 \lambda (g: G).(\lambda (n: nat).(\lambda (k: nat).(eq_ind A (aplus g (asucc 
g (ASort O n)) k) (\lambda (a: A).(eq A a (aplus g (ASort O (next g n)) k))) 
(refl_equal A (aplus g (ASort O (next g n)) k)) (asucc g (aplus g (ASort O n) 
k)) (aplus_asucc g k (ASort O n))))).
(* COMMENTS
Initial nodes: 97
END *)

theorem aplus_sort_S_S_simpl:
 \forall (g: G).(\forall (n: nat).(\forall (h: nat).(\forall (k: nat).(eq A 
(aplus g (ASort (S h) n) (S k)) (aplus g (ASort h n) k)))))
\def
 \lambda (g: G).(\lambda (n: nat).(\lambda (h: nat).(\lambda (k: nat).(eq_ind 
A (aplus g (asucc g (ASort (S h) n)) k) (\lambda (a: A).(eq A a (aplus g 
(ASort h n) k))) (refl_equal A (aplus g (ASort h n) k)) (asucc g (aplus g 
(ASort (S h) n) k)) (aplus_asucc g k (ASort (S h) n)))))).
(* COMMENTS
Initial nodes: 97
END *)

theorem aplus_asort_O_simpl:
 \forall (g: G).(\forall (h: nat).(\forall (n: nat).(eq A (aplus g (ASort O 
n) h) (ASort O (next_plus g n h)))))
\def
 \lambda (g: G).(\lambda (h: nat).(nat_ind (\lambda (n: nat).(\forall (n0: 
nat).(eq A (aplus g (ASort O n0) n) (ASort O (next_plus g n0 n))))) (\lambda 
(n: nat).(refl_equal A (ASort O n))) (\lambda (n: nat).(\lambda (H: ((\forall 
(n0: nat).(eq A (aplus g (ASort O n0) n) (ASort O (next_plus g n0 
n)))))).(\lambda (n0: nat).(eq_ind A (aplus g (asucc g (ASort O n0)) n) 
(\lambda (a: A).(eq A a (ASort O (next g (next_plus g n0 n))))) (eq_ind nat 
(next_plus g (next g n0) n) (\lambda (n1: nat).(eq A (aplus g (ASort O (next 
g n0)) n) (ASort O n1))) (H (next g n0)) (next g (next_plus g n0 n)) 
(next_plus_next g n0 n)) (asucc g (aplus g (ASort O n0) n)) (aplus_asucc g n 
(ASort O n0)))))) h)).
(* COMMENTS
Initial nodes: 229
END *)

theorem aplus_asort_le_simpl:
 \forall (g: G).(\forall (h: nat).(\forall (k: nat).(\forall (n: nat).((le h 
k) \to (eq A (aplus g (ASort k n) h) (ASort (minus k h) n))))))
\def
 \lambda (g: G).(\lambda (h: nat).(nat_ind (\lambda (n: nat).(\forall (k: 
nat).(\forall (n0: nat).((le n k) \to (eq A (aplus g (ASort k n0) n) (ASort 
(minus k n) n0)))))) (\lambda (k: nat).(\lambda (n: nat).(\lambda (_: (le O 
k)).(eq_ind nat k (\lambda (n0: nat).(eq A (ASort k n) (ASort n0 n))) 
(refl_equal A (ASort k n)) (minus k O) (minus_n_O k))))) (\lambda (h0: 
nat).(\lambda (H: ((\forall (k: nat).(\forall (n: nat).((le h0 k) \to (eq A 
(aplus g (ASort k n) h0) (ASort (minus k h0) n))))))).(\lambda (k: 
nat).(nat_ind (\lambda (n: nat).(\forall (n0: nat).((le (S h0) n) \to (eq A 
(asucc g (aplus g (ASort n n0) h0)) (ASort (minus n (S h0)) n0))))) (\lambda 
(n: nat).(\lambda (H0: (le (S h0) O)).(ex2_ind nat (\lambda (n0: nat).(eq nat 
O (S n0))) (\lambda (n0: nat).(le h0 n0)) (eq A (asucc g (aplus g (ASort O n) 
h0)) (ASort (minus O (S h0)) n)) (\lambda (x: nat).(\lambda (H1: (eq nat O (S 
x))).(\lambda (_: (le h0 x)).(let H3 \def (eq_ind nat O (\lambda (ee: 
nat).(match ee in nat return (\lambda (_: nat).Prop) with [O \Rightarrow True 
| (S _) \Rightarrow False])) I (S x) H1) in (False_ind (eq A (asucc g (aplus 
g (ASort O n) h0)) (ASort (minus O (S h0)) n)) H3))))) (le_gen_S h0 O H0)))) 
(\lambda (n: nat).(\lambda (_: ((\forall (n0: nat).((le (S h0) n) \to (eq A 
(asucc g (aplus g (ASort n n0) h0)) (ASort (minus n (S h0)) n0)))))).(\lambda 
(n0: nat).(\lambda (H1: (le (S h0) (S n))).(eq_ind A (aplus g (asucc g (ASort 
(S n) n0)) h0) (\lambda (a: A).(eq A a (ASort (minus (S n) (S h0)) n0))) (H n 
n0 (le_S_n h0 n H1)) (asucc g (aplus g (ASort (S n) n0) h0)) (aplus_asucc g 
h0 (ASort (S n) n0))))))) k)))) h)).
(* COMMENTS
Initial nodes: 484
END *)

theorem aplus_asort_simpl:
 \forall (g: G).(\forall (h: nat).(\forall (k: nat).(\forall (n: nat).(eq A 
(aplus g (ASort k n) h) (ASort (minus k h) (next_plus g n (minus h k)))))))
\def
 \lambda (g: G).(\lambda (h: nat).(\lambda (k: nat).(\lambda (n: 
nat).(lt_le_e k h (eq A (aplus g (ASort k n) h) (ASort (minus k h) (next_plus 
g n (minus h k)))) (\lambda (H: (lt k h)).(eq_ind_r nat (plus k (minus h k)) 
(\lambda (n0: nat).(eq A (aplus g (ASort k n) n0) (ASort (minus k h) 
(next_plus g n (minus h k))))) (eq_ind A (aplus g (aplus g (ASort k n) k) 
(minus h k)) (\lambda (a: A).(eq A a (ASort (minus k h) (next_plus g n (minus 
h k))))) (eq_ind_r A (ASort (minus k k) n) (\lambda (a: A).(eq A (aplus g a 
(minus h k)) (ASort (minus k h) (next_plus g n (minus h k))))) (eq_ind nat O 
(\lambda (n0: nat).(eq A (aplus g (ASort n0 n) (minus h k)) (ASort (minus k 
h) (next_plus g n (minus h k))))) (eq_ind_r nat O (\lambda (n0: nat).(eq A 
(aplus g (ASort O n) (minus h k)) (ASort n0 (next_plus g n (minus h k))))) 
(aplus_asort_O_simpl g (minus h k) n) (minus k h) (O_minus k h (le_S_n k h 
(le_S (S k) h H)))) (minus k k) (minus_n_n k)) (aplus g (ASort k n) k) 
(aplus_asort_le_simpl g k k n (le_n k))) (aplus g (ASort k n) (plus k (minus 
h k))) (aplus_assoc g (ASort k n) k (minus h k))) h (le_plus_minus k h 
(le_S_n k h (le_S (S k) h H))))) (\lambda (H: (le h k)).(eq_ind_r A (ASort 
(minus k h) n) (\lambda (a: A).(eq A a (ASort (minus k h) (next_plus g n 
(minus h k))))) (eq_ind_r nat O (\lambda (n0: nat).(eq A (ASort (minus k h) 
n) (ASort (minus k h) (next_plus g n n0)))) (refl_equal A (ASort (minus k h) 
(next_plus g n O))) (minus h k) (O_minus h k H)) (aplus g (ASort k n) h) 
(aplus_asort_le_simpl g h k n H))))))).
(* COMMENTS
Initial nodes: 587
END *)

theorem aplus_ahead_simpl:
 \forall (g: G).(\forall (h: nat).(\forall (a1: A).(\forall (a2: A).(eq A 
(aplus g (AHead a1 a2) h) (AHead a1 (aplus g a2 h))))))
\def
 \lambda (g: G).(\lambda (h: nat).(nat_ind (\lambda (n: nat).(\forall (a1: 
A).(\forall (a2: A).(eq A (aplus g (AHead a1 a2) n) (AHead a1 (aplus g a2 
n)))))) (\lambda (a1: A).(\lambda (a2: A).(refl_equal A (AHead a1 a2)))) 
(\lambda (n: nat).(\lambda (H: ((\forall (a1: A).(\forall (a2: A).(eq A 
(aplus g (AHead a1 a2) n) (AHead a1 (aplus g a2 n))))))).(\lambda (a1: 
A).(\lambda (a2: A).(eq_ind A (aplus g (asucc g (AHead a1 a2)) n) (\lambda 
(a: A).(eq A a (AHead a1 (asucc g (aplus g a2 n))))) (eq_ind A (aplus g 
(asucc g a2) n) (\lambda (a: A).(eq A (aplus g (asucc g (AHead a1 a2)) n) 
(AHead a1 a))) (H a1 (asucc g a2)) (asucc g (aplus g a2 n)) (aplus_asucc g n 
a2)) (asucc g (aplus g (AHead a1 a2) n)) (aplus_asucc g n (AHead a1 a2))))))) 
h)).
(* COMMENTS
Initial nodes: 239
END *)

theorem aplus_asucc_false:
 \forall (g: G).(\forall (a: A).(\forall (h: nat).((eq A (aplus g (asucc g a) 
h) a) \to (\forall (P: Prop).P))))
\def
 \lambda (g: G).(\lambda (a: A).(A_ind (\lambda (a0: A).(\forall (h: 
nat).((eq A (aplus g (asucc g a0) h) a0) \to (\forall (P: Prop).P)))) 
(\lambda (n: nat).(\lambda (n0: nat).(\lambda (h: nat).(\lambda (H: (eq A 
(aplus g (match n with [O \Rightarrow (ASort O (next g n0)) | (S h0) 
\Rightarrow (ASort h0 n0)]) h) (ASort n n0))).(\lambda (P: Prop).(nat_ind 
(\lambda (n1: nat).((eq A (aplus g (match n1 with [O \Rightarrow (ASort O 
(next g n0)) | (S h0) \Rightarrow (ASort h0 n0)]) h) (ASort n1 n0)) \to P)) 
(\lambda (H0: (eq A (aplus g (ASort O (next g n0)) h) (ASort O n0))).(let H1 
\def (eq_ind A (aplus g (ASort O (next g n0)) h) (\lambda (a0: A).(eq A a0 
(ASort O n0))) H0 (ASort (minus O h) (next_plus g (next g n0) (minus h O))) 
(aplus_asort_simpl g h O (next g n0))) in (let H2 \def (f_equal A nat 
(\lambda (e: A).(match e in A return (\lambda (_: A).nat) with [(ASort _ n1) 
\Rightarrow n1 | (AHead _ _) \Rightarrow ((let rec next_plus (g0: G) (n1: 
nat) (i: nat) on i: nat \def (match i with [O \Rightarrow n1 | (S i0) 
\Rightarrow (next g0 (next_plus g0 n1 i0))]) in next_plus) g (next g n0) 
(minus h O))])) (ASort (minus O h) (next_plus g (next g n0) (minus h O))) 
(ASort O n0) H1) in (let H3 \def (eq_ind_r nat (minus h O) (\lambda (n1: 
nat).(eq nat (next_plus g (next g n0) n1) n0)) H2 h (minus_n_O h)) in 
(le_lt_false (next_plus g (next g n0) h) n0 (eq_ind nat (next_plus g (next g 
n0) h) (\lambda (n1: nat).(le (next_plus g (next g n0) h) n1)) (le_n 
(next_plus g (next g n0) h)) n0 H3) (next_plus_lt g h n0) P))))) (\lambda 
(n1: nat).(\lambda (_: (((eq A (aplus g (match n1 with [O \Rightarrow (ASort 
O (next g n0)) | (S h0) \Rightarrow (ASort h0 n0)]) h) (ASort n1 n0)) \to 
P))).(\lambda (H0: (eq A (aplus g (ASort n1 n0) h) (ASort (S n1) n0))).(let 
H1 \def (eq_ind A (aplus g (ASort n1 n0) h) (\lambda (a0: A).(eq A a0 (ASort 
(S n1) n0))) H0 (ASort (minus n1 h) (next_plus g n0 (minus h n1))) 
(aplus_asort_simpl g h n1 n0)) in (let H2 \def (f_equal A nat (\lambda (e: 
A).(match e in A return (\lambda (_: A).nat) with [(ASort n2 _) \Rightarrow 
n2 | (AHead _ _) \Rightarrow ((let rec minus (n2: nat) on n2: (nat \to nat) 
\def (\lambda (m: nat).(match n2 with [O \Rightarrow O | (S k) \Rightarrow 
(match m with [O \Rightarrow (S k) | (S l) \Rightarrow (minus k l)])])) in 
minus) n1 h)])) (ASort (minus n1 h) (next_plus g n0 (minus h n1))) (ASort (S 
n1) n0) H1) in ((let H3 \def (f_equal A nat (\lambda (e: A).(match e in A 
return (\lambda (_: A).nat) with [(ASort _ n2) \Rightarrow n2 | (AHead _ _) 
\Rightarrow ((let rec next_plus (g0: G) (n2: nat) (i: nat) on i: nat \def 
(match i with [O \Rightarrow n2 | (S i0) \Rightarrow (next g0 (next_plus g0 
n2 i0))]) in next_plus) g n0 (minus h n1))])) (ASort (minus n1 h) (next_plus 
g n0 (minus h n1))) (ASort (S n1) n0) H1) in (\lambda (H4: (eq nat (minus n1 
h) (S n1))).(le_Sx_x n1 (eq_ind nat (minus n1 h) (\lambda (n2: nat).(le n2 
n1)) (minus_le n1 h) (S n1) H4) P))) H2)))))) n H)))))) (\lambda (a0: 
A).(\lambda (_: ((\forall (h: nat).((eq A (aplus g (asucc g a0) h) a0) \to 
(\forall (P: Prop).P))))).(\lambda (a1: A).(\lambda (H0: ((\forall (h: 
nat).((eq A (aplus g (asucc g a1) h) a1) \to (\forall (P: 
Prop).P))))).(\lambda (h: nat).(\lambda (H1: (eq A (aplus g (AHead a0 (asucc 
g a1)) h) (AHead a0 a1))).(\lambda (P: Prop).(let H2 \def (eq_ind A (aplus g 
(AHead a0 (asucc g a1)) h) (\lambda (a2: A).(eq A a2 (AHead a0 a1))) H1 
(AHead a0 (aplus g (asucc g a1) h)) (aplus_ahead_simpl g h a0 (asucc g a1))) 
in (let H3 \def (f_equal A A (\lambda (e: A).(match e in A return (\lambda 
(_: A).A) with [(ASort _ _) \Rightarrow ((let rec aplus (g0: G) (a2: A) (n: 
nat) on n: A \def (match n with [O \Rightarrow a2 | (S n0) \Rightarrow (asucc 
g0 (aplus g0 a2 n0))]) in aplus) g (asucc g a1) h) | (AHead _ a2) \Rightarrow 
a2])) (AHead a0 (aplus g (asucc g a1) h)) (AHead a0 a1) H2) in (H0 h H3 
P)))))))))) a)).
(* COMMENTS
Initial nodes: 977
END *)

theorem aplus_inj:
 \forall (g: G).(\forall (h1: nat).(\forall (h2: nat).(\forall (a: A).((eq A 
(aplus g a h1) (aplus g a h2)) \to (eq nat h1 h2)))))
\def
 \lambda (g: G).(\lambda (h1: nat).(nat_ind (\lambda (n: nat).(\forall (h2: 
nat).(\forall (a: A).((eq A (aplus g a n) (aplus g a h2)) \to (eq nat n 
h2))))) (\lambda (h2: nat).(nat_ind (\lambda (n: nat).(\forall (a: A).((eq A 
(aplus g a O) (aplus g a n)) \to (eq nat O n)))) (\lambda (a: A).(\lambda (_: 
(eq A a a)).(refl_equal nat O))) (\lambda (n: nat).(\lambda (_: ((\forall (a: 
A).((eq A a (aplus g a n)) \to (eq nat O n))))).(\lambda (a: A).(\lambda (H0: 
(eq A a (asucc g (aplus g a n)))).(let H1 \def (eq_ind_r A (asucc g (aplus g 
a n)) (\lambda (a0: A).(eq A a a0)) H0 (aplus g (asucc g a) n) (aplus_asucc g 
n a)) in (aplus_asucc_false g a n (sym_eq A a (aplus g (asucc g a) n) H1) (eq 
nat O (S n)))))))) h2)) (\lambda (n: nat).(\lambda (H: ((\forall (h2: 
nat).(\forall (a: A).((eq A (aplus g a n) (aplus g a h2)) \to (eq nat n 
h2)))))).(\lambda (h2: nat).(nat_ind (\lambda (n0: nat).(\forall (a: A).((eq 
A (aplus g a (S n)) (aplus g a n0)) \to (eq nat (S n) n0)))) (\lambda (a: 
A).(\lambda (H0: (eq A (asucc g (aplus g a n)) a)).(let H1 \def (eq_ind_r A 
(asucc g (aplus g a n)) (\lambda (a0: A).(eq A a0 a)) H0 (aplus g (asucc g a) 
n) (aplus_asucc g n a)) in (aplus_asucc_false g a n H1 (eq nat (S n) O))))) 
(\lambda (n0: nat).(\lambda (_: ((\forall (a: A).((eq A (asucc g (aplus g a 
n)) (aplus g a n0)) \to (eq nat (S n) n0))))).(\lambda (a: A).(\lambda (H1: 
(eq A (asucc g (aplus g a n)) (asucc g (aplus g a n0)))).(let H2 \def 
(eq_ind_r A (asucc g (aplus g a n)) (\lambda (a0: A).(eq A a0 (asucc g (aplus 
g a n0)))) H1 (aplus g (asucc g a) n) (aplus_asucc g n a)) in (let H3 \def 
(eq_ind_r A (asucc g (aplus g a n0)) (\lambda (a0: A).(eq A (aplus g (asucc g 
a) n) a0)) H2 (aplus g (asucc g a) n0) (aplus_asucc g n0 a)) in (f_equal nat 
nat S n n0 (H n0 (asucc g a) H3)))))))) h2)))) h1)).
(* COMMENTS
Initial nodes: 599
END *)

