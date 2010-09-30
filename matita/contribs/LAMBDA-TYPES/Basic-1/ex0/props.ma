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

include "Basic-1/ex0/defs.ma".

include "Basic-1/leq/defs.ma".

include "Basic-1/aplus/props.ma".

theorem aplus_gz_le:
 \forall (k: nat).(\forall (h: nat).(\forall (n: nat).((le h k) \to (eq A 
(aplus gz (ASort h n) k) (ASort O (plus (minus k h) n))))))
\def
 \lambda (k: nat).(nat_ind (\lambda (n: nat).(\forall (h: nat).(\forall (n0: 
nat).((le h n) \to (eq A (aplus gz (ASort h n0) n) (ASort O (plus (minus n h) 
n0))))))) (\lambda (h: nat).(\lambda (n: nat).(\lambda (H: (le h O)).(let H_y 
\def (le_n_O_eq h H) in (eq_ind nat O (\lambda (n0: nat).(eq A (ASort n0 n) 
(ASort O n))) (refl_equal A (ASort O n)) h H_y))))) (\lambda (k0: 
nat).(\lambda (IH: ((\forall (h: nat).(\forall (n: nat).((le h k0) \to (eq A 
(aplus gz (ASort h n) k0) (ASort O (plus (minus k0 h) n)))))))).(\lambda (h: 
nat).(nat_ind (\lambda (n: nat).(\forall (n0: nat).((le n (S k0)) \to (eq A 
(asucc gz (aplus gz (ASort n n0) k0)) (ASort O (plus (match n with [O 
\Rightarrow (S k0) | (S l) \Rightarrow (minus k0 l)]) n0)))))) (\lambda (n: 
nat).(\lambda (_: (le O (S k0))).(eq_ind A (aplus gz (asucc gz (ASort O n)) 
k0) (\lambda (a: A).(eq A a (ASort O (S (plus k0 n))))) (eq_ind_r A (ASort O 
(plus (minus k0 O) (S n))) (\lambda (a: A).(eq A a (ASort O (S (plus k0 
n))))) (eq_ind nat k0 (\lambda (n0: nat).(eq A (ASort O (plus n0 (S n))) 
(ASort O (S (plus k0 n))))) (eq_ind nat (S (plus k0 n)) (\lambda (n0: 
nat).(eq A (ASort O n0) (ASort O (S (plus k0 n))))) (refl_equal A (ASort O (S 
(plus k0 n)))) (plus k0 (S n)) (plus_n_Sm k0 n)) (minus k0 O) (minus_n_O k0)) 
(aplus gz (ASort O (S n)) k0) (IH O (S n) (le_O_n k0))) (asucc gz (aplus gz 
(ASort O n) k0)) (aplus_asucc gz k0 (ASort O n))))) (\lambda (n: 
nat).(\lambda (_: ((\forall (n0: nat).((le n (S k0)) \to (eq A (asucc gz 
(aplus gz (ASort n n0) k0)) (ASort O (plus (match n with [O \Rightarrow (S 
k0) | (S l) \Rightarrow (minus k0 l)]) n0))))))).(\lambda (n0: nat).(\lambda 
(H0: (le (S n) (S k0))).(let H_y \def (le_S_n n k0 H0) in (eq_ind A (aplus gz 
(ASort n n0) k0) (\lambda (a: A).(eq A (asucc gz (aplus gz (ASort (S n) n0) 
k0)) a)) (eq_ind A (aplus gz (asucc gz (ASort (S n) n0)) k0) (\lambda (a: 
A).(eq A a (aplus gz (ASort n n0) k0))) (refl_equal A (aplus gz (ASort n n0) 
k0)) (asucc gz (aplus gz (ASort (S n) n0) k0)) (aplus_asucc gz k0 (ASort (S 
n) n0))) (ASort O (plus (minus k0 n) n0)) (IH n n0 H_y))))))) h)))) k).
(* COMMENTS
Initial nodes: 683
END *)

theorem aplus_gz_ge:
 \forall (n: nat).(\forall (k: nat).(\forall (h: nat).((le k h) \to (eq A 
(aplus gz (ASort h n) k) (ASort (minus h k) n)))))
\def
 \lambda (n: nat).(\lambda (k: nat).(nat_ind (\lambda (n0: nat).(\forall (h: 
nat).((le n0 h) \to (eq A (aplus gz (ASort h n) n0) (ASort (minus h n0) 
n))))) (\lambda (h: nat).(\lambda (_: (le O h)).(eq_ind nat h (\lambda (n0: 
nat).(eq A (ASort h n) (ASort n0 n))) (refl_equal A (ASort h n)) (minus h O) 
(minus_n_O h)))) (\lambda (k0: nat).(\lambda (IH: ((\forall (h: nat).((le k0 
h) \to (eq A (aplus gz (ASort h n) k0) (ASort (minus h k0) n)))))).(\lambda 
(h: nat).(nat_ind (\lambda (n0: nat).((le (S k0) n0) \to (eq A (asucc gz 
(aplus gz (ASort n0 n) k0)) (ASort (minus n0 (S k0)) n)))) (\lambda (H: (le 
(S k0) O)).(ex2_ind nat (\lambda (n0: nat).(eq nat O (S n0))) (\lambda (n0: 
nat).(le k0 n0)) (eq A (asucc gz (aplus gz (ASort O n) k0)) (ASort O n)) 
(\lambda (x: nat).(\lambda (H0: (eq nat O (S x))).(\lambda (_: (le k0 
x)).(let H2 \def (eq_ind nat O (\lambda (ee: nat).(match ee in nat return 
(\lambda (_: nat).Prop) with [O \Rightarrow True | (S _) \Rightarrow False])) 
I (S x) H0) in (False_ind (eq A (asucc gz (aplus gz (ASort O n) k0)) (ASort O 
n)) H2))))) (le_gen_S k0 O H))) (\lambda (n0: nat).(\lambda (_: (((le (S k0) 
n0) \to (eq A (asucc gz (aplus gz (ASort n0 n) k0)) (ASort (minus n0 (S k0)) 
n))))).(\lambda (H0: (le (S k0) (S n0))).(let H_y \def (le_S_n k0 n0 H0) in 
(eq_ind A (aplus gz (ASort n0 n) k0) (\lambda (a: A).(eq A (asucc gz (aplus 
gz (ASort (S n0) n) k0)) a)) (eq_ind A (aplus gz (asucc gz (ASort (S n0) n)) 
k0) (\lambda (a: A).(eq A a (aplus gz (ASort n0 n) k0))) (refl_equal A (aplus 
gz (ASort n0 n) k0)) (asucc gz (aplus gz (ASort (S n0) n) k0)) (aplus_asucc 
gz k0 (ASort (S n0) n))) (ASort (minus n0 k0) n) (IH n0 H_y)))))) h)))) k)).
(* COMMENTS
Initial nodes: 524
END *)

theorem next_plus_gz:
 \forall (n: nat).(\forall (h: nat).(eq nat (next_plus gz n h) (plus h n)))
\def
 \lambda (n: nat).(\lambda (h: nat).(nat_ind (\lambda (n0: nat).(eq nat 
(next_plus gz n n0) (plus n0 n))) (refl_equal nat n) (\lambda (n0: 
nat).(\lambda (H: (eq nat (next_plus gz n n0) (plus n0 n))).(f_equal nat nat 
S (next_plus gz n n0) (plus n0 n) H))) h)).
(* COMMENTS
Initial nodes: 77
END *)

theorem leqz_leq:
 \forall (a1: A).(\forall (a2: A).((leq gz a1 a2) \to (leqz a1 a2)))
\def
 \lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leq gz a1 a2)).(leq_ind gz 
(\lambda (a: A).(\lambda (a0: A).(leqz a a0))) (\lambda (h1: nat).(\lambda 
(h2: nat).(\lambda (n1: nat).(\lambda (n2: nat).(\lambda (k: nat).(\lambda 
(H0: (eq A (aplus gz (ASort h1 n1) k) (aplus gz (ASort h2 n2) k))).(lt_le_e k 
h1 (leqz (ASort h1 n1) (ASort h2 n2)) (\lambda (H1: (lt k h1)).(lt_le_e k h2 
(leqz (ASort h1 n1) (ASort h2 n2)) (\lambda (H2: (lt k h2)).(let H3 \def 
(eq_ind A (aplus gz (ASort h1 n1) k) (\lambda (a: A).(eq A a (aplus gz (ASort 
h2 n2) k))) H0 (ASort (minus h1 k) n1) (aplus_gz_ge n1 k h1 (le_S_n k h1 
(le_S (S k) h1 H1)))) in (let H4 \def (eq_ind A (aplus gz (ASort h2 n2) k) 
(\lambda (a: A).(eq A (ASort (minus h1 k) n1) a)) H3 (ASort (minus h2 k) n2) 
(aplus_gz_ge n2 k h2 (le_S_n k h2 (le_S (S k) h2 H2)))) in (let H5 \def 
(f_equal A nat (\lambda (e: A).(match e in A return (\lambda (_: A).nat) with 
[(ASort n _) \Rightarrow n | (AHead _ _) \Rightarrow ((let rec minus (n: nat) 
on n: (nat \to nat) \def (\lambda (m: nat).(match n with [O \Rightarrow O | 
(S k0) \Rightarrow (match m with [O \Rightarrow (S k0) | (S l) \Rightarrow 
(minus k0 l)])])) in minus) h1 k)])) (ASort (minus h1 k) n1) (ASort (minus h2 
k) n2) H4) in ((let H6 \def (f_equal A nat (\lambda (e: A).(match e in A 
return (\lambda (_: A).nat) with [(ASort _ n) \Rightarrow n | (AHead _ _) 
\Rightarrow n1])) (ASort (minus h1 k) n1) (ASort (minus h2 k) n2) H4) in 
(\lambda (H7: (eq nat (minus h1 k) (minus h2 k))).(eq_ind nat n1 (\lambda (n: 
nat).(leqz (ASort h1 n1) (ASort h2 n))) (eq_ind nat h1 (\lambda (n: 
nat).(leqz (ASort h1 n1) (ASort n n1))) (leqz_sort h1 h1 n1 n1 (refl_equal 
nat (plus h1 n1))) h2 (minus_minus k h1 h2 (le_S_n k h1 (le_S (S k) h1 H1)) 
(le_S_n k h2 (le_S (S k) h2 H2)) H7)) n2 H6))) H5))))) (\lambda (H2: (le h2 
k)).(let H3 \def (eq_ind A (aplus gz (ASort h1 n1) k) (\lambda (a: A).(eq A a 
(aplus gz (ASort h2 n2) k))) H0 (ASort (minus h1 k) n1) (aplus_gz_ge n1 k h1 
(le_S_n k h1 (le_S (S k) h1 H1)))) in (let H4 \def (eq_ind A (aplus gz (ASort 
h2 n2) k) (\lambda (a: A).(eq A (ASort (minus h1 k) n1) a)) H3 (ASort O (plus 
(minus k h2) n2)) (aplus_gz_le k h2 n2 H2)) in (let H5 \def (eq_ind nat 
(minus h1 k) (\lambda (n: nat).(eq A (ASort n n1) (ASort O (plus (minus k h2) 
n2)))) H4 (S (minus h1 (S k))) (minus_x_Sy h1 k H1)) in (let H6 \def (eq_ind 
A (ASort (S (minus h1 (S k))) n1) (\lambda (ee: A).(match ee in A return 
(\lambda (_: A).Prop) with [(ASort n _) \Rightarrow (match n in nat return 
(\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True]) 
| (AHead _ _) \Rightarrow False])) I (ASort O (plus (minus k h2) n2)) H5) in 
(False_ind (leqz (ASort h1 n1) (ASort h2 n2)) H6)))))))) (\lambda (H1: (le h1 
k)).(lt_le_e k h2 (leqz (ASort h1 n1) (ASort h2 n2)) (\lambda (H2: (lt k 
h2)).(let H3 \def (eq_ind A (aplus gz (ASort h1 n1) k) (\lambda (a: A).(eq A 
a (aplus gz (ASort h2 n2) k))) H0 (ASort O (plus (minus k h1) n1)) 
(aplus_gz_le k h1 n1 H1)) in (let H4 \def (eq_ind A (aplus gz (ASort h2 n2) 
k) (\lambda (a: A).(eq A (ASort O (plus (minus k h1) n1)) a)) H3 (ASort 
(minus h2 k) n2) (aplus_gz_ge n2 k h2 (le_S_n k h2 (le_S (S k) h2 H2)))) in 
(let H5 \def (sym_eq A (ASort O (plus (minus k h1) n1)) (ASort (minus h2 k) 
n2) H4) in (let H6 \def (eq_ind nat (minus h2 k) (\lambda (n: nat).(eq A 
(ASort n n2) (ASort O (plus (minus k h1) n1)))) H5 (S (minus h2 (S k))) 
(minus_x_Sy h2 k H2)) in (let H7 \def (eq_ind A (ASort (S (minus h2 (S k))) 
n2) (\lambda (ee: A).(match ee in A return (\lambda (_: A).Prop) with [(ASort 
n _) \Rightarrow (match n in nat return (\lambda (_: nat).Prop) with [O 
\Rightarrow False | (S _) \Rightarrow True]) | (AHead _ _) \Rightarrow 
False])) I (ASort O (plus (minus k h1) n1)) H6) in (False_ind (leqz (ASort h1 
n1) (ASort h2 n2)) H7))))))) (\lambda (H2: (le h2 k)).(let H3 \def (eq_ind A 
(aplus gz (ASort h1 n1) k) (\lambda (a: A).(eq A a (aplus gz (ASort h2 n2) 
k))) H0 (ASort O (plus (minus k h1) n1)) (aplus_gz_le k h1 n1 H1)) in (let H4 
\def (eq_ind A (aplus gz (ASort h2 n2) k) (\lambda (a: A).(eq A (ASort O 
(plus (minus k h1) n1)) a)) H3 (ASort O (plus (minus k h2) n2)) (aplus_gz_le 
k h2 n2 H2)) in (let H5 \def (f_equal A nat (\lambda (e: A).(match e in A 
return (\lambda (_: A).nat) with [(ASort _ n) \Rightarrow n | (AHead _ _) 
\Rightarrow ((let rec plus (n: nat) on n: (nat \to nat) \def (\lambda (m: 
nat).(match n with [O \Rightarrow m | (S p) \Rightarrow (S (plus p m))])) in 
plus) (minus k h1) n1)])) (ASort O (plus (minus k h1) n1)) (ASort O (plus 
(minus k h2) n2)) H4) in (let H_y \def (plus_plus k h1 h2 n1 n2 H1 H2 H5) in 
(leqz_sort h1 h2 n1 n2 H_y))))))))))))))) (\lambda (a0: A).(\lambda (a3: 
A).(\lambda (_: (leq gz a0 a3)).(\lambda (H1: (leqz a0 a3)).(\lambda (a4: 
A).(\lambda (a5: A).(\lambda (_: (leq gz a4 a5)).(\lambda (H3: (leqz a4 
a5)).(leqz_head a0 a3 H1 a4 a5 H3))))))))) a1 a2 H))).
(* COMMENTS
Initial nodes: 1375
END *)

theorem leq_leqz:
 \forall (a1: A).(\forall (a2: A).((leqz a1 a2) \to (leq gz a1 a2)))
\def
 \lambda (a1: A).(\lambda (a2: A).(\lambda (H: (leqz a1 a2)).(leqz_ind 
(\lambda (a: A).(\lambda (a0: A).(leq gz a a0))) (\lambda (h1: nat).(\lambda 
(h2: nat).(\lambda (n1: nat).(\lambda (n2: nat).(\lambda (H0: (eq nat (plus 
h1 n2) (plus h2 n1))).(leq_sort gz h1 h2 n1 n2 (plus h1 h2) (eq_ind_r A 
(ASort (minus h1 (plus h1 h2)) (next_plus gz n1 (minus (plus h1 h2) h1))) 
(\lambda (a: A).(eq A a (aplus gz (ASort h2 n2) (plus h1 h2)))) (eq_ind_r A 
(ASort (minus h2 (plus h1 h2)) (next_plus gz n2 (minus (plus h1 h2) h2))) 
(\lambda (a: A).(eq A (ASort (minus h1 (plus h1 h2)) (next_plus gz n1 (minus 
(plus h1 h2) h1))) a)) (eq_ind_r nat h2 (\lambda (n: nat).(eq A (ASort (minus 
h1 (plus h1 h2)) (next_plus gz n1 n)) (ASort (minus h2 (plus h1 h2)) 
(next_plus gz n2 (minus (plus h1 h2) h2))))) (eq_ind_r nat h1 (\lambda (n: 
nat).(eq A (ASort (minus h1 (plus h1 h2)) (next_plus gz n1 h2)) (ASort (minus 
h2 (plus h1 h2)) (next_plus gz n2 n)))) (eq_ind_r nat O (\lambda (n: nat).(eq 
A (ASort n (next_plus gz n1 h2)) (ASort (minus h2 (plus h1 h2)) (next_plus gz 
n2 h1)))) (eq_ind_r nat O (\lambda (n: nat).(eq A (ASort O (next_plus gz n1 
h2)) (ASort n (next_plus gz n2 h1)))) (eq_ind_r nat (plus h2 n1) (\lambda (n: 
nat).(eq A (ASort O n) (ASort O (next_plus gz n2 h1)))) (eq_ind_r nat (plus 
h1 n2) (\lambda (n: nat).(eq A (ASort O (plus h2 n1)) (ASort O n))) (f_equal 
nat A (ASort O) (plus h2 n1) (plus h1 n2) (sym_eq nat (plus h1 n2) (plus h2 
n1) H0)) (next_plus gz n2 h1) (next_plus_gz n2 h1)) (next_plus gz n1 h2) 
(next_plus_gz n1 h2)) (minus h2 (plus h1 h2)) (O_minus h2 (plus h1 h2) 
(le_plus_r h1 h2))) (minus h1 (plus h1 h2)) (O_minus h1 (plus h1 h2) 
(le_plus_l h1 h2))) (minus (plus h1 h2) h2) (minus_plus_r h1 h2)) (minus 
(plus h1 h2) h1) (minus_plus h1 h2)) (aplus gz (ASort h2 n2) (plus h1 h2)) 
(aplus_asort_simpl gz (plus h1 h2) h2 n2)) (aplus gz (ASort h1 n1) (plus h1 
h2)) (aplus_asort_simpl gz (plus h1 h2) h1 n1)))))))) (\lambda (a0: 
A).(\lambda (a3: A).(\lambda (_: (leqz a0 a3)).(\lambda (H1: (leq gz a0 
a3)).(\lambda (a4: A).(\lambda (a5: A).(\lambda (_: (leqz a4 a5)).(\lambda 
(H3: (leq gz a4 a5)).(leq_head gz a0 a3 H1 a4 a5 H3))))))))) a1 a2 H))).
(* COMMENTS
Initial nodes: 717
END *)

