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

include "Legacy-1/coq/defs.ma".

theorem f_equal:
 \forall (A: Set).(\forall (B: Set).(\forall (f: ((A \to B))).(\forall (x: 
A).(\forall (y: A).((eq A x y) \to (eq B (f x) (f y)))))))
\def
 \lambda (A: Set).(\lambda (B: Set).(\lambda (f: ((A \to B))).(\lambda (x: 
A).(\lambda (y: A).(\lambda (H: (eq A x y)).(eq_ind A x (\lambda (a: A).(eq B 
(f x) (f a))) (refl_equal B (f x)) y H)))))).
(* COMMENTS
Initial nodes: 51
END *)

theorem f_equal2:
 \forall (A1: Set).(\forall (A2: Set).(\forall (B: Set).(\forall (f: ((A1 \to 
(A2 \to B)))).(\forall (x1: A1).(\forall (y1: A1).(\forall (x2: A2).(\forall 
(y2: A2).((eq A1 x1 y1) \to ((eq A2 x2 y2) \to (eq B (f x1 x2) (f y1 
y2)))))))))))
\def
 \lambda (A1: Set).(\lambda (A2: Set).(\lambda (B: Set).(\lambda (f: ((A1 \to 
(A2 \to B)))).(\lambda (x1: A1).(\lambda (y1: A1).(\lambda (x2: A2).(\lambda 
(y2: A2).(\lambda (H: (eq A1 x1 y1)).(eq_ind A1 x1 (\lambda (a: A1).((eq A2 
x2 y2) \to (eq B (f x1 x2) (f a y2)))) (\lambda (H0: (eq A2 x2 y2)).(eq_ind 
A2 x2 (\lambda (a: A2).(eq B (f x1 x2) (f x1 a))) (refl_equal B (f x1 x2)) y2 
H0)) y1 H))))))))).
(* COMMENTS
Initial nodes: 109
END *)

theorem f_equal3:
 \forall (A1: Set).(\forall (A2: Set).(\forall (A3: Set).(\forall (B: 
Set).(\forall (f: ((A1 \to (A2 \to (A3 \to B))))).(\forall (x1: A1).(\forall 
(y1: A1).(\forall (x2: A2).(\forall (y2: A2).(\forall (x3: A3).(\forall (y3: 
A3).((eq A1 x1 y1) \to ((eq A2 x2 y2) \to ((eq A3 x3 y3) \to (eq B (f x1 x2 
x3) (f y1 y2 y3)))))))))))))))
\def
 \lambda (A1: Set).(\lambda (A2: Set).(\lambda (A3: Set).(\lambda (B: 
Set).(\lambda (f: ((A1 \to (A2 \to (A3 \to B))))).(\lambda (x1: A1).(\lambda 
(y1: A1).(\lambda (x2: A2).(\lambda (y2: A2).(\lambda (x3: A3).(\lambda (y3: 
A3).(\lambda (H: (eq A1 x1 y1)).(eq_ind A1 x1 (\lambda (a: A1).((eq A2 x2 y2) 
\to ((eq A3 x3 y3) \to (eq B (f x1 x2 x3) (f a y2 y3))))) (\lambda (H0: (eq 
A2 x2 y2)).(eq_ind A2 x2 (\lambda (a: A2).((eq A3 x3 y3) \to (eq B (f x1 x2 
x3) (f x1 a y3)))) (\lambda (H1: (eq A3 x3 y3)).(eq_ind A3 x3 (\lambda (a: 
A3).(eq B (f x1 x2 x3) (f x1 x2 a))) (refl_equal B (f x1 x2 x3)) y3 H1)) y2 
H0)) y1 H)))))))))))).
(* COMMENTS
Initial nodes: 183
END *)

theorem sym_eq:
 \forall (A: Set).(\forall (x: A).(\forall (y: A).((eq A x y) \to (eq A y 
x))))
\def
 \lambda (A: Set).(\lambda (x: A).(\lambda (y: A).(\lambda (H: (eq A x 
y)).(eq_ind A x (\lambda (a: A).(eq A a x)) (refl_equal A x) y H)))).
(* COMMENTS
Initial nodes: 39
END *)

theorem eq_ind_r:
 \forall (A: Set).(\forall (x: A).(\forall (P: ((A \to Prop))).((P x) \to 
(\forall (y: A).((eq A y x) \to (P y))))))
\def
 \lambda (A: Set).(\lambda (x: A).(\lambda (P: ((A \to Prop))).(\lambda (H: 
(P x)).(\lambda (y: A).(\lambda (H0: (eq A y x)).(match (sym_eq A y x H0) in 
eq return (\lambda (a: A).(\lambda (_: (eq ? ? a)).(P a))) with [refl_equal 
\Rightarrow H])))))).
(* COMMENTS
Initial nodes: 38
END *)

theorem trans_eq:
 \forall (A: Set).(\forall (x: A).(\forall (y: A).(\forall (z: A).((eq A x y) 
\to ((eq A y z) \to (eq A x z))))))
\def
 \lambda (A: Set).(\lambda (x: A).(\lambda (y: A).(\lambda (z: A).(\lambda 
(H: (eq A x y)).(\lambda (H0: (eq A y z)).(eq_ind A y (\lambda (a: A).(eq A x 
a)) H z H0)))))).
(* COMMENTS
Initial nodes: 45
END *)

theorem sym_not_eq:
 \forall (A: Set).(\forall (x: A).(\forall (y: A).((not (eq A x y)) \to (not 
(eq A y x)))))
\def
 \lambda (A: Set).(\lambda (x: A).(\lambda (y: A).(\lambda (h1: (not (eq A x 
y))).(\lambda (h2: (eq A y x)).(h1 (eq_ind A y (\lambda (a: A).(eq A a y)) 
(refl_equal A y) x h2)))))).
(* COMMENTS
Initial nodes: 51
END *)

theorem nat_double_ind:
 \forall (R: ((nat \to (nat \to Prop)))).(((\forall (n: nat).(R O n))) \to 
(((\forall (n: nat).(R (S n) O))) \to (((\forall (n: nat).(\forall (m: 
nat).((R n m) \to (R (S n) (S m)))))) \to (\forall (n: nat).(\forall (m: 
nat).(R n m))))))
\def
 \lambda (R: ((nat \to (nat \to Prop)))).(\lambda (H: ((\forall (n: nat).(R O 
n)))).(\lambda (H0: ((\forall (n: nat).(R (S n) O)))).(\lambda (H1: ((\forall 
(n: nat).(\forall (m: nat).((R n m) \to (R (S n) (S m))))))).(\lambda (n: 
nat).(nat_ind (\lambda (n0: nat).(\forall (m: nat).(R n0 m))) H (\lambda (n0: 
nat).(\lambda (H2: ((\forall (m: nat).(R n0 m)))).(\lambda (m: nat).(nat_ind 
(\lambda (n1: nat).(R (S n0) n1)) (H0 n0) (\lambda (n1: nat).(\lambda (_: (R 
(S n0) n1)).(H1 n0 n1 (H2 n1)))) m)))) n))))).
(* COMMENTS
Initial nodes: 111
END *)

theorem eq_add_S:
 \forall (n: nat).(\forall (m: nat).((eq nat (S n) (S m)) \to (eq nat n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (eq nat (S n) (S 
m))).(f_equal nat nat pred (S n) (S m) H))).
(* COMMENTS
Initial nodes: 33
END *)

theorem O_S:
 \forall (n: nat).(not (eq nat O (S n)))
\def
 \lambda (n: nat).(\lambda (H: (eq nat O (S n))).(eq_ind nat (S n) (\lambda 
(n0: nat).(IsSucc n0)) I O (sym_eq nat O (S n) H))).
(* COMMENTS
Initial nodes: 41
END *)

theorem not_eq_S:
 \forall (n: nat).(\forall (m: nat).((not (eq nat n m)) \to (not (eq nat (S 
n) (S m)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (not (eq nat n m))).(\lambda 
(H0: (eq nat (S n) (S m))).(H (eq_add_S n m H0))))).
(* COMMENTS
Initial nodes: 35
END *)

theorem pred_Sn:
 \forall (m: nat).(eq nat m (pred (S m)))
\def
 \lambda (m: nat).(refl_equal nat (pred (S m))).
(* COMMENTS
Initial nodes: 11
END *)

theorem S_pred:
 \forall (n: nat).(\forall (m: nat).((lt m n) \to (eq nat n (S (pred n)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt m n)).(le_ind (S m) 
(\lambda (n0: nat).(eq nat n0 (S (pred n0)))) (refl_equal nat (S (pred (S 
m)))) (\lambda (m0: nat).(\lambda (_: (le (S m) m0)).(\lambda (_: (eq nat m0 
(S (pred m0)))).(refl_equal nat (S (pred (S m0))))))) n H))).
(* COMMENTS
Initial nodes: 79
END *)

theorem le_trans:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((le n m) \to ((le m p) 
\to (le n p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (le n 
m)).(\lambda (H0: (le m p)).(le_ind m (\lambda (n0: nat).(le n n0)) H 
(\lambda (m0: nat).(\lambda (_: (le m m0)).(\lambda (IHle: (le n m0)).(le_S n 
m0 IHle)))) p H0))))).
(* COMMENTS
Initial nodes: 57
END *)

theorem le_trans_S:
 \forall (n: nat).(\forall (m: nat).((le (S n) m) \to (le n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le (S n) m)).(le_trans n (S 
n) m (le_S n n (le_n n)) H))).
(* COMMENTS
Initial nodes: 33
END *)

theorem le_n_S:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (le (S n) (S m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(le_ind n (\lambda 
(n0: nat).(le (S n) (S n0))) (le_n (S n)) (\lambda (m0: nat).(\lambda (_: (le 
n m0)).(\lambda (IHle: (le (S n) (S m0))).(le_S (S n) (S m0) IHle)))) m H))).
(* COMMENTS
Initial nodes: 65
END *)

theorem le_O_n:
 \forall (n: nat).(le O n)
\def
 \lambda (n: nat).(nat_ind (\lambda (n0: nat).(le O n0)) (le_n O) (\lambda 
(n0: nat).(\lambda (IHn: (le O n0)).(le_S O n0 IHn))) n).
(* COMMENTS
Initial nodes: 33
END *)

theorem le_S_n:
 \forall (n: nat).(\forall (m: nat).((le (S n) (S m)) \to (le n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le (S n) (S m))).(le_ind (S 
n) (\lambda (n0: nat).(le (pred (S n)) (pred n0))) (le_n n) (\lambda (m0: 
nat).(\lambda (H0: (le (S n) m0)).(\lambda (_: (le n (pred m0))).(le_trans_S 
n m0 H0)))) (S m) H))).
(* COMMENTS
Initial nodes: 69
END *)

theorem le_Sn_O:
 \forall (n: nat).(not (le (S n) O))
\def
 \lambda (n: nat).(\lambda (H: (le (S n) O)).(le_ind (S n) (\lambda (n0: 
nat).(IsSucc n0)) I (\lambda (m: nat).(\lambda (_: (le (S n) m)).(\lambda (_: 
(IsSucc m)).I))) O H)).
(* COMMENTS
Initial nodes: 43
END *)

theorem le_Sn_n:
 \forall (n: nat).(not (le (S n) n))
\def
 \lambda (n: nat).(nat_ind (\lambda (n0: nat).(not (le (S n0) n0))) (le_Sn_O 
O) (\lambda (n0: nat).(\lambda (IHn: (not (le (S n0) n0))).(\lambda (H: (le 
(S (S n0)) (S n0))).(IHn (le_S_n (S n0) n0 H))))) n).
(* COMMENTS
Initial nodes: 57
END *)

theorem le_antisym:
 \forall (n: nat).(\forall (m: nat).((le n m) \to ((le m n) \to (eq nat n 
m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (h: (le n m)).(le_ind n (\lambda 
(n0: nat).((le n0 n) \to (eq nat n n0))) (\lambda (_: (le n n)).(refl_equal 
nat n)) (\lambda (m0: nat).(\lambda (H: (le n m0)).(\lambda (_: (((le m0 n) 
\to (eq nat n m0)))).(\lambda (H1: (le (S m0) n)).(False_ind (eq nat n (S 
m0)) (let H2 \def (le_trans (S m0) n m0 H1 H) in ((let H3 \def (le_Sn_n m0) 
in (\lambda (H4: (le (S m0) m0)).(H3 H4))) H2))))))) m h))).
(* COMMENTS
Initial nodes: 119
END *)

theorem le_n_O_eq:
 \forall (n: nat).((le n O) \to (eq nat O n))
\def
 \lambda (n: nat).(\lambda (H: (le n O)).(le_antisym O n (le_O_n n) H)).
(* COMMENTS
Initial nodes: 19
END *)

theorem le_elim_rel:
 \forall (P: ((nat \to (nat \to Prop)))).(((\forall (p: nat).(P O p))) \to 
(((\forall (p: nat).(\forall (q: nat).((le p q) \to ((P p q) \to (P (S p) (S 
q))))))) \to (\forall (n: nat).(\forall (m: nat).((le n m) \to (P n m))))))
\def
 \lambda (P: ((nat \to (nat \to Prop)))).(\lambda (H: ((\forall (p: nat).(P O 
p)))).(\lambda (H0: ((\forall (p: nat).(\forall (q: nat).((le p q) \to ((P p 
q) \to (P (S p) (S q)))))))).(\lambda (n: nat).(nat_ind (\lambda (n0: 
nat).(\forall (m: nat).((le n0 m) \to (P n0 m)))) (\lambda (m: nat).(\lambda 
(_: (le O m)).(H m))) (\lambda (n0: nat).(\lambda (IHn: ((\forall (m: 
nat).((le n0 m) \to (P n0 m))))).(\lambda (m: nat).(\lambda (Le: (le (S n0) 
m)).(le_ind (S n0) (\lambda (n1: nat).(P (S n0) n1)) (H0 n0 n0 (le_n n0) (IHn 
n0 (le_n n0))) (\lambda (m0: nat).(\lambda (H1: (le (S n0) m0)).(\lambda (_: 
(P (S n0) m0)).(H0 n0 m0 (le_trans_S n0 m0 H1) (IHn m0 (le_trans_S n0 m0 
H1)))))) m Le))))) n)))).
(* COMMENTS
Initial nodes: 181
END *)

theorem lt_n_n:
 \forall (n: nat).(not (lt n n))
\def
 le_Sn_n.
(* COMMENTS
Initial nodes: 1
END *)

theorem lt_n_S:
 \forall (n: nat).(\forall (m: nat).((lt n m) \to (lt (S n) (S m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt n m)).(le_n_S (S n) m 
H))).
(* COMMENTS
Initial nodes: 19
END *)

theorem lt_n_Sn:
 \forall (n: nat).(lt n (S n))
\def
 \lambda (n: nat).(le_n (S n)).
(* COMMENTS
Initial nodes: 7
END *)

theorem lt_S_n:
 \forall (n: nat).(\forall (m: nat).((lt (S n) (S m)) \to (lt n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt (S n) (S m))).(le_S_n (S 
n) m H))).
(* COMMENTS
Initial nodes: 23
END *)

theorem lt_n_O:
 \forall (n: nat).(not (lt n O))
\def
 le_Sn_O.
(* COMMENTS
Initial nodes: 1
END *)

theorem lt_trans:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((lt n m) \to ((lt m p) 
\to (lt n p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (lt n 
m)).(\lambda (H0: (lt m p)).(le_ind (S m) (\lambda (n0: nat).(lt n n0)) (le_S 
(S n) m H) (\lambda (m0: nat).(\lambda (_: (le (S m) m0)).(\lambda (IHle: (lt 
n m0)).(le_S (S n) m0 IHle)))) p H0))))).
(* COMMENTS
Initial nodes: 71
END *)

theorem lt_O_Sn:
 \forall (n: nat).(lt O (S n))
\def
 \lambda (n: nat).(le_n_S O n (le_O_n n)).
(* COMMENTS
Initial nodes: 11
END *)

theorem lt_le_S:
 \forall (n: nat).(\forall (p: nat).((lt n p) \to (le (S n) p)))
\def
 \lambda (n: nat).(\lambda (p: nat).(\lambda (H: (lt n p)).H)).
(* COMMENTS
Initial nodes: 11
END *)

theorem le_not_lt:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (not (lt m n))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(le_ind n (\lambda 
(n0: nat).(not (lt n0 n))) (lt_n_n n) (\lambda (m0: nat).(\lambda (_: (le n 
m0)).(\lambda (IHle: (not (lt m0 n))).(\lambda (H1: (lt (S m0) n)).(IHle 
(le_trans_S (S m0) n H1)))))) m H))).
(* COMMENTS
Initial nodes: 67
END *)

theorem le_lt_n_Sm:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (lt n (S m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(le_n_S n m H))).
(* COMMENTS
Initial nodes: 17
END *)

theorem le_lt_trans:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((le n m) \to ((lt m p) 
\to (lt n p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (le n 
m)).(\lambda (H0: (lt m p)).(le_ind (S m) (\lambda (n0: nat).(lt n n0)) 
(le_n_S n m H) (\lambda (m0: nat).(\lambda (_: (le (S m) m0)).(\lambda (IHle: 
(lt n m0)).(le_S (S n) m0 IHle)))) p H0))))).
(* COMMENTS
Initial nodes: 69
END *)

theorem lt_le_trans:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((lt n m) \to ((le m p) 
\to (lt n p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (lt n 
m)).(\lambda (H0: (le m p)).(le_ind m (\lambda (n0: nat).(lt n n0)) H 
(\lambda (m0: nat).(\lambda (_: (le m m0)).(\lambda (IHle: (lt n m0)).(le_S 
(S n) m0 IHle)))) p H0))))).
(* COMMENTS
Initial nodes: 59
END *)

theorem lt_le_weak:
 \forall (n: nat).(\forall (m: nat).((lt n m) \to (le n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt n m)).(le_trans_S n m 
H))).
(* COMMENTS
Initial nodes: 17
END *)

theorem lt_n_Sm_le:
 \forall (n: nat).(\forall (m: nat).((lt n (S m)) \to (le n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt n (S m))).(le_S_n n m 
H))).
(* COMMENTS
Initial nodes: 19
END *)

theorem le_lt_or_eq:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (or (lt n m) (eq nat n m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(le_ind n (\lambda 
(n0: nat).(or (lt n n0) (eq nat n n0))) (or_intror (lt n n) (eq nat n n) 
(refl_equal nat n)) (\lambda (m0: nat).(\lambda (H0: (le n m0)).(\lambda (_: 
(or (lt n m0) (eq nat n m0))).(or_introl (lt n (S m0)) (eq nat n (S m0)) 
(le_n_S n m0 H0))))) m H))).
(* COMMENTS
Initial nodes: 109
END *)

theorem le_or_lt:
 \forall (n: nat).(\forall (m: nat).(or (le n m) (lt m n)))
\def
 \lambda (n: nat).(\lambda (m: nat).(nat_double_ind (\lambda (n0: 
nat).(\lambda (n1: nat).(or (le n0 n1) (lt n1 n0)))) (\lambda (n0: 
nat).(or_introl (le O n0) (lt n0 O) (le_O_n n0))) (\lambda (n0: 
nat).(or_intror (le (S n0) O) (lt O (S n0)) (lt_le_S O (S n0) (lt_O_Sn n0)))) 
(\lambda (n0: nat).(\lambda (m0: nat).(\lambda (H: (or (le n0 m0) (lt m0 
n0))).(or_ind (le n0 m0) (lt m0 n0) (or (le (S n0) (S m0)) (lt (S m0) (S 
n0))) (\lambda (H0: (le n0 m0)).(or_introl (le (S n0) (S m0)) (lt (S m0) (S 
n0)) (le_n_S n0 m0 H0))) (\lambda (H0: (lt m0 n0)).(or_intror (le (S n0) (S 
m0)) (lt (S m0) (S n0)) (le_n_S (S m0) n0 H0))) H)))) n m)).
(* COMMENTS
Initial nodes: 209
END *)

theorem plus_n_O:
 \forall (n: nat).(eq nat n (plus n O))
\def
 \lambda (n: nat).(nat_ind (\lambda (n0: nat).(eq nat n0 (plus n0 O))) 
(refl_equal nat O) (\lambda (n0: nat).(\lambda (H: (eq nat n0 (plus n0 
O))).(f_equal nat nat S n0 (plus n0 O) H))) n).
(* COMMENTS
Initial nodes: 57
END *)

theorem plus_n_Sm:
 \forall (n: nat).(\forall (m: nat).(eq nat (S (plus n m)) (plus n (S m))))
\def
 \lambda (m: nat).(\lambda (n: nat).(nat_ind (\lambda (n0: nat).(eq nat (S 
(plus n0 n)) (plus n0 (S n)))) (refl_equal nat (S n)) (\lambda (n0: 
nat).(\lambda (H: (eq nat (S (plus n0 n)) (plus n0 (S n)))).(f_equal nat nat 
S (S (plus n0 n)) (plus n0 (S n)) H))) m)).
(* COMMENTS
Initial nodes: 85
END *)

theorem plus_sym:
 \forall (n: nat).(\forall (m: nat).(eq nat (plus n m) (plus m n)))
\def
 \lambda (n: nat).(\lambda (m: nat).(nat_ind (\lambda (n0: nat).(eq nat (plus 
n0 m) (plus m n0))) (plus_n_O m) (\lambda (y: nat).(\lambda (H: (eq nat (plus 
y m) (plus m y))).(eq_ind nat (S (plus m y)) (\lambda (n0: nat).(eq nat (S 
(plus y m)) n0)) (f_equal nat nat S (plus y m) (plus m y) H) (plus m (S y)) 
(plus_n_Sm m y)))) n)).
(* COMMENTS
Initial nodes: 111
END *)

theorem plus_Snm_nSm:
 \forall (n: nat).(\forall (m: nat).(eq nat (plus (S n) m) (plus n (S m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(eq_ind_r nat (plus m n) (\lambda (n0: 
nat).(eq nat (S n0) (plus n (S m)))) (eq_ind_r nat (plus (S m) n) (\lambda 
(n0: nat).(eq nat (S (plus m n)) n0)) (refl_equal nat (plus (S m) n)) (plus n 
(S m)) (plus_sym n (S m))) (plus n m) (plus_sym n m))).
(* COMMENTS
Initial nodes: 99
END *)

theorem plus_assoc_l:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(eq nat (plus n (plus m 
p)) (plus (plus n m) p))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(nat_ind (\lambda (n0: 
nat).(eq nat (plus n0 (plus m p)) (plus (plus n0 m) p))) (refl_equal nat 
(plus m p)) (\lambda (n0: nat).(\lambda (H: (eq nat (plus n0 (plus m p)) 
(plus (plus n0 m) p))).(f_equal nat nat S (plus n0 (plus m p)) (plus (plus n0 
m) p) H))) n))).
(* COMMENTS
Initial nodes: 101
END *)

theorem plus_assoc_r:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(eq nat (plus (plus n 
m) p) (plus n (plus m p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(sym_eq nat (plus n 
(plus m p)) (plus (plus n m) p) (plus_assoc_l n m p)))).
(* COMMENTS
Initial nodes: 37
END *)

theorem simpl_plus_l:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((eq nat (plus n m) 
(plus n p)) \to (eq nat m p))))
\def
 \lambda (n: nat).(nat_ind (\lambda (n0: nat).(\forall (m: nat).(\forall (p: 
nat).((eq nat (plus n0 m) (plus n0 p)) \to (eq nat m p))))) (\lambda (m: 
nat).(\lambda (p: nat).(\lambda (H: (eq nat m p)).H))) (\lambda (n0: 
nat).(\lambda (IHn: ((\forall (m: nat).(\forall (p: nat).((eq nat (plus n0 m) 
(plus n0 p)) \to (eq nat m p)))))).(\lambda (m: nat).(\lambda (p: 
nat).(\lambda (H: (eq nat (S (plus n0 m)) (S (plus n0 p)))).(IHn m p (IHn 
(plus n0 m) (plus n0 p) (f_equal nat nat (plus n0) (plus n0 m) (plus n0 p) 
(eq_add_S (plus n0 m) (plus n0 p) H))))))))) n).
(* COMMENTS
Initial nodes: 161
END *)

theorem minus_n_O:
 \forall (n: nat).(eq nat n (minus n O))
\def
 \lambda (n: nat).(nat_ind (\lambda (n0: nat).(eq nat n0 (minus n0 O))) 
(refl_equal nat O) (\lambda (n0: nat).(\lambda (_: (eq nat n0 (minus n0 
O))).(refl_equal nat (S n0)))) n).
(* COMMENTS
Initial nodes: 47
END *)

theorem minus_n_n:
 \forall (n: nat).(eq nat O (minus n n))
\def
 \lambda (n: nat).(nat_ind (\lambda (n0: nat).(eq nat O (minus n0 n0))) 
(refl_equal nat O) (\lambda (n0: nat).(\lambda (IHn: (eq nat O (minus n0 
n0))).IHn)) n).
(* COMMENTS
Initial nodes: 41
END *)

theorem minus_Sn_m:
 \forall (n: nat).(\forall (m: nat).((le m n) \to (eq nat (S (minus n m)) 
(minus (S n) m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (Le: (le m n)).(le_elim_rel 
(\lambda (n0: nat).(\lambda (n1: nat).(eq nat (S (minus n1 n0)) (minus (S n1) 
n0)))) (\lambda (p: nat).(f_equal nat nat S (minus p O) p (sym_eq nat p 
(minus p O) (minus_n_O p)))) (\lambda (p: nat).(\lambda (q: nat).(\lambda (_: 
(le p q)).(\lambda (H0: (eq nat (S (minus q p)) (match p with [O \Rightarrow 
(S q) | (S l) \Rightarrow (minus q l)]))).H0)))) m n Le))).
(* COMMENTS
Initial nodes: 111
END *)

theorem plus_minus:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((eq nat n (plus m p)) 
\to (eq nat p (minus n m)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(nat_double_ind 
(\lambda (n0: nat).(\lambda (n1: nat).((eq nat n1 (plus n0 p)) \to (eq nat p 
(minus n1 n0))))) (\lambda (n0: nat).(\lambda (H: (eq nat n0 p)).(eq_ind nat 
n0 (\lambda (n1: nat).(eq nat p n1)) (sym_eq nat n0 p H) (minus n0 O) 
(minus_n_O n0)))) (\lambda (n0: nat).(\lambda (H: (eq nat O (S (plus n0 
p)))).(False_ind (eq nat p O) (let H0 \def H in ((let H1 \def (O_S (plus n0 
p)) in (\lambda (H2: (eq nat O (S (plus n0 p)))).(H1 H2))) H0))))) (\lambda 
(n0: nat).(\lambda (m0: nat).(\lambda (H: (((eq nat m0 (plus n0 p)) \to (eq 
nat p (minus m0 n0))))).(\lambda (H0: (eq nat (S m0) (S (plus n0 p)))).(H 
(eq_add_S m0 (plus n0 p) H0)))))) m n))).
(* COMMENTS
Initial nodes: 199
END *)

theorem minus_plus:
 \forall (n: nat).(\forall (m: nat).(eq nat (minus (plus n m) n) m))
\def
 \lambda (n: nat).(\lambda (m: nat).(sym_eq nat m (minus (plus n m) n) 
(plus_minus (plus n m) n m (refl_equal nat (plus n m))))).
(* COMMENTS
Initial nodes: 41
END *)

theorem le_pred_n:
 \forall (n: nat).(le (pred n) n)
\def
 \lambda (n: nat).(nat_ind (\lambda (n0: nat).(le (pred n0) n0)) (le_n O) 
(\lambda (n0: nat).(\lambda (_: (le (pred n0) n0)).(le_S (pred (S n0)) n0 
(le_n n0)))) n).
(* COMMENTS
Initial nodes: 43
END *)

theorem le_plus_l:
 \forall (n: nat).(\forall (m: nat).(le n (plus n m)))
\def
 \lambda (n: nat).(nat_ind (\lambda (n0: nat).(\forall (m: nat).(le n0 (plus 
n0 m)))) (\lambda (m: nat).(le_O_n m)) (\lambda (n0: nat).(\lambda (IHn: 
((\forall (m: nat).(le n0 (plus n0 m))))).(\lambda (m: nat).(le_n_S n0 (plus 
n0 m) (IHn m))))) n).
(* COMMENTS
Initial nodes: 55
END *)

theorem le_plus_r:
 \forall (n: nat).(\forall (m: nat).(le m (plus n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(nat_ind (\lambda (n0: nat).(le m (plus 
n0 m))) (le_n m) (\lambda (n0: nat).(\lambda (H: (le m (plus n0 m))).(le_S m 
(plus n0 m) H))) n)).
(* COMMENTS
Initial nodes: 47
END *)

theorem simpl_le_plus_l:
 \forall (p: nat).(\forall (n: nat).(\forall (m: nat).((le (plus p n) (plus p 
m)) \to (le n m))))
\def
 \lambda (p: nat).(nat_ind (\lambda (n: nat).(\forall (n0: nat).(\forall (m: 
nat).((le (plus n n0) (plus n m)) \to (le n0 m))))) (\lambda (n: 
nat).(\lambda (m: nat).(\lambda (H: (le n m)).H))) (\lambda (p0: 
nat).(\lambda (IHp: ((\forall (n: nat).(\forall (m: nat).((le (plus p0 n) 
(plus p0 m)) \to (le n m)))))).(\lambda (n: nat).(\lambda (m: nat).(\lambda 
(H: (le (S (plus p0 n)) (S (plus p0 m)))).(IHp n m (le_S_n (plus p0 n) (plus 
p0 m) H))))))) p).
(* COMMENTS
Initial nodes: 113
END *)

theorem le_plus_trans:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((le n m) \to (le n 
(plus m p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (le n 
m)).(le_trans n m (plus m p) H (le_plus_l m p))))).
(* COMMENTS
Initial nodes: 31
END *)

theorem le_reg_l:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((le n m) \to (le (plus 
p n) (plus p m)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(nat_ind (\lambda (n0: 
nat).((le n m) \to (le (plus n0 n) (plus n0 m)))) (\lambda (H: (le n m)).H) 
(\lambda (p0: nat).(\lambda (IHp: (((le n m) \to (le (plus p0 n) (plus p0 
m))))).(\lambda (H: (le n m)).(le_n_S (plus p0 n) (plus p0 m) (IHp H))))) 
p))).
(* COMMENTS
Initial nodes: 85
END *)

theorem le_plus_plus:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(\forall (q: nat).((le 
n m) \to ((le p q) \to (le (plus n p) (plus m q)))))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (q: 
nat).(\lambda (H: (le n m)).(\lambda (H0: (le p q)).(le_ind n (\lambda (n0: 
nat).(le (plus n p) (plus n0 q))) (le_reg_l p q n H0) (\lambda (m0: 
nat).(\lambda (_: (le n m0)).(\lambda (H2: (le (plus n p) (plus m0 q))).(le_S 
(plus n p) (plus m0 q) H2)))) m H)))))).
(* COMMENTS
Initial nodes: 91
END *)

theorem le_plus_minus:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (eq nat m (plus n (minus m 
n)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (Le: (le n m)).(le_elim_rel 
(\lambda (n0: nat).(\lambda (n1: nat).(eq nat n1 (plus n0 (minus n1 n0))))) 
(\lambda (p: nat).(minus_n_O p)) (\lambda (p: nat).(\lambda (q: nat).(\lambda 
(_: (le p q)).(\lambda (H0: (eq nat q (plus p (minus q p)))).(f_equal nat nat 
S q (plus p (minus q p)) H0))))) n m Le))).
(* COMMENTS
Initial nodes: 91
END *)

theorem le_plus_minus_r:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (eq nat (plus n (minus m 
n)) m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(sym_eq nat m 
(plus n (minus m n)) (le_plus_minus n m H)))).
(* COMMENTS
Initial nodes: 33
END *)

theorem simpl_lt_plus_l:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((lt (plus p n) (plus p 
m)) \to (lt n m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(nat_ind (\lambda (n0: 
nat).((lt (plus n0 n) (plus n0 m)) \to (lt n m))) (\lambda (H: (lt n m)).H) 
(\lambda (p0: nat).(\lambda (IHp: (((lt (plus p0 n) (plus p0 m)) \to (lt n 
m)))).(\lambda (H: (lt (S (plus p0 n)) (S (plus p0 m)))).(IHp (le_S_n (S 
(plus p0 n)) (plus p0 m) H))))) p))).
(* COMMENTS
Initial nodes: 99
END *)

theorem lt_reg_l:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((lt n m) \to (lt (plus 
p n) (plus p m)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(nat_ind (\lambda (n0: 
nat).((lt n m) \to (lt (plus n0 n) (plus n0 m)))) (\lambda (H: (lt n m)).H) 
(\lambda (p0: nat).(\lambda (IHp: (((lt n m) \to (lt (plus p0 n) (plus p0 
m))))).(\lambda (H: (lt n m)).(lt_n_S (plus p0 n) (plus p0 m) (IHp H))))) 
p))).
(* COMMENTS
Initial nodes: 85
END *)

theorem lt_reg_r:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((lt n m) \to (lt (plus 
n p) (plus m p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (lt n 
m)).(eq_ind_r nat (plus p n) (\lambda (n0: nat).(lt n0 (plus m p))) (eq_ind_r 
nat (plus p m) (\lambda (n0: nat).(lt (plus p n) n0)) (nat_ind (\lambda (n0: 
nat).(lt (plus n0 n) (plus n0 m))) H (\lambda (n0: nat).(\lambda (_: (lt 
(plus n0 n) (plus n0 m))).(lt_reg_l n m (S n0) H))) p) (plus m p) (plus_sym m 
p)) (plus n p) (plus_sym n p))))).
(* COMMENTS
Initial nodes: 129
END *)

theorem le_lt_plus_plus:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(\forall (q: nat).((le 
n m) \to ((lt p q) \to (lt (plus n p) (plus m q)))))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (q: 
nat).(\lambda (H: (le n m)).(\lambda (H0: (le (S p) q)).(eq_ind_r nat (plus n 
(S p)) (\lambda (n0: nat).(le n0 (plus m q))) (le_plus_plus n m (S p) q H H0) 
(plus (S n) p) (plus_Snm_nSm n p))))))).
(* COMMENTS
Initial nodes: 75
END *)

theorem lt_le_plus_plus:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(\forall (q: nat).((lt 
n m) \to ((le p q) \to (lt (plus n p) (plus m q)))))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (q: 
nat).(\lambda (H: (le (S n) m)).(\lambda (H0: (le p q)).(le_plus_plus (S n) m 
p q H H0)))))).
(* COMMENTS
Initial nodes: 37
END *)

theorem lt_plus_plus:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(\forall (q: nat).((lt 
n m) \to ((lt p q) \to (lt (plus n p) (plus m q)))))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (q: 
nat).(\lambda (H: (lt n m)).(\lambda (H0: (lt p q)).(lt_le_plus_plus n m p q 
H (lt_le_weak p q H0))))))).
(* COMMENTS
Initial nodes: 39
END *)

theorem well_founded_ltof:
 \forall (A: Set).(\forall (f: ((A \to nat))).(well_founded A (ltof A f)))
\def
 \lambda (A: Set).(\lambda (f: ((A \to nat))).(let H \def (\lambda (n: 
nat).(nat_ind (\lambda (n0: nat).(\forall (a: A).((lt (f a) n0) \to (Acc A 
(ltof A f) a)))) (\lambda (a: A).(\lambda (H: (lt (f a) O)).(False_ind (Acc A 
(ltof A f) a) (let H0 \def H in ((let H1 \def (lt_n_O (f a)) in (\lambda (H2: 
(lt (f a) O)).(H1 H2))) H0))))) (\lambda (n0: nat).(\lambda (IHn: ((\forall 
(a: A).((lt (f a) n0) \to (Acc A (ltof A f) a))))).(\lambda (a: A).(\lambda 
(ltSma: (lt (f a) (S n0))).(Acc_intro A (ltof A f) a (\lambda (b: A).(\lambda 
(ltfafb: (lt (f b) (f a))).(IHn b (lt_le_trans (f b) (f a) n0 ltfafb 
(lt_n_Sm_le (f a) n0 ltSma)))))))))) n)) in (\lambda (a: A).(H (S (f a)) a 
(le_n (S (f a))))))).
(* COMMENTS
Initial nodes: 189
END *)

theorem lt_wf:
 well_founded nat lt
\def
 well_founded_ltof nat (\lambda (m: nat).m).
(* COMMENTS
Initial nodes: 7
END *)

theorem lt_wf_ind:
 \forall (p: nat).(\forall (P: ((nat \to Prop))).(((\forall (n: 
nat).(((\forall (m: nat).((lt m n) \to (P m)))) \to (P n)))) \to (P p)))
\def
 \lambda (p: nat).(\lambda (P: ((nat \to Prop))).(\lambda (H: ((\forall (n: 
nat).(((\forall (m: nat).((lt m n) \to (P m)))) \to (P n))))).(Acc_ind nat lt 
(\lambda (n: nat).(P n)) (\lambda (x: nat).(\lambda (_: ((\forall (y: 
nat).((lt y x) \to (Acc nat lt y))))).(\lambda (H1: ((\forall (y: nat).((lt y 
x) \to (P y))))).(H x H1)))) p (lt_wf p)))).
(* COMMENTS
Initial nodes: 77
END *)

