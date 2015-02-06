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

include "legacy_1/coq/fwd.ma".

theorem f_equal:
 \forall (A: Type[0]).(\forall (B: Type[0]).(\forall (f: ((A \to 
B))).(\forall (x: A).(\forall (y: A).((eq A x y) \to (eq B (f x) (f y)))))))
\def
 \lambda (A: Type[0]).(\lambda (B: Type[0]).(\lambda (f: ((A \to 
B))).(\lambda (x: A).(\lambda (y: A).(\lambda (H: (eq A x y)).(let TMP_3 \def 
(\lambda (a: A).(let TMP_1 \def (f x) in (let TMP_2 \def (f a) in (eq B TMP_1 
TMP_2)))) in (let TMP_4 \def (f x) in (let TMP_5 \def (refl_equal B TMP_4) in 
(eq_ind A x TMP_3 TMP_5 y H))))))))).

theorem f_equal2:
 \forall (A1: Type[0]).(\forall (A2: Type[0]).(\forall (B: Type[0]).(\forall 
(f: ((A1 \to (A2 \to B)))).(\forall (x1: A1).(\forall (y1: A1).(\forall (x2: 
A2).(\forall (y2: A2).((eq A1 x1 y1) \to ((eq A2 x2 y2) \to (eq B (f x1 x2) 
(f y1 y2)))))))))))
\def
 \lambda (A1: Type[0]).(\lambda (A2: Type[0]).(\lambda (B: Type[0]).(\lambda 
(f: ((A1 \to (A2 \to B)))).(\lambda (x1: A1).(\lambda (y1: A1).(\lambda (x2: 
A2).(\lambda (y2: A2).(\lambda (H: (eq A1 x1 y1)).(let TMP_3 \def (\lambda 
(a: A1).((eq A2 x2 y2) \to (let TMP_1 \def (f x1 x2) in (let TMP_2 \def (f a 
y2) in (eq B TMP_1 TMP_2))))) in (let TMP_9 \def (\lambda (H0: (eq A2 x2 
y2)).(let TMP_6 \def (\lambda (a: A2).(let TMP_4 \def (f x1 x2) in (let TMP_5 
\def (f x1 a) in (eq B TMP_4 TMP_5)))) in (let TMP_7 \def (f x1 x2) in (let 
TMP_8 \def (refl_equal B TMP_7) in (eq_ind A2 x2 TMP_6 TMP_8 y2 H0))))) in 
(eq_ind A1 x1 TMP_3 TMP_9 y1 H))))))))))).

theorem f_equal3:
 \forall (A1: Type[0]).(\forall (A2: Type[0]).(\forall (A3: Type[0]).(\forall 
(B: Type[0]).(\forall (f: ((A1 \to (A2 \to (A3 \to B))))).(\forall (x1: 
A1).(\forall (y1: A1).(\forall (x2: A2).(\forall (y2: A2).(\forall (x3: 
A3).(\forall (y3: A3).((eq A1 x1 y1) \to ((eq A2 x2 y2) \to ((eq A3 x3 y3) 
\to (eq B (f x1 x2 x3) (f y1 y2 y3)))))))))))))))
\def
 \lambda (A1: Type[0]).(\lambda (A2: Type[0]).(\lambda (A3: Type[0]).(\lambda 
(B: Type[0]).(\lambda (f: ((A1 \to (A2 \to (A3 \to B))))).(\lambda (x1: 
A1).(\lambda (y1: A1).(\lambda (x2: A2).(\lambda (y2: A2).(\lambda (x3: 
A3).(\lambda (y3: A3).(\lambda (H: (eq A1 x1 y1)).(let TMP_3 \def (\lambda 
(a: A1).((eq A2 x2 y2) \to ((eq A3 x3 y3) \to (let TMP_1 \def (f x1 x2 x3) in 
(let TMP_2 \def (f a y2 y3) in (eq B TMP_1 TMP_2)))))) in (let TMP_13 \def 
(\lambda (H0: (eq A2 x2 y2)).(let TMP_6 \def (\lambda (a: A2).((eq A3 x3 y3) 
\to (let TMP_4 \def (f x1 x2 x3) in (let TMP_5 \def (f x1 a y3) in (eq B 
TMP_4 TMP_5))))) in (let TMP_12 \def (\lambda (H1: (eq A3 x3 y3)).(let TMP_9 
\def (\lambda (a: A3).(let TMP_7 \def (f x1 x2 x3) in (let TMP_8 \def (f x1 
x2 a) in (eq B TMP_7 TMP_8)))) in (let TMP_10 \def (f x1 x2 x3) in (let 
TMP_11 \def (refl_equal B TMP_10) in (eq_ind A3 x3 TMP_9 TMP_11 y3 H1))))) in 
(eq_ind A2 x2 TMP_6 TMP_12 y2 H0)))) in (eq_ind A1 x1 TMP_3 TMP_13 y1 
H)))))))))))))).

theorem sym_eq:
 \forall (A: Type[0]).(\forall (x: A).(\forall (y: A).((eq A x y) \to (eq A y 
x))))
\def
 \lambda (A: Type[0]).(\lambda (x: A).(\lambda (y: A).(\lambda (H: (eq A x 
y)).(let TMP_1 \def (\lambda (a: A).(eq A a x)) in (let TMP_2 \def 
(refl_equal A x) in (eq_ind A x TMP_1 TMP_2 y H)))))).

theorem eq_ind_r:
 \forall (A: Type[0]).(\forall (x: A).(\forall (P: ((A \to Prop))).((P x) \to 
(\forall (y: A).((eq A y x) \to (P y))))))
\def
 \lambda (A: Type[0]).(\lambda (x: A).(\lambda (P: ((A \to Prop))).(\lambda 
(H: (P x)).(\lambda (y: A).(\lambda (H0: (eq A y x)).(let TMP_1 \def (sym_eq 
A y x H0) in (match TMP_1 with [refl_equal \Rightarrow H]))))))).

theorem trans_eq:
 \forall (A: Type[0]).(\forall (x: A).(\forall (y: A).(\forall (z: A).((eq A 
x y) \to ((eq A y z) \to (eq A x z))))))
\def
 \lambda (A: Type[0]).(\lambda (x: A).(\lambda (y: A).(\lambda (z: 
A).(\lambda (H: (eq A x y)).(\lambda (H0: (eq A y z)).(let TMP_1 \def 
(\lambda (a: A).(eq A x a)) in (eq_ind A y TMP_1 H z H0))))))).

theorem sym_not_eq:
 \forall (A: Type[0]).(\forall (x: A).(\forall (y: A).((not (eq A x y)) \to 
(not (eq A y x)))))
\def
 \lambda (A: Type[0]).(\lambda (x: A).(\lambda (y: A).(\lambda (h1: (not (eq 
A x y))).(\lambda (h2: (eq A y x)).(let TMP_1 \def (\lambda (a: A).(eq A a 
y)) in (let TMP_2 \def (refl_equal A y) in (let TMP_3 \def (eq_ind A y TMP_1 
TMP_2 x h2) in (h1 TMP_3)))))))).

theorem nat_double_ind:
 \forall (R: ((nat \to (nat \to Prop)))).(((\forall (n: nat).(R O n))) \to 
(((\forall (n: nat).(R (S n) O))) \to (((\forall (n: nat).(\forall (m: 
nat).((R n m) \to (R (S n) (S m)))))) \to (\forall (n: nat).(\forall (m: 
nat).(R n m))))))
\def
 \lambda (R: ((nat \to (nat \to Prop)))).(\lambda (H: ((\forall (n: nat).(R O 
n)))).(\lambda (H0: ((\forall (n: nat).(R (S n) O)))).(\lambda (H1: ((\forall 
(n: nat).(\forall (m: nat).((R n m) \to (R (S n) (S m))))))).(\lambda (n: 
nat).(let TMP_1 \def (\lambda (n0: nat).(\forall (m: nat).(R n0 m))) in (let 
TMP_7 \def (\lambda (n0: nat).(\lambda (H2: ((\forall (m: nat).(R n0 
m)))).(\lambda (m: nat).(let TMP_3 \def (\lambda (n1: nat).(let TMP_2 \def (S 
n0) in (R TMP_2 n1))) in (let TMP_4 \def (H0 n0) in (let TMP_6 \def (\lambda 
(n1: nat).(\lambda (_: (R (S n0) n1)).(let TMP_5 \def (H2 n1) in (H1 n0 n1 
TMP_5)))) in (nat_ind TMP_3 TMP_4 TMP_6 m))))))) in (nat_ind TMP_1 H TMP_7 
n))))))).

theorem eq_add_S:
 \forall (n: nat).(\forall (m: nat).((eq nat (S n) (S m)) \to (eq nat n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (eq nat (S n) (S m))).(let 
TMP_1 \def (S n) in (let TMP_2 \def (S m) in (f_equal nat nat pred TMP_1 
TMP_2 H))))).

theorem O_S:
 \forall (n: nat).(not (eq nat O (S n)))
\def
 \lambda (n: nat).(\lambda (H: (eq nat O (S n))).(let TMP_1 \def (S n) in 
(let TMP_2 \def (\lambda (n0: nat).(IsSucc n0)) in (let TMP_3 \def (S n) in 
(let TMP_4 \def (sym_eq nat O TMP_3 H) in (eq_ind nat TMP_1 TMP_2 I O 
TMP_4)))))).

theorem not_eq_S:
 \forall (n: nat).(\forall (m: nat).((not (eq nat n m)) \to (not (eq nat (S 
n) (S m)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (not (eq nat n m))).(\lambda 
(H0: (eq nat (S n) (S m))).(let TMP_1 \def (eq_add_S n m H0) in (H TMP_1))))).

theorem pred_Sn:
 \forall (m: nat).(eq nat m (pred (S m)))
\def
 \lambda (m: nat).(let TMP_1 \def (S m) in (let TMP_2 \def (pred TMP_1) in 
(refl_equal nat TMP_2))).

theorem S_pred:
 \forall (n: nat).(\forall (m: nat).((lt m n) \to (eq nat n (S (pred n)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt m n)).(let TMP_1 \def (S 
m) in (let TMP_4 \def (\lambda (n0: nat).(let TMP_2 \def (pred n0) in (let 
TMP_3 \def (S TMP_2) in (eq nat n0 TMP_3)))) in (let TMP_5 \def (S m) in (let 
TMP_6 \def (pred TMP_5) in (let TMP_7 \def (S TMP_6) in (let TMP_8 \def 
(refl_equal nat TMP_7) in (let TMP_12 \def (\lambda (m0: nat).(\lambda (_: 
(le (S m) m0)).(\lambda (_: (eq nat m0 (S (pred m0)))).(let TMP_9 \def (S m0) 
in (let TMP_10 \def (pred TMP_9) in (let TMP_11 \def (S TMP_10) in 
(refl_equal nat TMP_11))))))) in (le_ind TMP_1 TMP_4 TMP_8 TMP_12 n 
H)))))))))).

theorem le_trans:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((le n m) \to ((le m p) 
\to (le n p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (le n 
m)).(\lambda (H0: (le m p)).(let TMP_1 \def (\lambda (n0: nat).(le n n0)) in 
(let TMP_2 \def (\lambda (m0: nat).(\lambda (_: (le m m0)).(\lambda (IHle: 
(le n m0)).(le_S n m0 IHle)))) in (le_ind m TMP_1 H TMP_2 p H0))))))).

theorem le_trans_S:
 \forall (n: nat).(\forall (m: nat).((le (S n) m) \to (le n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le (S n) m)).(let TMP_1 
\def (S n) in (let TMP_2 \def (le_n n) in (let TMP_3 \def (le_S n n TMP_2) in 
(le_trans n TMP_1 m TMP_3 H)))))).

theorem le_n_S:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (le (S n) (S m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(let TMP_3 \def 
(\lambda (n0: nat).(let TMP_1 \def (S n) in (let TMP_2 \def (S n0) in (le 
TMP_1 TMP_2)))) in (let TMP_4 \def (S n) in (let TMP_5 \def (le_n TMP_4) in 
(let TMP_8 \def (\lambda (m0: nat).(\lambda (_: (le n m0)).(\lambda (IHle: 
(le (S n) (S m0))).(let TMP_6 \def (S n) in (let TMP_7 \def (S m0) in (le_S 
TMP_6 TMP_7 IHle)))))) in (le_ind n TMP_3 TMP_5 TMP_8 m H))))))).

theorem le_O_n:
 \forall (n: nat).(le O n)
\def
 \lambda (n: nat).(let TMP_1 \def (\lambda (n0: nat).(le O n0)) in (let TMP_2 
\def (le_n O) in (let TMP_3 \def (\lambda (n0: nat).(\lambda (IHn: (le O 
n0)).(le_S O n0 IHn))) in (nat_ind TMP_1 TMP_2 TMP_3 n)))).

theorem le_S_n:
 \forall (n: nat).(\forall (m: nat).((le (S n) (S m)) \to (le n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le (S n) (S m))).(let TMP_1 
\def (S n) in (let TMP_5 \def (\lambda (n0: nat).(let TMP_2 \def (S n) in 
(let TMP_3 \def (pred TMP_2) in (let TMP_4 \def (pred n0) in (le TMP_3 
TMP_4))))) in (let TMP_6 \def (le_n n) in (let TMP_7 \def (\lambda (m0: 
nat).(\lambda (H0: (le (S n) m0)).(\lambda (_: (le n (pred m0))).(le_trans_S 
n m0 H0)))) in (let TMP_8 \def (S m) in (le_ind TMP_1 TMP_5 TMP_6 TMP_7 TMP_8 
H)))))))).

theorem le_Sn_O:
 \forall (n: nat).(not (le (S n) O))
\def
 \lambda (n: nat).(\lambda (H: (le (S n) O)).(let TMP_1 \def (S n) in (let 
TMP_2 \def (\lambda (n0: nat).(IsSucc n0)) in (let TMP_3 \def (\lambda (m: 
nat).(\lambda (_: (le (S n) m)).(\lambda (_: (IsSucc m)).I))) in (le_ind 
TMP_1 TMP_2 I TMP_3 O H))))).

theorem le_Sn_n:
 \forall (n: nat).(not (le (S n) n))
\def
 \lambda (n: nat).(let TMP_3 \def (\lambda (n0: nat).(let TMP_1 \def (S n0) 
in (let TMP_2 \def (le TMP_1 n0) in (not TMP_2)))) in (let TMP_4 \def 
(le_Sn_O O) in (let TMP_7 \def (\lambda (n0: nat).(\lambda (IHn: (not (le (S 
n0) n0))).(\lambda (H: (le (S (S n0)) (S n0))).(let TMP_5 \def (S n0) in (let 
TMP_6 \def (le_S_n TMP_5 n0 H) in (IHn TMP_6)))))) in (nat_ind TMP_3 TMP_4 
TMP_7 n)))).

theorem le_antisym:
 \forall (n: nat).(\forall (m: nat).((le n m) \to ((le m n) \to (eq nat n 
m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (h: (le n m)).(let TMP_1 \def 
(\lambda (n0: nat).((le n0 n) \to (eq nat n n0))) in (let TMP_2 \def (\lambda 
(_: (le n n)).(refl_equal nat n)) in (let TMP_8 \def (\lambda (m0: 
nat).(\lambda (H: (le n m0)).(\lambda (_: (((le m0 n) \to (eq nat n 
m0)))).(\lambda (H1: (le (S m0) n)).(let TMP_3 \def (S m0) in (let TMP_4 \def 
(eq nat n TMP_3) in (let TMP_5 \def (S m0) in (let H2 \def (le_trans TMP_5 n 
m0 H1 H) in (let H3 \def (le_Sn_n m0) in (let TMP_6 \def (\lambda (H4: (le (S 
m0) m0)).(H3 H4)) in (let TMP_7 \def (TMP_6 H2) in (False_ind TMP_4 
TMP_7)))))))))))) in (le_ind n TMP_1 TMP_2 TMP_8 m h)))))).

theorem le_n_O_eq:
 \forall (n: nat).((le n O) \to (eq nat O n))
\def
 \lambda (n: nat).(\lambda (H: (le n O)).(let TMP_1 \def (le_O_n n) in 
(le_antisym O n TMP_1 H))).

theorem le_elim_rel:
 \forall (P: ((nat \to (nat \to Prop)))).(((\forall (p: nat).(P O p))) \to 
(((\forall (p: nat).(\forall (q: nat).((le p q) \to ((P p q) \to (P (S p) (S 
q))))))) \to (\forall (n: nat).(\forall (m: nat).((le n m) \to (P n m))))))
\def
 \lambda (P: ((nat \to (nat \to Prop)))).(\lambda (H: ((\forall (p: nat).(P O 
p)))).(\lambda (H0: ((\forall (p: nat).(\forall (q: nat).((le p q) \to ((P p 
q) \to (P (S p) (S q)))))))).(\lambda (n: nat).(let TMP_1 \def (\lambda (n0: 
nat).(\forall (m: nat).((le n0 m) \to (P n0 m)))) in (let TMP_2 \def (\lambda 
(m: nat).(\lambda (_: (le O m)).(H m))) in (let TMP_14 \def (\lambda (n0: 
nat).(\lambda (IHn: ((\forall (m: nat).((le n0 m) \to (P n0 m))))).(\lambda 
(m: nat).(\lambda (Le: (le (S n0) m)).(let TMP_3 \def (S n0) in (let TMP_5 
\def (\lambda (n1: nat).(let TMP_4 \def (S n0) in (P TMP_4 n1))) in (let 
TMP_6 \def (le_n n0) in (let TMP_7 \def (le_n n0) in (let TMP_8 \def (IHn n0 
TMP_7) in (let TMP_9 \def (H0 n0 n0 TMP_6 TMP_8) in (let TMP_13 \def (\lambda 
(m0: nat).(\lambda (H1: (le (S n0) m0)).(\lambda (_: (P (S n0) m0)).(let 
TMP_10 \def (le_trans_S n0 m0 H1) in (let TMP_11 \def (le_trans_S n0 m0 H1) 
in (let TMP_12 \def (IHn m0 TMP_11) in (H0 n0 m0 TMP_10 TMP_12))))))) in 
(le_ind TMP_3 TMP_5 TMP_9 TMP_13 m Le)))))))))))) in (nat_ind TMP_1 TMP_2 
TMP_14 n))))))).

theorem lt_n_n:
 \forall (n: nat).(not (lt n n))
\def
 le_Sn_n.

theorem lt_n_S:
 \forall (n: nat).(\forall (m: nat).((lt n m) \to (lt (S n) (S m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt n m)).(let TMP_1 \def (S 
n) in (le_n_S TMP_1 m H)))).

theorem lt_n_Sn:
 \forall (n: nat).(lt n (S n))
\def
 \lambda (n: nat).(let TMP_1 \def (S n) in (le_n TMP_1)).

theorem lt_S_n:
 \forall (n: nat).(\forall (m: nat).((lt (S n) (S m)) \to (lt n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt (S n) (S m))).(let TMP_1 
\def (S n) in (le_S_n TMP_1 m H)))).

theorem lt_n_O:
 \forall (n: nat).(not (lt n O))
\def
 le_Sn_O.

theorem lt_trans:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((lt n m) \to ((lt m p) 
\to (lt n p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (lt n 
m)).(\lambda (H0: (lt m p)).(let TMP_1 \def (S m) in (let TMP_2 \def (\lambda 
(n0: nat).(lt n n0)) in (let TMP_3 \def (S n) in (let TMP_4 \def (le_S TMP_3 
m H) in (let TMP_6 \def (\lambda (m0: nat).(\lambda (_: (le (S m) 
m0)).(\lambda (IHle: (lt n m0)).(let TMP_5 \def (S n) in (le_S TMP_5 m0 
IHle))))) in (le_ind TMP_1 TMP_2 TMP_4 TMP_6 p H0)))))))))).

theorem lt_O_Sn:
 \forall (n: nat).(lt O (S n))
\def
 \lambda (n: nat).(let TMP_1 \def (le_O_n n) in (le_n_S O n TMP_1)).

theorem lt_le_S:
 \forall (n: nat).(\forall (p: nat).((lt n p) \to (le (S n) p)))
\def
 \lambda (n: nat).(\lambda (p: nat).(\lambda (H: (lt n p)).H)).

theorem le_not_lt:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (not (lt m n))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(let TMP_2 \def 
(\lambda (n0: nat).(let TMP_1 \def (lt n0 n) in (not TMP_1))) in (let TMP_3 
\def (lt_n_n n) in (let TMP_6 \def (\lambda (m0: nat).(\lambda (_: (le n 
m0)).(\lambda (IHle: (not (lt m0 n))).(\lambda (H1: (lt (S m0) n)).(let TMP_4 
\def (S m0) in (let TMP_5 \def (le_trans_S TMP_4 n H1) in (IHle TMP_5))))))) 
in (le_ind n TMP_2 TMP_3 TMP_6 m H)))))).

theorem le_lt_n_Sm:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (lt n (S m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(le_n_S n m H))).

theorem le_lt_trans:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((le n m) \to ((lt m p) 
\to (lt n p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (le n 
m)).(\lambda (H0: (lt m p)).(let TMP_1 \def (S m) in (let TMP_2 \def (\lambda 
(n0: nat).(lt n n0)) in (let TMP_3 \def (le_n_S n m H) in (let TMP_5 \def 
(\lambda (m0: nat).(\lambda (_: (le (S m) m0)).(\lambda (IHle: (lt n 
m0)).(let TMP_4 \def (S n) in (le_S TMP_4 m0 IHle))))) in (le_ind TMP_1 TMP_2 
TMP_3 TMP_5 p H0))))))))).

theorem lt_le_trans:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((lt n m) \to ((le m p) 
\to (lt n p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (lt n 
m)).(\lambda (H0: (le m p)).(let TMP_1 \def (\lambda (n0: nat).(lt n n0)) in 
(let TMP_3 \def (\lambda (m0: nat).(\lambda (_: (le m m0)).(\lambda (IHle: 
(lt n m0)).(let TMP_2 \def (S n) in (le_S TMP_2 m0 IHle))))) in (le_ind m 
TMP_1 H TMP_3 p H0))))))).

theorem lt_le_weak:
 \forall (n: nat).(\forall (m: nat).((lt n m) \to (le n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt n m)).(le_trans_S n m 
H))).

theorem lt_n_Sm_le:
 \forall (n: nat).(\forall (m: nat).((lt n (S m)) \to (le n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt n (S m))).(le_S_n n m 
H))).

theorem le_lt_or_eq:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (or (lt n m) (eq nat n m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(let TMP_3 \def 
(\lambda (n0: nat).(let TMP_1 \def (lt n n0) in (let TMP_2 \def (eq nat n n0) 
in (or TMP_1 TMP_2)))) in (let TMP_4 \def (lt n n) in (let TMP_5 \def (eq nat 
n n) in (let TMP_6 \def (refl_equal nat n) in (let TMP_7 \def (or_intror 
TMP_4 TMP_5 TMP_6) in (let TMP_13 \def (\lambda (m0: nat).(\lambda (H0: (le n 
m0)).(\lambda (_: (or (lt n m0) (eq nat n m0))).(let TMP_8 \def (S m0) in 
(let TMP_9 \def (lt n TMP_8) in (let TMP_10 \def (S m0) in (let TMP_11 \def 
(eq nat n TMP_10) in (let TMP_12 \def (le_n_S n m0 H0) in (or_introl TMP_9 
TMP_11 TMP_12))))))))) in (le_ind n TMP_3 TMP_7 TMP_13 m H))))))))).

theorem le_or_lt:
 \forall (n: nat).(\forall (m: nat).(or (le n m) (lt m n)))
\def
 \lambda (n: nat).(\lambda (m: nat).(let TMP_3 \def (\lambda (n0: 
nat).(\lambda (n1: nat).(let TMP_1 \def (le n0 n1) in (let TMP_2 \def (lt n1 
n0) in (or TMP_1 TMP_2))))) in (let TMP_7 \def (\lambda (n0: nat).(let TMP_4 
\def (le O n0) in (let TMP_5 \def (lt n0 O) in (let TMP_6 \def (le_O_n n0) in 
(or_introl TMP_4 TMP_5 TMP_6))))) in (let TMP_15 \def (\lambda (n0: nat).(let 
TMP_8 \def (S n0) in (let TMP_9 \def (le TMP_8 O) in (let TMP_10 \def (S n0) 
in (let TMP_11 \def (lt O TMP_10) in (let TMP_12 \def (S n0) in (let TMP_13 
\def (lt_O_Sn n0) in (let TMP_14 \def (lt_le_S O TMP_12 TMP_13) in (or_intror 
TMP_9 TMP_11 TMP_14))))))))) in (let TMP_42 \def (\lambda (n0: nat).(\lambda 
(m0: nat).(\lambda (H: (or (le n0 m0) (lt m0 n0))).(let TMP_16 \def (le n0 
m0) in (let TMP_17 \def (lt m0 n0) in (let TMP_18 \def (S n0) in (let TMP_19 
\def (S m0) in (let TMP_20 \def (le TMP_18 TMP_19) in (let TMP_21 \def (S m0) 
in (let TMP_22 \def (S n0) in (let TMP_23 \def (lt TMP_21 TMP_22) in (let 
TMP_24 \def (or TMP_20 TMP_23) in (let TMP_32 \def (\lambda (H0: (le n0 
m0)).(let TMP_25 \def (S n0) in (let TMP_26 \def (S m0) in (let TMP_27 \def 
(le TMP_25 TMP_26) in (let TMP_28 \def (S m0) in (let TMP_29 \def (S n0) in 
(let TMP_30 \def (lt TMP_28 TMP_29) in (let TMP_31 \def (le_n_S n0 m0 H0) in 
(or_introl TMP_27 TMP_30 TMP_31))))))))) in (let TMP_41 \def (\lambda (H0: 
(lt m0 n0)).(let TMP_33 \def (S n0) in (let TMP_34 \def (S m0) in (let TMP_35 
\def (le TMP_33 TMP_34) in (let TMP_36 \def (S m0) in (let TMP_37 \def (S n0) 
in (let TMP_38 \def (lt TMP_36 TMP_37) in (let TMP_39 \def (S m0) in (let 
TMP_40 \def (le_n_S TMP_39 n0 H0) in (or_intror TMP_35 TMP_38 
TMP_40)))))))))) in (or_ind TMP_16 TMP_17 TMP_24 TMP_32 TMP_41 
H))))))))))))))) in (nat_double_ind TMP_3 TMP_7 TMP_15 TMP_42 n m)))))).

theorem plus_n_O:
 \forall (n: nat).(eq nat n (plus n O))
\def
 \lambda (n: nat).(let TMP_2 \def (\lambda (n0: nat).(let TMP_1 \def (plus n0 
O) in (eq nat n0 TMP_1))) in (let TMP_3 \def (refl_equal nat O) in (let TMP_5 
\def (\lambda (n0: nat).(\lambda (H: (eq nat n0 (plus n0 O))).(let TMP_4 \def 
(plus n0 O) in (f_equal nat nat S n0 TMP_4 H)))) in (nat_ind TMP_2 TMP_3 
TMP_5 n)))).

theorem plus_n_Sm:
 \forall (n: nat).(\forall (m: nat).(eq nat (S (plus n m)) (plus n (S m))))
\def
 \lambda (m: nat).(\lambda (n: nat).(let TMP_5 \def (\lambda (n0: nat).(let 
TMP_1 \def (plus n0 n) in (let TMP_2 \def (S TMP_1) in (let TMP_3 \def (S n) 
in (let TMP_4 \def (plus n0 TMP_3) in (eq nat TMP_2 TMP_4)))))) in (let TMP_6 
\def (S n) in (let TMP_7 \def (refl_equal nat TMP_6) in (let TMP_12 \def 
(\lambda (n0: nat).(\lambda (H: (eq nat (S (plus n0 n)) (plus n0 (S 
n)))).(let TMP_8 \def (plus n0 n) in (let TMP_9 \def (S TMP_8) in (let TMP_10 
\def (S n) in (let TMP_11 \def (plus n0 TMP_10) in (f_equal nat nat S TMP_9 
TMP_11 H))))))) in (nat_ind TMP_5 TMP_7 TMP_12 m)))))).

theorem plus_sym:
 \forall (n: nat).(\forall (m: nat).(eq nat (plus n m) (plus m n)))
\def
 \lambda (n: nat).(\lambda (m: nat).(let TMP_3 \def (\lambda (n0: nat).(let 
TMP_1 \def (plus n0 m) in (let TMP_2 \def (plus m n0) in (eq nat TMP_1 
TMP_2)))) in (let TMP_4 \def (plus_n_O m) in (let TMP_16 \def (\lambda (y: 
nat).(\lambda (H: (eq nat (plus y m) (plus m y))).(let TMP_5 \def (plus m y) 
in (let TMP_6 \def (S TMP_5) in (let TMP_9 \def (\lambda (n0: nat).(let TMP_7 
\def (plus y m) in (let TMP_8 \def (S TMP_7) in (eq nat TMP_8 n0)))) in (let 
TMP_10 \def (plus y m) in (let TMP_11 \def (plus m y) in (let TMP_12 \def 
(f_equal nat nat S TMP_10 TMP_11 H) in (let TMP_13 \def (S y) in (let TMP_14 
\def (plus m TMP_13) in (let TMP_15 \def (plus_n_Sm m y) in (eq_ind nat TMP_6 
TMP_9 TMP_12 TMP_14 TMP_15)))))))))))) in (nat_ind TMP_3 TMP_4 TMP_16 n))))).

theorem plus_Snm_nSm:
 \forall (n: nat).(\forall (m: nat).(eq nat (plus (S n) m) (plus n (S m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(let TMP_1 \def (plus m n) in (let TMP_5 
\def (\lambda (n0: nat).(let TMP_2 \def (S n0) in (let TMP_3 \def (S m) in 
(let TMP_4 \def (plus n TMP_3) in (eq nat TMP_2 TMP_4))))) in (let TMP_6 \def 
(S m) in (let TMP_7 \def (plus TMP_6 n) in (let TMP_10 \def (\lambda (n0: 
nat).(let TMP_8 \def (plus m n) in (let TMP_9 \def (S TMP_8) in (eq nat TMP_9 
n0)))) in (let TMP_11 \def (S m) in (let TMP_12 \def (plus TMP_11 n) in (let 
TMP_13 \def (refl_equal nat TMP_12) in (let TMP_14 \def (S m) in (let TMP_15 
\def (plus n TMP_14) in (let TMP_16 \def (S m) in (let TMP_17 \def (plus_sym 
n TMP_16) in (let TMP_18 \def (eq_ind_r nat TMP_7 TMP_10 TMP_13 TMP_15 
TMP_17) in (let TMP_19 \def (plus n m) in (let TMP_20 \def (plus_sym n m) in 
(eq_ind_r nat TMP_1 TMP_5 TMP_18 TMP_19 TMP_20))))))))))))))))).

theorem plus_assoc_l:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(eq nat (plus n (plus m 
p)) (plus (plus n m) p))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(let TMP_5 \def 
(\lambda (n0: nat).(let TMP_1 \def (plus m p) in (let TMP_2 \def (plus n0 
TMP_1) in (let TMP_3 \def (plus n0 m) in (let TMP_4 \def (plus TMP_3 p) in 
(eq nat TMP_2 TMP_4)))))) in (let TMP_6 \def (plus m p) in (let TMP_7 \def 
(refl_equal nat TMP_6) in (let TMP_12 \def (\lambda (n0: nat).(\lambda (H: 
(eq nat (plus n0 (plus m p)) (plus (plus n0 m) p))).(let TMP_8 \def (plus m 
p) in (let TMP_9 \def (plus n0 TMP_8) in (let TMP_10 \def (plus n0 m) in (let 
TMP_11 \def (plus TMP_10 p) in (f_equal nat nat S TMP_9 TMP_11 H))))))) in 
(nat_ind TMP_5 TMP_7 TMP_12 n))))))).

theorem plus_assoc_r:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(eq nat (plus (plus n 
m) p) (plus n (plus m p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(let TMP_1 \def (plus m 
p) in (let TMP_2 \def (plus n TMP_1) in (let TMP_3 \def (plus n m) in (let 
TMP_4 \def (plus TMP_3 p) in (let TMP_5 \def (plus_assoc_l n m p) in (sym_eq 
nat TMP_2 TMP_4 TMP_5)))))))).

theorem simpl_plus_l:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((eq nat (plus n m) 
(plus n p)) \to (eq nat m p))))
\def
 \lambda (n: nat).(let TMP_1 \def (\lambda (n0: nat).(\forall (m: 
nat).(\forall (p: nat).((eq nat (plus n0 m) (plus n0 p)) \to (eq nat m p))))) 
in (let TMP_2 \def (\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (eq nat m 
p)).H))) in (let TMP_13 \def (\lambda (n0: nat).(\lambda (IHn: ((\forall (m: 
nat).(\forall (p: nat).((eq nat (plus n0 m) (plus n0 p)) \to (eq nat m 
p)))))).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (eq nat (S (plus n0 
m)) (S (plus n0 p)))).(let TMP_3 \def (plus n0 m) in (let TMP_4 \def (plus n0 
p) in (let TMP_5 \def (plus n0) in (let TMP_6 \def (plus n0 m) in (let TMP_7 
\def (plus n0 p) in (let TMP_8 \def (plus n0 m) in (let TMP_9 \def (plus n0 
p) in (let TMP_10 \def (eq_add_S TMP_8 TMP_9 H) in (let TMP_11 \def (f_equal 
nat nat TMP_5 TMP_6 TMP_7 TMP_10) in (let TMP_12 \def (IHn TMP_3 TMP_4 
TMP_11) in (IHn m p TMP_12)))))))))))))))) in (nat_ind TMP_1 TMP_2 TMP_13 
n)))).

theorem minus_n_O:
 \forall (n: nat).(eq nat n (minus n O))
\def
 \lambda (n: nat).(let TMP_2 \def (\lambda (n0: nat).(let TMP_1 \def (minus 
n0 O) in (eq nat n0 TMP_1))) in (let TMP_3 \def (refl_equal nat O) in (let 
TMP_5 \def (\lambda (n0: nat).(\lambda (_: (eq nat n0 (minus n0 O))).(let 
TMP_4 \def (S n0) in (refl_equal nat TMP_4)))) in (nat_ind TMP_2 TMP_3 TMP_5 
n)))).

theorem minus_n_n:
 \forall (n: nat).(eq nat O (minus n n))
\def
 \lambda (n: nat).(let TMP_2 \def (\lambda (n0: nat).(let TMP_1 \def (minus 
n0 n0) in (eq nat O TMP_1))) in (let TMP_3 \def (refl_equal nat O) in (let 
TMP_4 \def (\lambda (n0: nat).(\lambda (IHn: (eq nat O (minus n0 n0))).IHn)) 
in (nat_ind TMP_2 TMP_3 TMP_4 n)))).

theorem minus_Sn_m:
 \forall (n: nat).(\forall (m: nat).((le m n) \to (eq nat (S (minus n m)) 
(minus (S n) m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (Le: (le m n)).(let TMP_5 \def 
(\lambda (n0: nat).(\lambda (n1: nat).(let TMP_1 \def (minus n1 n0) in (let 
TMP_2 \def (S TMP_1) in (let TMP_3 \def (S n1) in (let TMP_4 \def (minus 
TMP_3 n0) in (eq nat TMP_2 TMP_4))))))) in (let TMP_10 \def (\lambda (p: 
nat).(let TMP_6 \def (minus p O) in (let TMP_7 \def (minus p O) in (let TMP_8 
\def (minus_n_O p) in (let TMP_9 \def (sym_eq nat p TMP_7 TMP_8) in (f_equal 
nat nat S TMP_6 p TMP_9)))))) in (let TMP_11 \def (\lambda (p: nat).(\lambda 
(q: nat).(\lambda (_: (le p q)).(\lambda (H0: (eq nat (S (minus q p)) (match 
p with [O \Rightarrow (S q) | (S l) \Rightarrow (minus q l)]))).H0)))) in 
(le_elim_rel TMP_5 TMP_10 TMP_11 m n Le)))))).

theorem plus_minus:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((eq nat n (plus m p)) 
\to (eq nat p (minus n m)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(let TMP_2 \def 
(\lambda (n0: nat).(\lambda (n1: nat).((eq nat n1 (plus n0 p)) \to (let TMP_1 
\def (minus n1 n0) in (eq nat p TMP_1))))) in (let TMP_7 \def (\lambda (n0: 
nat).(\lambda (H: (eq nat n0 p)).(let TMP_3 \def (\lambda (n1: nat).(eq nat p 
n1)) in (let TMP_4 \def (sym_eq nat n0 p H) in (let TMP_5 \def (minus n0 O) 
in (let TMP_6 \def (minus_n_O n0) in (eq_ind nat n0 TMP_3 TMP_4 TMP_5 
TMP_6))))))) in (let TMP_12 \def (\lambda (n0: nat).(\lambda (H: (eq nat O (S 
(plus n0 p)))).(let TMP_8 \def (eq nat p O) in (let H0 \def H in (let TMP_9 
\def (plus n0 p) in (let H1 \def (O_S TMP_9) in (let TMP_10 \def (\lambda 
(H2: (eq nat O (S (plus n0 p)))).(H1 H2)) in (let TMP_11 \def (TMP_10 H0) in 
(False_ind TMP_8 TMP_11))))))))) in (let TMP_15 \def (\lambda (n0: 
nat).(\lambda (m0: nat).(\lambda (H: (((eq nat m0 (plus n0 p)) \to (eq nat p 
(minus m0 n0))))).(\lambda (H0: (eq nat (S m0) (S (plus n0 p)))).(let TMP_13 
\def (plus n0 p) in (let TMP_14 \def (eq_add_S m0 TMP_13 H0) in (H 
TMP_14))))))) in (nat_double_ind TMP_2 TMP_7 TMP_12 TMP_15 m n))))))).

theorem minus_plus:
 \forall (n: nat).(\forall (m: nat).(eq nat (minus (plus n m) n) m))
\def
 \lambda (n: nat).(\lambda (m: nat).(let TMP_1 \def (plus n m) in (let TMP_2 
\def (minus TMP_1 n) in (let TMP_3 \def (plus n m) in (let TMP_4 \def (plus n 
m) in (let TMP_5 \def (refl_equal nat TMP_4) in (let TMP_6 \def (plus_minus 
TMP_3 n m TMP_5) in (sym_eq nat m TMP_2 TMP_6)))))))).

theorem le_pred_n:
 \forall (n: nat).(le (pred n) n)
\def
 \lambda (n: nat).(let TMP_2 \def (\lambda (n0: nat).(let TMP_1 \def (pred 
n0) in (le TMP_1 n0))) in (let TMP_3 \def (le_n O) in (let TMP_7 \def 
(\lambda (n0: nat).(\lambda (_: (le (pred n0) n0)).(let TMP_4 \def (S n0) in 
(let TMP_5 \def (pred TMP_4) in (let TMP_6 \def (le_n n0) in (le_S TMP_5 n0 
TMP_6)))))) in (nat_ind TMP_2 TMP_3 TMP_7 n)))).

theorem le_plus_l:
 \forall (n: nat).(\forall (m: nat).(le n (plus n m)))
\def
 \lambda (n: nat).(let TMP_2 \def (\lambda (n0: nat).(\forall (m: nat).(let 
TMP_1 \def (plus n0 m) in (le n0 TMP_1)))) in (let TMP_3 \def (\lambda (m: 
nat).(le_O_n m)) in (let TMP_6 \def (\lambda (n0: nat).(\lambda (IHn: 
((\forall (m: nat).(le n0 (plus n0 m))))).(\lambda (m: nat).(let TMP_4 \def 
(plus n0 m) in (let TMP_5 \def (IHn m) in (le_n_S n0 TMP_4 TMP_5)))))) in 
(nat_ind TMP_2 TMP_3 TMP_6 n)))).

theorem le_plus_r:
 \forall (n: nat).(\forall (m: nat).(le m (plus n m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(let TMP_2 \def (\lambda (n0: nat).(let 
TMP_1 \def (plus n0 m) in (le m TMP_1))) in (let TMP_3 \def (le_n m) in (let 
TMP_5 \def (\lambda (n0: nat).(\lambda (H: (le m (plus n0 m))).(let TMP_4 
\def (plus n0 m) in (le_S m TMP_4 H)))) in (nat_ind TMP_2 TMP_3 TMP_5 n))))).

theorem simpl_le_plus_l:
 \forall (p: nat).(\forall (n: nat).(\forall (m: nat).((le (plus p n) (plus p 
m)) \to (le n m))))
\def
 \lambda (p: nat).(let TMP_1 \def (\lambda (n: nat).(\forall (n0: 
nat).(\forall (m: nat).((le (plus n n0) (plus n m)) \to (le n0 m))))) in (let 
TMP_2 \def (\lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).H))) in 
(let TMP_6 \def (\lambda (p0: nat).(\lambda (IHp: ((\forall (n: nat).(\forall 
(m: nat).((le (plus p0 n) (plus p0 m)) \to (le n m)))))).(\lambda (n: 
nat).(\lambda (m: nat).(\lambda (H: (le (S (plus p0 n)) (S (plus p0 
m)))).(let TMP_3 \def (plus p0 n) in (let TMP_4 \def (plus p0 m) in (let 
TMP_5 \def (le_S_n TMP_3 TMP_4 H) in (IHp n m TMP_5))))))))) in (nat_ind 
TMP_1 TMP_2 TMP_6 p)))).

theorem le_plus_trans:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((le n m) \to (le n 
(plus m p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (le n 
m)).(let TMP_1 \def (plus m p) in (let TMP_2 \def (le_plus_l m p) in 
(le_trans n m TMP_1 H TMP_2)))))).

theorem le_reg_l:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((le n m) \to (le (plus 
p n) (plus p m)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(let TMP_3 \def 
(\lambda (n0: nat).((le n m) \to (let TMP_1 \def (plus n0 n) in (let TMP_2 
\def (plus n0 m) in (le TMP_1 TMP_2))))) in (let TMP_4 \def (\lambda (H: (le 
n m)).H) in (let TMP_8 \def (\lambda (p0: nat).(\lambda (IHp: (((le n m) \to 
(le (plus p0 n) (plus p0 m))))).(\lambda (H: (le n m)).(let TMP_5 \def (plus 
p0 n) in (let TMP_6 \def (plus p0 m) in (let TMP_7 \def (IHp H) in (le_n_S 
TMP_5 TMP_6 TMP_7))))))) in (nat_ind TMP_3 TMP_4 TMP_8 p)))))).

theorem le_plus_plus:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(\forall (q: nat).((le 
n m) \to ((le p q) \to (le (plus n p) (plus m q)))))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (q: 
nat).(\lambda (H: (le n m)).(\lambda (H0: (le p q)).(let TMP_3 \def (\lambda 
(n0: nat).(let TMP_1 \def (plus n p) in (let TMP_2 \def (plus n0 q) in (le 
TMP_1 TMP_2)))) in (let TMP_4 \def (le_reg_l p q n H0) in (let TMP_7 \def 
(\lambda (m0: nat).(\lambda (_: (le n m0)).(\lambda (H2: (le (plus n p) (plus 
m0 q))).(let TMP_5 \def (plus n p) in (let TMP_6 \def (plus m0 q) in (le_S 
TMP_5 TMP_6 H2)))))) in (le_ind n TMP_3 TMP_4 TMP_7 m H))))))))).

theorem le_plus_minus:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (eq nat m (plus n (minus m 
n)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (Le: (le n m)).(let TMP_3 \def 
(\lambda (n0: nat).(\lambda (n1: nat).(let TMP_1 \def (minus n1 n0) in (let 
TMP_2 \def (plus n0 TMP_1) in (eq nat n1 TMP_2))))) in (let TMP_4 \def 
(\lambda (p: nat).(minus_n_O p)) in (let TMP_7 \def (\lambda (p: 
nat).(\lambda (q: nat).(\lambda (_: (le p q)).(\lambda (H0: (eq nat q (plus p 
(minus q p)))).(let TMP_5 \def (minus q p) in (let TMP_6 \def (plus p TMP_5) 
in (f_equal nat nat S q TMP_6 H0))))))) in (le_elim_rel TMP_3 TMP_4 TMP_7 n m 
Le)))))).

theorem le_plus_minus_r:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (eq nat (plus n (minus m 
n)) m)))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(let TMP_1 \def 
(minus m n) in (let TMP_2 \def (plus n TMP_1) in (let TMP_3 \def 
(le_plus_minus n m H) in (sym_eq nat m TMP_2 TMP_3)))))).

theorem simpl_lt_plus_l:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((lt (plus p n) (plus p 
m)) \to (lt n m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(let TMP_1 \def 
(\lambda (n0: nat).((lt (plus n0 n) (plus n0 m)) \to (lt n m))) in (let TMP_2 
\def (\lambda (H: (lt n m)).H) in (let TMP_7 \def (\lambda (p0: nat).(\lambda 
(IHp: (((lt (plus p0 n) (plus p0 m)) \to (lt n m)))).(\lambda (H: (lt (S 
(plus p0 n)) (S (plus p0 m)))).(let TMP_3 \def (plus p0 n) in (let TMP_4 \def 
(S TMP_3) in (let TMP_5 \def (plus p0 m) in (let TMP_6 \def (le_S_n TMP_4 
TMP_5 H) in (IHp TMP_6)))))))) in (nat_ind TMP_1 TMP_2 TMP_7 p)))))).

theorem lt_reg_l:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((lt n m) \to (lt (plus 
p n) (plus p m)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(let TMP_3 \def 
(\lambda (n0: nat).((lt n m) \to (let TMP_1 \def (plus n0 n) in (let TMP_2 
\def (plus n0 m) in (lt TMP_1 TMP_2))))) in (let TMP_4 \def (\lambda (H: (lt 
n m)).H) in (let TMP_8 \def (\lambda (p0: nat).(\lambda (IHp: (((lt n m) \to 
(lt (plus p0 n) (plus p0 m))))).(\lambda (H: (lt n m)).(let TMP_5 \def (plus 
p0 n) in (let TMP_6 \def (plus p0 m) in (let TMP_7 \def (IHp H) in (lt_n_S 
TMP_5 TMP_6 TMP_7))))))) in (nat_ind TMP_3 TMP_4 TMP_8 p)))))).

theorem lt_reg_r:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((lt n m) \to (lt (plus 
n p) (plus m p)))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (lt n 
m)).(let TMP_1 \def (plus p n) in (let TMP_3 \def (\lambda (n0: nat).(let 
TMP_2 \def (plus m p) in (lt n0 TMP_2))) in (let TMP_4 \def (plus p m) in 
(let TMP_6 \def (\lambda (n0: nat).(let TMP_5 \def (plus p n) in (lt TMP_5 
n0))) in (let TMP_9 \def (\lambda (n0: nat).(let TMP_7 \def (plus n0 n) in 
(let TMP_8 \def (plus n0 m) in (lt TMP_7 TMP_8)))) in (let TMP_11 \def 
(\lambda (n0: nat).(\lambda (_: (lt (plus n0 n) (plus n0 m))).(let TMP_10 
\def (S n0) in (lt_reg_l n m TMP_10 H)))) in (let TMP_12 \def (nat_ind TMP_9 
H TMP_11 p) in (let TMP_13 \def (plus m p) in (let TMP_14 \def (plus_sym m p) 
in (let TMP_15 \def (eq_ind_r nat TMP_4 TMP_6 TMP_12 TMP_13 TMP_14) in (let 
TMP_16 \def (plus n p) in (let TMP_17 \def (plus_sym n p) in (eq_ind_r nat 
TMP_1 TMP_3 TMP_15 TMP_16 TMP_17)))))))))))))))).

theorem le_lt_plus_plus:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(\forall (q: nat).((le 
n m) \to ((lt p q) \to (lt (plus n p) (plus m q)))))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (q: 
nat).(\lambda (H: (le n m)).(\lambda (H0: (le (S p) q)).(let TMP_1 \def (S p) 
in (let TMP_2 \def (plus n TMP_1) in (let TMP_4 \def (\lambda (n0: nat).(let 
TMP_3 \def (plus m q) in (le n0 TMP_3))) in (let TMP_5 \def (S p) in (let 
TMP_6 \def (le_plus_plus n m TMP_5 q H H0) in (let TMP_7 \def (S n) in (let 
TMP_8 \def (plus TMP_7 p) in (let TMP_9 \def (plus_Snm_nSm n p) in (eq_ind_r 
nat TMP_2 TMP_4 TMP_6 TMP_8 TMP_9)))))))))))))).

theorem lt_le_plus_plus:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(\forall (q: nat).((lt 
n m) \to ((le p q) \to (lt (plus n p) (plus m q)))))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (q: 
nat).(\lambda (H: (le (S n) m)).(\lambda (H0: (le p q)).(let TMP_1 \def (S n) 
in (le_plus_plus TMP_1 m p q H H0))))))).

theorem lt_plus_plus:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).(\forall (q: nat).((lt 
n m) \to ((lt p q) \to (lt (plus n p) (plus m q)))))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (q: 
nat).(\lambda (H: (lt n m)).(\lambda (H0: (lt p q)).(let TMP_1 \def 
(lt_le_weak p q H0) in (lt_le_plus_plus n m p q H TMP_1))))))).

theorem well_founded_ltof:
 \forall (A: Type[0]).(\forall (f: ((A \to nat))).(well_founded A (ltof A f)))
\def
 \lambda (A: Type[0]).(\lambda (f: ((A \to nat))).(let H \def (\lambda (n: 
nat).(let TMP_2 \def (\lambda (n0: nat).(\forall (a: A).((lt (f a) n0) \to 
(let TMP_1 \def (ltof A f) in (Acc A TMP_1 a))))) in (let TMP_8 \def (\lambda 
(a: A).(\lambda (H: (lt (f a) O)).(let TMP_3 \def (ltof A f) in (let TMP_4 
\def (Acc A TMP_3 a) in (let H0 \def H in (let TMP_5 \def (f a) in (let H1 
\def (lt_n_O TMP_5) in (let TMP_6 \def (\lambda (H2: (lt (f a) O)).(H1 H2)) 
in (let TMP_7 \def (TMP_6 H0) in (False_ind TMP_4 TMP_7)))))))))) in (let 
TMP_16 \def (\lambda (n0: nat).(\lambda (IHn: ((\forall (a: A).((lt (f a) n0) 
\to (Acc A (ltof A f) a))))).(\lambda (a: A).(\lambda (ltSma: (lt (f a) (S 
n0))).(let TMP_9 \def (ltof A f) in (let TMP_15 \def (\lambda (b: A).(\lambda 
(ltfafb: (lt (f b) (f a))).(let TMP_10 \def (f b) in (let TMP_11 \def (f a) 
in (let TMP_12 \def (f a) in (let TMP_13 \def (lt_n_Sm_le TMP_12 n0 ltSma) in 
(let TMP_14 \def (lt_le_trans TMP_10 TMP_11 n0 ltfafb TMP_13) in (IHn b 
TMP_14)))))))) in (Acc_intro A TMP_9 a TMP_15))))))) in (nat_ind TMP_2 TMP_8 
TMP_16 n))))) in (\lambda (a: A).(let TMP_17 \def (f a) in (let TMP_18 \def 
(S TMP_17) in (let TMP_19 \def (f a) in (let TMP_20 \def (S TMP_19) in (let 
TMP_21 \def (le_n TMP_20) in (H TMP_18 a TMP_21))))))))).

theorem lt_wf:
 well_founded nat lt
\def
 let TMP_1 \def (\lambda (m: nat).m) in (well_founded_ltof nat TMP_1).

theorem lt_wf_ind:
 \forall (p: nat).(\forall (P: ((nat \to Prop))).(((\forall (n: 
nat).(((\forall (m: nat).((lt m n) \to (P m)))) \to (P n)))) \to (P p)))
\def
 \lambda (p: nat).(\lambda (P: ((nat \to Prop))).(\lambda (H: ((\forall (n: 
nat).(((\forall (m: nat).((lt m n) \to (P m)))) \to (P n))))).(let TMP_1 \def 
(\lambda (n: nat).(P n)) in (let TMP_2 \def (\lambda (x: nat).(\lambda (_: 
((\forall (y: nat).((lt y x) \to (Acc nat lt y))))).(\lambda (H1: ((\forall 
(y: nat).((lt y x) \to (P y))))).(H x H1)))) in (let TMP_3 \def (lt_wf p) in 
(Acc_ind nat lt TMP_1 TMP_2 p TMP_3)))))).

