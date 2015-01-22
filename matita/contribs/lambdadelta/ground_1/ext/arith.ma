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

include "Ground-1/preamble.ma".

theorem nat_dec:
 \forall (n1: nat).(\forall (n2: nat).(or (eq nat n1 n2) ((eq nat n1 n2) \to 
(\forall (P: Prop).P))))
\def
 \lambda (n1: nat).(nat_ind (\lambda (n: nat).(\forall (n2: nat).(or (eq nat 
n n2) ((eq nat n n2) \to (\forall (P: Prop).P))))) (\lambda (n2: 
nat).(nat_ind (\lambda (n: nat).(or (eq nat O n) ((eq nat O n) \to (\forall 
(P: Prop).P)))) (or_introl (eq nat O O) ((eq nat O O) \to (\forall (P: 
Prop).P)) (refl_equal nat O)) (\lambda (n: nat).(\lambda (_: (or (eq nat O n) 
((eq nat O n) \to (\forall (P: Prop).P)))).(or_intror (eq nat O (S n)) ((eq 
nat O (S n)) \to (\forall (P: Prop).P)) (\lambda (H0: (eq nat O (S 
n))).(\lambda (P: Prop).(let H1 \def (eq_ind nat O (\lambda (ee: nat).(match 
ee in nat return (\lambda (_: nat).Prop) with [O \Rightarrow True | (S _) 
\Rightarrow False])) I (S n) H0) in (False_ind P H1))))))) n2)) (\lambda (n: 
nat).(\lambda (H: ((\forall (n2: nat).(or (eq nat n n2) ((eq nat n n2) \to 
(\forall (P: Prop).P)))))).(\lambda (n2: nat).(nat_ind (\lambda (n0: nat).(or 
(eq nat (S n) n0) ((eq nat (S n) n0) \to (\forall (P: Prop).P)))) (or_intror 
(eq nat (S n) O) ((eq nat (S n) O) \to (\forall (P: Prop).P)) (\lambda (H0: 
(eq nat (S n) O)).(\lambda (P: Prop).(let H1 \def (eq_ind nat (S n) (\lambda 
(ee: nat).(match ee in nat return (\lambda (_: nat).Prop) with [O \Rightarrow 
False | (S _) \Rightarrow True])) I O H0) in (False_ind P H1))))) (\lambda 
(n0: nat).(\lambda (H0: (or (eq nat (S n) n0) ((eq nat (S n) n0) \to (\forall 
(P: Prop).P)))).(or_ind (eq nat n n0) ((eq nat n n0) \to (\forall (P: 
Prop).P)) (or (eq nat (S n) (S n0)) ((eq nat (S n) (S n0)) \to (\forall (P: 
Prop).P))) (\lambda (H1: (eq nat n n0)).(let H2 \def (eq_ind_r nat n0 
(\lambda (n3: nat).(or (eq nat (S n) n3) ((eq nat (S n) n3) \to (\forall (P: 
Prop).P)))) H0 n H1) in (eq_ind nat n (\lambda (n3: nat).(or (eq nat (S n) (S 
n3)) ((eq nat (S n) (S n3)) \to (\forall (P: Prop).P)))) (or_introl (eq nat 
(S n) (S n)) ((eq nat (S n) (S n)) \to (\forall (P: Prop).P)) (refl_equal nat 
(S n))) n0 H1))) (\lambda (H1: (((eq nat n n0) \to (\forall (P: 
Prop).P)))).(or_intror (eq nat (S n) (S n0)) ((eq nat (S n) (S n0)) \to 
(\forall (P: Prop).P)) (\lambda (H2: (eq nat (S n) (S n0))).(\lambda (P: 
Prop).(let H3 \def (f_equal nat nat (\lambda (e: nat).(match e in nat return 
(\lambda (_: nat).nat) with [O \Rightarrow n | (S n3) \Rightarrow n3])) (S n) 
(S n0) H2) in (let H4 \def (eq_ind_r nat n0 (\lambda (n3: nat).((eq nat n n3) 
\to (\forall (P0: Prop).P0))) H1 n H3) in (let H5 \def (eq_ind_r nat n0 
(\lambda (n3: nat).(or (eq nat (S n) n3) ((eq nat (S n) n3) \to (\forall (P0: 
Prop).P0)))) H0 n H3) in (H4 (refl_equal nat n) P)))))))) (H n0)))) n2)))) 
n1).
(* COMMENTS
Initial nodes: 676
END *)

theorem simpl_plus_r:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((eq nat (plus m n) 
(plus p n)) \to (eq nat m p))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (eq nat 
(plus m n) (plus p n))).(simpl_plus_l n m p (eq_ind_r nat (plus m n) (\lambda 
(n0: nat).(eq nat n0 (plus n p))) (eq_ind_r nat (plus p n) (\lambda (n0: 
nat).(eq nat n0 (plus n p))) (sym_eq nat (plus n p) (plus p n) (plus_sym n 
p)) (plus m n) H) (plus n m) (plus_sym n m)))))).
(* COMMENTS
Initial nodes: 119
END *)

theorem minus_Sx_Sy:
 \forall (x: nat).(\forall (y: nat).(eq nat (minus (S x) (S y)) (minus x y)))
\def
 \lambda (x: nat).(\lambda (y: nat).(refl_equal nat (minus x y))).
(* COMMENTS
Initial nodes: 13
END *)

theorem minus_plus_r:
 \forall (m: nat).(\forall (n: nat).(eq nat (minus (plus m n) n) m))
\def
 \lambda (m: nat).(\lambda (n: nat).(eq_ind_r nat (plus n m) (\lambda (n0: 
nat).(eq nat (minus n0 n) m)) (minus_plus n m) (plus m n) (plus_sym m n))).
(* COMMENTS
Initial nodes: 45
END *)

theorem plus_permute_2_in_3:
 \forall (x: nat).(\forall (y: nat).(\forall (z: nat).(eq nat (plus (plus x 
y) z) (plus (plus x z) y))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (z: nat).(eq_ind_r nat (plus x 
(plus y z)) (\lambda (n: nat).(eq nat n (plus (plus x z) y))) (eq_ind_r nat 
(plus z y) (\lambda (n: nat).(eq nat (plus x n) (plus (plus x z) y))) (eq_ind 
nat (plus (plus x z) y) (\lambda (n: nat).(eq nat n (plus (plus x z) y))) 
(refl_equal nat (plus (plus x z) y)) (plus x (plus z y)) (plus_assoc_r x z 
y)) (plus y z) (plus_sym y z)) (plus (plus x y) z) (plus_assoc_r x y z)))).
(* COMMENTS
Initial nodes: 163
END *)

theorem plus_permute_2_in_3_assoc:
 \forall (n: nat).(\forall (h: nat).(\forall (k: nat).(eq nat (plus (plus n 
h) k) (plus n (plus k h)))))
\def
 \lambda (n: nat).(\lambda (h: nat).(\lambda (k: nat).(eq_ind_r nat (plus 
(plus n k) h) (\lambda (n0: nat).(eq nat n0 (plus n (plus k h)))) (eq_ind_r 
nat (plus (plus n k) h) (\lambda (n0: nat).(eq nat (plus (plus n k) h) n0)) 
(refl_equal nat (plus (plus n k) h)) (plus n (plus k h)) (plus_assoc_l n k 
h)) (plus (plus n h) k) (plus_permute_2_in_3 n h k)))).
(* COMMENTS
Initial nodes: 119
END *)

theorem plus_O:
 \forall (x: nat).(\forall (y: nat).((eq nat (plus x y) O) \to (land (eq nat 
x O) (eq nat y O))))
\def
 \lambda (x: nat).(nat_ind (\lambda (n: nat).(\forall (y: nat).((eq nat (plus 
n y) O) \to (land (eq nat n O) (eq nat y O))))) (\lambda (y: nat).(\lambda 
(H: (eq nat (plus O y) O)).(conj (eq nat O O) (eq nat y O) (refl_equal nat O) 
H))) (\lambda (n: nat).(\lambda (_: ((\forall (y: nat).((eq nat (plus n y) O) 
\to (land (eq nat n O) (eq nat y O)))))).(\lambda (y: nat).(\lambda (H0: (eq 
nat (plus (S n) y) O)).(let H1 \def (match H0 in eq return (\lambda (n0: 
nat).(\lambda (_: (eq ? ? n0)).((eq nat n0 O) \to (land (eq nat (S n) O) (eq 
nat y O))))) with [refl_equal \Rightarrow (\lambda (H1: (eq nat (plus (S n) 
y) O)).(let H2 \def (eq_ind nat (plus (S n) y) (\lambda (e: nat).(match e in 
nat return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) 
\Rightarrow True])) I O H1) in (False_ind (land (eq nat (S n) O) (eq nat y 
O)) H2)))]) in (H1 (refl_equal nat O))))))) x).
(* COMMENTS
Initial nodes: 233
END *)

theorem minus_Sx_SO:
 \forall (x: nat).(eq nat (minus (S x) (S O)) x)
\def
 \lambda (x: nat).(eq_ind nat x (\lambda (n: nat).(eq nat n x)) (refl_equal 
nat x) (minus x O) (minus_n_O x)).
(* COMMENTS
Initial nodes: 33
END *)

theorem eq_nat_dec:
 \forall (i: nat).(\forall (j: nat).(or (not (eq nat i j)) (eq nat i j)))
\def
 \lambda (i: nat).(nat_ind (\lambda (n: nat).(\forall (j: nat).(or (not (eq 
nat n j)) (eq nat n j)))) (\lambda (j: nat).(nat_ind (\lambda (n: nat).(or 
(not (eq nat O n)) (eq nat O n))) (or_intror (not (eq nat O O)) (eq nat O O) 
(refl_equal nat O)) (\lambda (n: nat).(\lambda (_: (or (not (eq nat O n)) (eq 
nat O n))).(or_introl (not (eq nat O (S n))) (eq nat O (S n)) (O_S n)))) j)) 
(\lambda (n: nat).(\lambda (H: ((\forall (j: nat).(or (not (eq nat n j)) (eq 
nat n j))))).(\lambda (j: nat).(nat_ind (\lambda (n0: nat).(or (not (eq nat 
(S n) n0)) (eq nat (S n) n0))) (or_introl (not (eq nat (S n) O)) (eq nat (S 
n) O) (sym_not_eq nat O (S n) (O_S n))) (\lambda (n0: nat).(\lambda (_: (or 
(not (eq nat (S n) n0)) (eq nat (S n) n0))).(or_ind (not (eq nat n n0)) (eq 
nat n n0) (or (not (eq nat (S n) (S n0))) (eq nat (S n) (S n0))) (\lambda 
(H1: (not (eq nat n n0))).(or_introl (not (eq nat (S n) (S n0))) (eq nat (S 
n) (S n0)) (not_eq_S n n0 H1))) (\lambda (H1: (eq nat n n0)).(or_intror (not 
(eq nat (S n) (S n0))) (eq nat (S n) (S n0)) (f_equal nat nat S n n0 H1))) (H 
n0)))) j)))) i).
(* COMMENTS
Initial nodes: 401
END *)

theorem neq_eq_e:
 \forall (i: nat).(\forall (j: nat).(\forall (P: Prop).((((not (eq nat i j)) 
\to P)) \to ((((eq nat i j) \to P)) \to P))))
\def
 \lambda (i: nat).(\lambda (j: nat).(\lambda (P: Prop).(\lambda (H: (((not 
(eq nat i j)) \to P))).(\lambda (H0: (((eq nat i j) \to P))).(let o \def 
(eq_nat_dec i j) in (or_ind (not (eq nat i j)) (eq nat i j) P H H0 o)))))).
(* COMMENTS
Initial nodes: 61
END *)

theorem le_false:
 \forall (m: nat).(\forall (n: nat).(\forall (P: Prop).((le m n) \to ((le (S 
n) m) \to P))))
\def
 \lambda (m: nat).(nat_ind (\lambda (n: nat).(\forall (n0: nat).(\forall (P: 
Prop).((le n n0) \to ((le (S n0) n) \to P))))) (\lambda (n: nat).(\lambda (P: 
Prop).(\lambda (_: (le O n)).(\lambda (H0: (le (S n) O)).(let H1 \def (match 
H0 in le return (\lambda (n0: nat).(\lambda (_: (le ? n0)).((eq nat n0 O) \to 
P))) with [le_n \Rightarrow (\lambda (H1: (eq nat (S n) O)).(let H2 \def 
(eq_ind nat (S n) (\lambda (e: nat).(match e in nat return (\lambda (_: 
nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) I O H1) in 
(False_ind P H2))) | (le_S m0 H1) \Rightarrow (\lambda (H2: (eq nat (S m0) 
O)).((let H3 \def (eq_ind nat (S m0) (\lambda (e: nat).(match e in nat return 
(\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) 
I O H2) in (False_ind ((le (S n) m0) \to P) H3)) H1))]) in (H1 (refl_equal 
nat O))))))) (\lambda (n: nat).(\lambda (H: ((\forall (n0: nat).(\forall (P: 
Prop).((le n n0) \to ((le (S n0) n) \to P)))))).(\lambda (n0: nat).(nat_ind 
(\lambda (n1: nat).(\forall (P: Prop).((le (S n) n1) \to ((le (S n1) (S n)) 
\to P)))) (\lambda (P: Prop).(\lambda (H0: (le (S n) O)).(\lambda (_: (le (S 
O) (S n))).(let H2 \def (match H0 in le return (\lambda (n1: nat).(\lambda 
(_: (le ? n1)).((eq nat n1 O) \to P))) with [le_n \Rightarrow (\lambda (H2: 
(eq nat (S n) O)).(let H3 \def (eq_ind nat (S n) (\lambda (e: nat).(match e 
in nat return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) 
\Rightarrow True])) I O H2) in (False_ind P H3))) | (le_S m0 H2) \Rightarrow 
(\lambda (H3: (eq nat (S m0) O)).((let H4 \def (eq_ind nat (S m0) (\lambda 
(e: nat).(match e in nat return (\lambda (_: nat).Prop) with [O \Rightarrow 
False | (S _) \Rightarrow True])) I O H3) in (False_ind ((le (S n) m0) \to P) 
H4)) H2))]) in (H2 (refl_equal nat O)))))) (\lambda (n1: nat).(\lambda (_: 
((\forall (P: Prop).((le (S n) n1) \to ((le (S n1) (S n)) \to P))))).(\lambda 
(P: Prop).(\lambda (H1: (le (S n) (S n1))).(\lambda (H2: (le (S (S n1)) (S 
n))).(H n1 P (le_S_n n n1 H1) (le_S_n (S n1) n H2))))))) n0)))) m).
(* COMMENTS
Initial nodes: 409
END *)

theorem le_Sx_x:
 \forall (x: nat).((le (S x) x) \to (\forall (P: Prop).P))
\def
 \lambda (x: nat).(\lambda (H: (le (S x) x)).(\lambda (P: Prop).(let H0 \def 
le_Sn_n in (False_ind P (H0 x H))))).
(* COMMENTS
Initial nodes: 23
END *)

theorem le_n_pred:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (le (pred n) (pred m))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(le_ind n (\lambda 
(n0: nat).(le (pred n) (pred n0))) (le_n (pred n)) (\lambda (m0: 
nat).(\lambda (_: (le n m0)).(\lambda (H1: (le (pred n) (pred m0))).(le_trans 
(pred n) (pred m0) m0 H1 (le_pred_n m0))))) m H))).
(* COMMENTS
Initial nodes: 71
END *)

theorem minus_le:
 \forall (x: nat).(\forall (y: nat).(le (minus x y) x))
\def
 \lambda (x: nat).(nat_ind (\lambda (n: nat).(\forall (y: nat).(le (minus n 
y) n))) (\lambda (_: nat).(le_n O)) (\lambda (n: nat).(\lambda (H: ((\forall 
(y: nat).(le (minus n y) n)))).(\lambda (y: nat).(nat_ind (\lambda (n0: 
nat).(le (minus (S n) n0) (S n))) (le_n (S n)) (\lambda (n0: nat).(\lambda 
(_: (le (match n0 with [O \Rightarrow (S n) | (S l) \Rightarrow (minus n l)]) 
(S n))).(le_S (minus n n0) n (H n0)))) y)))) x).
(* COMMENTS
Initial nodes: 101
END *)

theorem le_plus_minus_sym:
 \forall (n: nat).(\forall (m: nat).((le n m) \to (eq nat m (plus (minus m n) 
n))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (H: (le n m)).(eq_ind_r nat 
(plus n (minus m n)) (\lambda (n0: nat).(eq nat m n0)) (le_plus_minus n m H) 
(plus (minus m n) n) (plus_sym (minus m n) n)))).
(* COMMENTS
Initial nodes: 61
END *)

theorem le_minus_minus:
 \forall (x: nat).(\forall (y: nat).((le x y) \to (\forall (z: nat).((le y z) 
\to (le (minus y x) (minus z x))))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (le x y)).(\lambda (z: 
nat).(\lambda (H0: (le y z)).(simpl_le_plus_l x (minus y x) (minus z x) 
(eq_ind_r nat y (\lambda (n: nat).(le n (plus x (minus z x)))) (eq_ind_r nat 
z (\lambda (n: nat).(le y n)) H0 (plus x (minus z x)) (le_plus_minus_r x z 
(le_trans x y z H H0))) (plus x (minus y x)) (le_plus_minus_r x y H))))))).
(* COMMENTS
Initial nodes: 117
END *)

theorem le_minus_plus:
 \forall (z: nat).(\forall (x: nat).((le z x) \to (\forall (y: nat).(eq nat 
(minus (plus x y) z) (plus (minus x z) y)))))
\def
 \lambda (z: nat).(nat_ind (\lambda (n: nat).(\forall (x: nat).((le n x) \to 
(\forall (y: nat).(eq nat (minus (plus x y) n) (plus (minus x n) y)))))) 
(\lambda (x: nat).(\lambda (H: (le O x)).(let H0 \def (match H in le return 
(\lambda (n: nat).(\lambda (_: (le ? n)).((eq nat n x) \to (\forall (y: 
nat).(eq nat (minus (plus x y) O) (plus (minus x O) y)))))) with [le_n 
\Rightarrow (\lambda (H0: (eq nat O x)).(eq_ind nat O (\lambda (n: 
nat).(\forall (y: nat).(eq nat (minus (plus n y) O) (plus (minus n O) y)))) 
(\lambda (y: nat).(sym_eq nat (plus (minus O O) y) (minus (plus O y) O) 
(minus_n_O (plus O y)))) x H0)) | (le_S m H0) \Rightarrow (\lambda (H1: (eq 
nat (S m) x)).(eq_ind nat (S m) (\lambda (n: nat).((le O m) \to (\forall (y: 
nat).(eq nat (minus (plus n y) O) (plus (minus n O) y))))) (\lambda (_: (le O 
m)).(\lambda (y: nat).(refl_equal nat (plus (minus (S m) O) y)))) x H1 H0))]) 
in (H0 (refl_equal nat x))))) (\lambda (z0: nat).(\lambda (H: ((\forall (x: 
nat).((le z0 x) \to (\forall (y: nat).(eq nat (minus (plus x y) z0) (plus 
(minus x z0) y))))))).(\lambda (x: nat).(nat_ind (\lambda (n: nat).((le (S 
z0) n) \to (\forall (y: nat).(eq nat (minus (plus n y) (S z0)) (plus (minus n 
(S z0)) y))))) (\lambda (H0: (le (S z0) O)).(\lambda (y: nat).(let H1 \def 
(match H0 in le return (\lambda (n: nat).(\lambda (_: (le ? n)).((eq nat n O) 
\to (eq nat (minus (plus O y) (S z0)) (plus (minus O (S z0)) y))))) with 
[le_n \Rightarrow (\lambda (H1: (eq nat (S z0) O)).(let H2 \def (eq_ind nat 
(S z0) (\lambda (e: nat).(match e in nat return (\lambda (_: nat).Prop) with 
[O \Rightarrow False | (S _) \Rightarrow True])) I O H1) in (False_ind (eq 
nat (minus (plus O y) (S z0)) (plus (minus O (S z0)) y)) H2))) | (le_S m H1) 
\Rightarrow (\lambda (H2: (eq nat (S m) O)).((let H3 \def (eq_ind nat (S m) 
(\lambda (e: nat).(match e in nat return (\lambda (_: nat).Prop) with [O 
\Rightarrow False | (S _) \Rightarrow True])) I O H2) in (False_ind ((le (S 
z0) m) \to (eq nat (minus (plus O y) (S z0)) (plus (minus O (S z0)) y))) H3)) 
H1))]) in (H1 (refl_equal nat O))))) (\lambda (n: nat).(\lambda (_: (((le (S 
z0) n) \to (\forall (y: nat).(eq nat (minus (plus n y) (S z0)) (plus (minus n 
(S z0)) y)))))).(\lambda (H1: (le (S z0) (S n))).(\lambda (y: nat).(H n 
(le_S_n z0 n H1) y))))) x)))) z).
(* COMMENTS
Initial nodes: 603
END *)

theorem le_minus:
 \forall (x: nat).(\forall (z: nat).(\forall (y: nat).((le (plus x y) z) \to 
(le x (minus z y)))))
\def
 \lambda (x: nat).(\lambda (z: nat).(\lambda (y: nat).(\lambda (H: (le (plus 
x y) z)).(eq_ind nat (minus (plus x y) y) (\lambda (n: nat).(le n (minus z 
y))) (le_minus_minus y (plus x y) (le_plus_r x y) z H) x (minus_plus_r x 
y))))).
(* COMMENTS
Initial nodes: 69
END *)

theorem le_trans_plus_r:
 \forall (x: nat).(\forall (y: nat).(\forall (z: nat).((le (plus x y) z) \to 
(le y z))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (z: nat).(\lambda (H: (le (plus 
x y) z)).(le_trans y (plus x y) z (le_plus_r x y) H)))).
(* COMMENTS
Initial nodes: 35
END *)

theorem lt_x_O:
 \forall (x: nat).((lt x O) \to (\forall (P: Prop).P))
\def
 \lambda (x: nat).(\lambda (H: (le (S x) O)).(\lambda (P: Prop).(let H_y \def 
(le_n_O_eq (S x) H) in (let H0 \def (eq_ind nat O (\lambda (ee: nat).(match 
ee in nat return (\lambda (_: nat).Prop) with [O \Rightarrow True | (S _) 
\Rightarrow False])) I (S x) H_y) in (False_ind P H0))))).
(* COMMENTS
Initial nodes: 48
END *)

theorem le_gen_S:
 \forall (m: nat).(\forall (x: nat).((le (S m) x) \to (ex2 nat (\lambda (n: 
nat).(eq nat x (S n))) (\lambda (n: nat).(le m n)))))
\def
 \lambda (m: nat).(\lambda (x: nat).(\lambda (H: (le (S m) x)).(let H0 \def 
(match H in le return (\lambda (n: nat).(\lambda (_: (le ? n)).((eq nat n x) 
\to (ex2 nat (\lambda (n0: nat).(eq nat x (S n0))) (\lambda (n0: nat).(le m 
n0)))))) with [le_n \Rightarrow (\lambda (H0: (eq nat (S m) x)).(eq_ind nat 
(S m) (\lambda (n: nat).(ex2 nat (\lambda (n0: nat).(eq nat n (S n0))) 
(\lambda (n0: nat).(le m n0)))) (ex_intro2 nat (\lambda (n: nat).(eq nat (S 
m) (S n))) (\lambda (n: nat).(le m n)) m (refl_equal nat (S m)) (le_n m)) x 
H0)) | (le_S m0 H0) \Rightarrow (\lambda (H1: (eq nat (S m0) x)).(eq_ind nat 
(S m0) (\lambda (n: nat).((le (S m) m0) \to (ex2 nat (\lambda (n0: nat).(eq 
nat n (S n0))) (\lambda (n0: nat).(le m n0))))) (\lambda (H2: (le (S m) 
m0)).(ex_intro2 nat (\lambda (n: nat).(eq nat (S m0) (S n))) (\lambda (n: 
nat).(le m n)) m0 (refl_equal nat (S m0)) (le_S_n m m0 (le_S (S m) m0 H2)))) 
x H1 H0))]) in (H0 (refl_equal nat x))))).
(* COMMENTS
Initial nodes: 261
END *)

theorem lt_x_plus_x_Sy:
 \forall (x: nat).(\forall (y: nat).(lt x (plus x (S y))))
\def
 \lambda (x: nat).(\lambda (y: nat).(eq_ind_r nat (plus (S y) x) (\lambda (n: 
nat).(lt x n)) (le_S_n (S x) (S (plus y x)) (le_n_S (S x) (S (plus y x)) 
(le_n_S x (plus y x) (le_plus_r y x)))) (plus x (S y)) (plus_sym x (S y)))).
(* COMMENTS
Initial nodes: 83
END *)

theorem simpl_lt_plus_r:
 \forall (p: nat).(\forall (n: nat).(\forall (m: nat).((lt (plus n p) (plus m 
p)) \to (lt n m))))
\def
 \lambda (p: nat).(\lambda (n: nat).(\lambda (m: nat).(\lambda (H: (lt (plus 
n p) (plus m p))).(simpl_lt_plus_l n m p (let H0 \def (eq_ind nat (plus n p) 
(\lambda (n0: nat).(lt n0 (plus m p))) H (plus p n) (plus_sym n p)) in (let 
H1 \def (eq_ind nat (plus m p) (\lambda (n0: nat).(lt (plus p n) n0)) H0 
(plus p m) (plus_sym m p)) in H1)))))).
(* COMMENTS
Initial nodes: 101
END *)

theorem minus_x_Sy:
 \forall (x: nat).(\forall (y: nat).((lt y x) \to (eq nat (minus x y) (S 
(minus x (S y))))))
\def
 \lambda (x: nat).(nat_ind (\lambda (n: nat).(\forall (y: nat).((lt y n) \to 
(eq nat (minus n y) (S (minus n (S y))))))) (\lambda (y: nat).(\lambda (H: 
(lt y O)).(let H0 \def (match H in le return (\lambda (n: nat).(\lambda (_: 
(le ? n)).((eq nat n O) \to (eq nat (minus O y) (S (minus O (S y))))))) with 
[le_n \Rightarrow (\lambda (H0: (eq nat (S y) O)).(let H1 \def (eq_ind nat (S 
y) (\lambda (e: nat).(match e in nat return (\lambda (_: nat).Prop) with [O 
\Rightarrow False | (S _) \Rightarrow True])) I O H0) in (False_ind (eq nat 
(minus O y) (S (minus O (S y)))) H1))) | (le_S m H0) \Rightarrow (\lambda 
(H1: (eq nat (S m) O)).((let H2 \def (eq_ind nat (S m) (\lambda (e: 
nat).(match e in nat return (\lambda (_: nat).Prop) with [O \Rightarrow False 
| (S _) \Rightarrow True])) I O H1) in (False_ind ((le (S y) m) \to (eq nat 
(minus O y) (S (minus O (S y))))) H2)) H0))]) in (H0 (refl_equal nat O))))) 
(\lambda (n: nat).(\lambda (H: ((\forall (y: nat).((lt y n) \to (eq nat 
(minus n y) (S (minus n (S y)))))))).(\lambda (y: nat).(nat_ind (\lambda (n0: 
nat).((lt n0 (S n)) \to (eq nat (minus (S n) n0) (S (minus (S n) (S n0)))))) 
(\lambda (_: (lt O (S n))).(eq_ind nat n (\lambda (n0: nat).(eq nat (S n) (S 
n0))) (refl_equal nat (S n)) (minus n O) (minus_n_O n))) (\lambda (n0: 
nat).(\lambda (_: (((lt n0 (S n)) \to (eq nat (minus (S n) n0) (S (minus (S 
n) (S n0))))))).(\lambda (H1: (lt (S n0) (S n))).(let H2 \def (le_S_n (S n0) 
n H1) in (H n0 H2))))) y)))) x).
(* COMMENTS
Initial nodes: 383
END *)

theorem lt_plus_minus:
 \forall (x: nat).(\forall (y: nat).((lt x y) \to (eq nat y (S (plus x (minus 
y (S x)))))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (lt x y)).(le_plus_minus (S 
x) y H))).
(* COMMENTS
Initial nodes: 19
END *)

theorem lt_plus_minus_r:
 \forall (x: nat).(\forall (y: nat).((lt x y) \to (eq nat y (S (plus (minus y 
(S x)) x)))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (lt x y)).(eq_ind_r nat 
(plus x (minus y (S x))) (\lambda (n: nat).(eq nat y (S n))) (lt_plus_minus x 
y H) (plus (minus y (S x)) x) (plus_sym (minus y (S x)) x)))).
(* COMMENTS
Initial nodes: 69
END *)

theorem minus_x_SO:
 \forall (x: nat).((lt O x) \to (eq nat x (S (minus x (S O)))))
\def
 \lambda (x: nat).(\lambda (H: (lt O x)).(eq_ind nat (minus x O) (\lambda (n: 
nat).(eq nat x n)) (eq_ind nat x (\lambda (n: nat).(eq nat x n)) (refl_equal 
nat x) (minus x O) (minus_n_O x)) (S (minus x (S O))) (minus_x_Sy x O H))).
(* COMMENTS
Initial nodes: 77
END *)

theorem le_x_pred_y:
 \forall (y: nat).(\forall (x: nat).((lt x y) \to (le x (pred y))))
\def
 \lambda (y: nat).(nat_ind (\lambda (n: nat).(\forall (x: nat).((lt x n) \to 
(le x (pred n))))) (\lambda (x: nat).(\lambda (H: (lt x O)).(let H0 \def 
(match H in le return (\lambda (n: nat).(\lambda (_: (le ? n)).((eq nat n O) 
\to (le x O)))) with [le_n \Rightarrow (\lambda (H0: (eq nat (S x) O)).(let 
H1 \def (eq_ind nat (S x) (\lambda (e: nat).(match e in nat return (\lambda 
(_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) I O H0) 
in (False_ind (le x O) H1))) | (le_S m H0) \Rightarrow (\lambda (H1: (eq nat 
(S m) O)).((let H2 \def (eq_ind nat (S m) (\lambda (e: nat).(match e in nat 
return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow 
True])) I O H1) in (False_ind ((le (S x) m) \to (le x O)) H2)) H0))]) in (H0 
(refl_equal nat O))))) (\lambda (n: nat).(\lambda (_: ((\forall (x: nat).((lt 
x n) \to (le x (pred n)))))).(\lambda (x: nat).(\lambda (H0: (lt x (S 
n))).(le_S_n x n H0))))) y).
(* COMMENTS
Initial nodes: 189
END *)

theorem lt_le_minus:
 \forall (x: nat).(\forall (y: nat).((lt x y) \to (le x (minus y (S O)))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (lt x y)).(le_minus x y (S 
O) (eq_ind_r nat (plus (S O) x) (\lambda (n: nat).(le n y)) H (plus x (S O)) 
(plus_sym x (S O)))))).
(* COMMENTS
Initial nodes: 57
END *)

theorem lt_le_e:
 \forall (n: nat).(\forall (d: nat).(\forall (P: Prop).((((lt n d) \to P)) 
\to ((((le d n) \to P)) \to P))))
\def
 \lambda (n: nat).(\lambda (d: nat).(\lambda (P: Prop).(\lambda (H: (((lt n 
d) \to P))).(\lambda (H0: (((le d n) \to P))).(let H1 \def (le_or_lt d n) in 
(or_ind (le d n) (lt n d) P H0 H H1)))))).
(* COMMENTS
Initial nodes: 49
END *)

theorem lt_eq_e:
 \forall (x: nat).(\forall (y: nat).(\forall (P: Prop).((((lt x y) \to P)) 
\to ((((eq nat x y) \to P)) \to ((le x y) \to P)))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (P: Prop).(\lambda (H: (((lt x 
y) \to P))).(\lambda (H0: (((eq nat x y) \to P))).(\lambda (H1: (le x 
y)).(or_ind (lt x y) (eq nat x y) P H H0 (le_lt_or_eq x y H1))))))).
(* COMMENTS
Initial nodes: 59
END *)

theorem lt_eq_gt_e:
 \forall (x: nat).(\forall (y: nat).(\forall (P: Prop).((((lt x y) \to P)) 
\to ((((eq nat x y) \to P)) \to ((((lt y x) \to P)) \to P)))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (P: Prop).(\lambda (H: (((lt x 
y) \to P))).(\lambda (H0: (((eq nat x y) \to P))).(\lambda (H1: (((lt y x) 
\to P))).(lt_le_e x y P H (\lambda (H2: (le y x)).(lt_eq_e y x P H1 (\lambda 
(H3: (eq nat y x)).(H0 (sym_eq nat y x H3))) H2)))))))).
(* COMMENTS
Initial nodes: 79
END *)

theorem lt_gen_xS:
 \forall (x: nat).(\forall (n: nat).((lt x (S n)) \to (or (eq nat x O) (ex2 
nat (\lambda (m: nat).(eq nat x (S m))) (\lambda (m: nat).(lt m n))))))
\def
 \lambda (x: nat).(nat_ind (\lambda (n: nat).(\forall (n0: nat).((lt n (S 
n0)) \to (or (eq nat n O) (ex2 nat (\lambda (m: nat).(eq nat n (S m))) 
(\lambda (m: nat).(lt m n0))))))) (\lambda (n: nat).(\lambda (_: (lt O (S 
n))).(or_introl (eq nat O O) (ex2 nat (\lambda (m: nat).(eq nat O (S m))) 
(\lambda (m: nat).(lt m n))) (refl_equal nat O)))) (\lambda (n: nat).(\lambda 
(_: ((\forall (n0: nat).((lt n (S n0)) \to (or (eq nat n O) (ex2 nat (\lambda 
(m: nat).(eq nat n (S m))) (\lambda (m: nat).(lt m n0)))))))).(\lambda (n0: 
nat).(\lambda (H0: (lt (S n) (S n0))).(or_intror (eq nat (S n) O) (ex2 nat 
(\lambda (m: nat).(eq nat (S n) (S m))) (\lambda (m: nat).(lt m n0))) 
(ex_intro2 nat (\lambda (m: nat).(eq nat (S n) (S m))) (\lambda (m: nat).(lt 
m n0)) n (refl_equal nat (S n)) (le_S_n (S n) n0 H0))))))) x).
(* COMMENTS
Initial nodes: 243
END *)

theorem le_lt_false:
 \forall (x: nat).(\forall (y: nat).((le x y) \to ((lt y x) \to (\forall (P: 
Prop).P))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (le x y)).(\lambda (H0: (lt 
y x)).(\lambda (P: Prop).(False_ind P (le_not_lt x y H H0)))))).
(* COMMENTS
Initial nodes: 31
END *)

theorem lt_neq:
 \forall (x: nat).(\forall (y: nat).((lt x y) \to (not (eq nat x y))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (lt x y)).(\lambda (H0: (eq 
nat x y)).(let H1 \def (eq_ind nat x (\lambda (n: nat).(lt n y)) H y H0) in 
(lt_n_n y H1))))).
(* COMMENTS
Initial nodes: 43
END *)

theorem arith0:
 \forall (h2: nat).(\forall (d2: nat).(\forall (n: nat).((le (plus d2 h2) n) 
\to (\forall (h1: nat).(le (plus d2 h1) (minus (plus n h1) h2))))))
\def
 \lambda (h2: nat).(\lambda (d2: nat).(\lambda (n: nat).(\lambda (H: (le 
(plus d2 h2) n)).(\lambda (h1: nat).(eq_ind nat (minus (plus h2 (plus d2 h1)) 
h2) (\lambda (n0: nat).(le n0 (minus (plus n h1) h2))) (le_minus_minus h2 
(plus h2 (plus d2 h1)) (le_plus_l h2 (plus d2 h1)) (plus n h1) (eq_ind_r nat 
(plus (plus h2 d2) h1) (\lambda (n0: nat).(le n0 (plus n h1))) (eq_ind_r nat 
(plus d2 h2) (\lambda (n0: nat).(le (plus n0 h1) (plus n h1))) (le_S_n (plus 
(plus d2 h2) h1) (plus n h1) (le_n_S (plus (plus d2 h2) h1) (plus n h1) 
(le_plus_plus (plus d2 h2) n h1 h1 H (le_n h1)))) (plus h2 d2) (plus_sym h2 
d2)) (plus h2 (plus d2 h1)) (plus_assoc_l h2 d2 h1))) (plus d2 h1) 
(minus_plus h2 (plus d2 h1))))))).
(* COMMENTS
Initial nodes: 235
END *)

theorem O_minus:
 \forall (x: nat).(\forall (y: nat).((le x y) \to (eq nat (minus x y) O)))
\def
 \lambda (x: nat).(nat_ind (\lambda (n: nat).(\forall (y: nat).((le n y) \to 
(eq nat (minus n y) O)))) (\lambda (y: nat).(\lambda (_: (le O 
y)).(refl_equal nat O))) (\lambda (x0: nat).(\lambda (H: ((\forall (y: 
nat).((le x0 y) \to (eq nat (minus x0 y) O))))).(\lambda (y: nat).(nat_ind 
(\lambda (n: nat).((le (S x0) n) \to (eq nat (match n with [O \Rightarrow (S 
x0) | (S l) \Rightarrow (minus x0 l)]) O))) (\lambda (H0: (le (S x0) 
O)).(ex2_ind nat (\lambda (n: nat).(eq nat O (S n))) (\lambda (n: nat).(le x0 
n)) (eq nat (S x0) O) (\lambda (x1: nat).(\lambda (H1: (eq nat O (S 
x1))).(\lambda (_: (le x0 x1)).(let H3 \def (eq_ind nat O (\lambda (ee: 
nat).(match ee in nat return (\lambda (_: nat).Prop) with [O \Rightarrow True 
| (S _) \Rightarrow False])) I (S x1) H1) in (False_ind (eq nat (S x0) O) 
H3))))) (le_gen_S x0 O H0))) (\lambda (n: nat).(\lambda (_: (((le (S x0) n) 
\to (eq nat (match n with [O \Rightarrow (S x0) | (S l) \Rightarrow (minus x0 
l)]) O)))).(\lambda (H1: (le (S x0) (S n))).(H n (le_S_n x0 n H1))))) y)))) 
x).
(* COMMENTS
Initial nodes: 252
END *)

theorem minus_minus:
 \forall (z: nat).(\forall (x: nat).(\forall (y: nat).((le z x) \to ((le z y) 
\to ((eq nat (minus x z) (minus y z)) \to (eq nat x y))))))
\def
 \lambda (z: nat).(nat_ind (\lambda (n: nat).(\forall (x: nat).(\forall (y: 
nat).((le n x) \to ((le n y) \to ((eq nat (minus x n) (minus y n)) \to (eq 
nat x y))))))) (\lambda (x: nat).(\lambda (y: nat).(\lambda (_: (le O 
x)).(\lambda (_: (le O y)).(\lambda (H1: (eq nat (minus x O) (minus y 
O))).(let H2 \def (eq_ind_r nat (minus x O) (\lambda (n: nat).(eq nat n 
(minus y O))) H1 x (minus_n_O x)) in (let H3 \def (eq_ind_r nat (minus y O) 
(\lambda (n: nat).(eq nat x n)) H2 y (minus_n_O y)) in H3))))))) (\lambda 
(z0: nat).(\lambda (IH: ((\forall (x: nat).(\forall (y: nat).((le z0 x) \to 
((le z0 y) \to ((eq nat (minus x z0) (minus y z0)) \to (eq nat x 
y)))))))).(\lambda (x: nat).(nat_ind (\lambda (n: nat).(\forall (y: nat).((le 
(S z0) n) \to ((le (S z0) y) \to ((eq nat (minus n (S z0)) (minus y (S z0))) 
\to (eq nat n y)))))) (\lambda (y: nat).(\lambda (H: (le (S z0) O)).(\lambda 
(_: (le (S z0) y)).(\lambda (_: (eq nat (minus O (S z0)) (minus y (S 
z0)))).(ex2_ind nat (\lambda (n: nat).(eq nat O (S n))) (\lambda (n: nat).(le 
z0 n)) (eq nat O y) (\lambda (x0: nat).(\lambda (H2: (eq nat O (S 
x0))).(\lambda (_: (le z0 x0)).(let H4 \def (eq_ind nat O (\lambda (ee: 
nat).(match ee in nat return (\lambda (_: nat).Prop) with [O \Rightarrow True 
| (S _) \Rightarrow False])) I (S x0) H2) in (False_ind (eq nat O y) H4))))) 
(le_gen_S z0 O H)))))) (\lambda (x0: nat).(\lambda (_: ((\forall (y: 
nat).((le (S z0) x0) \to ((le (S z0) y) \to ((eq nat (minus x0 (S z0)) (minus 
y (S z0))) \to (eq nat x0 y))))))).(\lambda (y: nat).(nat_ind (\lambda (n: 
nat).((le (S z0) (S x0)) \to ((le (S z0) n) \to ((eq nat (minus (S x0) (S 
z0)) (minus n (S z0))) \to (eq nat (S x0) n))))) (\lambda (H: (le (S z0) (S 
x0))).(\lambda (H0: (le (S z0) O)).(\lambda (_: (eq nat (minus (S x0) (S z0)) 
(minus O (S z0)))).(let H_y \def (le_S_n z0 x0 H) in (ex2_ind nat (\lambda 
(n: nat).(eq nat O (S n))) (\lambda (n: nat).(le z0 n)) (eq nat (S x0) O) 
(\lambda (x1: nat).(\lambda (H2: (eq nat O (S x1))).(\lambda (_: (le z0 
x1)).(let H4 \def (eq_ind nat O (\lambda (ee: nat).(match ee in nat return 
(\lambda (_: nat).Prop) with [O \Rightarrow True | (S _) \Rightarrow False])) 
I (S x1) H2) in (False_ind (eq nat (S x0) O) H4))))) (le_gen_S z0 O H0)))))) 
(\lambda (y0: nat).(\lambda (_: (((le (S z0) (S x0)) \to ((le (S z0) y0) \to 
((eq nat (minus (S x0) (S z0)) (minus y0 (S z0))) \to (eq nat (S x0) 
y0)))))).(\lambda (H: (le (S z0) (S x0))).(\lambda (H0: (le (S z0) (S 
y0))).(\lambda (H1: (eq nat (minus (S x0) (S z0)) (minus (S y0) (S 
z0)))).(f_equal nat nat S x0 y0 (IH x0 y0 (le_S_n z0 x0 H) (le_S_n z0 y0 H0) 
H1))))))) y)))) x)))) z).
(* COMMENTS
Initial nodes: 751
END *)

theorem plus_plus:
 \forall (z: nat).(\forall (x1: nat).(\forall (x2: nat).(\forall (y1: 
nat).(\forall (y2: nat).((le x1 z) \to ((le x2 z) \to ((eq nat (plus (minus z 
x1) y1) (plus (minus z x2) y2)) \to (eq nat (plus x1 y2) (plus x2 y1)))))))))
\def
 \lambda (z: nat).(nat_ind (\lambda (n: nat).(\forall (x1: nat).(\forall (x2: 
nat).(\forall (y1: nat).(\forall (y2: nat).((le x1 n) \to ((le x2 n) \to ((eq 
nat (plus (minus n x1) y1) (plus (minus n x2) y2)) \to (eq nat (plus x1 y2) 
(plus x2 y1)))))))))) (\lambda (x1: nat).(\lambda (x2: nat).(\lambda (y1: 
nat).(\lambda (y2: nat).(\lambda (H: (le x1 O)).(\lambda (H0: (le x2 
O)).(\lambda (H1: (eq nat y1 y2)).(eq_ind nat y1 (\lambda (n: nat).(eq nat 
(plus x1 n) (plus x2 y1))) (let H_y \def (le_n_O_eq x2 H0) in (eq_ind nat O 
(\lambda (n: nat).(eq nat (plus x1 y1) (plus n y1))) (let H_y0 \def 
(le_n_O_eq x1 H) in (eq_ind nat O (\lambda (n: nat).(eq nat (plus n y1) (plus 
O y1))) (refl_equal nat (plus O y1)) x1 H_y0)) x2 H_y)) y2 H1)))))))) 
(\lambda (z0: nat).(\lambda (IH: ((\forall (x1: nat).(\forall (x2: 
nat).(\forall (y1: nat).(\forall (y2: nat).((le x1 z0) \to ((le x2 z0) \to 
((eq nat (plus (minus z0 x1) y1) (plus (minus z0 x2) y2)) \to (eq nat (plus 
x1 y2) (plus x2 y1))))))))))).(\lambda (x1: nat).(nat_ind (\lambda (n: 
nat).(\forall (x2: nat).(\forall (y1: nat).(\forall (y2: nat).((le n (S z0)) 
\to ((le x2 (S z0)) \to ((eq nat (plus (minus (S z0) n) y1) (plus (minus (S 
z0) x2) y2)) \to (eq nat (plus n y2) (plus x2 y1))))))))) (\lambda (x2: 
nat).(nat_ind (\lambda (n: nat).(\forall (y1: nat).(\forall (y2: nat).((le O 
(S z0)) \to ((le n (S z0)) \to ((eq nat (plus (minus (S z0) O) y1) (plus 
(minus (S z0) n) y2)) \to (eq nat (plus O y2) (plus n y1)))))))) (\lambda 
(y1: nat).(\lambda (y2: nat).(\lambda (_: (le O (S z0))).(\lambda (_: (le O 
(S z0))).(\lambda (H1: (eq nat (S (plus z0 y1)) (S (plus z0 y2)))).(let H_y 
\def (IH O O) in (let H2 \def (eq_ind_r nat (minus z0 O) (\lambda (n: 
nat).(\forall (y3: nat).(\forall (y4: nat).((le O z0) \to ((le O z0) \to ((eq 
nat (plus n y3) (plus n y4)) \to (eq nat y4 y3))))))) H_y z0 (minus_n_O z0)) 
in (H2 y1 y2 (le_O_n z0) (le_O_n z0) (eq_add_S (plus z0 y1) (plus z0 y2) 
H1))))))))) (\lambda (x3: nat).(\lambda (_: ((\forall (y1: nat).(\forall (y2: 
nat).((le O (S z0)) \to ((le x3 (S z0)) \to ((eq nat (S (plus z0 y1)) (plus 
(match x3 with [O \Rightarrow (S z0) | (S l) \Rightarrow (minus z0 l)]) y2)) 
\to (eq nat y2 (plus x3 y1))))))))).(\lambda (y1: nat).(\lambda (y2: 
nat).(\lambda (_: (le O (S z0))).(\lambda (H0: (le (S x3) (S z0))).(\lambda 
(H1: (eq nat (S (plus z0 y1)) (plus (minus z0 x3) y2))).(let H_y \def (IH O 
x3 (S y1)) in (let H2 \def (eq_ind_r nat (minus z0 O) (\lambda (n: 
nat).(\forall (y3: nat).((le O z0) \to ((le x3 z0) \to ((eq nat (plus n (S 
y1)) (plus (minus z0 x3) y3)) \to (eq nat y3 (plus x3 (S y1)))))))) H_y z0 
(minus_n_O z0)) in (let H3 \def (eq_ind_r nat (plus z0 (S y1)) (\lambda (n: 
nat).(\forall (y3: nat).((le O z0) \to ((le x3 z0) \to ((eq nat n (plus 
(minus z0 x3) y3)) \to (eq nat y3 (plus x3 (S y1)))))))) H2 (S (plus z0 y1)) 
(plus_n_Sm z0 y1)) in (let H4 \def (eq_ind_r nat (plus x3 (S y1)) (\lambda 
(n: nat).(\forall (y3: nat).((le O z0) \to ((le x3 z0) \to ((eq nat (S (plus 
z0 y1)) (plus (minus z0 x3) y3)) \to (eq nat y3 n)))))) H3 (S (plus x3 y1)) 
(plus_n_Sm x3 y1)) in (H4 y2 (le_O_n z0) (le_S_n x3 z0 H0) H1)))))))))))) 
x2)) (\lambda (x2: nat).(\lambda (_: ((\forall (x3: nat).(\forall (y1: 
nat).(\forall (y2: nat).((le x2 (S z0)) \to ((le x3 (S z0)) \to ((eq nat 
(plus (minus (S z0) x2) y1) (plus (minus (S z0) x3) y2)) \to (eq nat (plus x2 
y2) (plus x3 y1)))))))))).(\lambda (x3: nat).(nat_ind (\lambda (n: 
nat).(\forall (y1: nat).(\forall (y2: nat).((le (S x2) (S z0)) \to ((le n (S 
z0)) \to ((eq nat (plus (minus (S z0) (S x2)) y1) (plus (minus (S z0) n) y2)) 
\to (eq nat (plus (S x2) y2) (plus n y1)))))))) (\lambda (y1: nat).(\lambda 
(y2: nat).(\lambda (H: (le (S x2) (S z0))).(\lambda (_: (le O (S 
z0))).(\lambda (H1: (eq nat (plus (minus z0 x2) y1) (S (plus z0 y2)))).(let 
H_y \def (IH x2 O y1 (S y2)) in (let H2 \def (eq_ind_r nat (minus z0 O) 
(\lambda (n: nat).((le x2 z0) \to ((le O z0) \to ((eq nat (plus (minus z0 x2) 
y1) (plus n (S y2))) \to (eq nat (plus x2 (S y2)) y1))))) H_y z0 (minus_n_O 
z0)) in (let H3 \def (eq_ind_r nat (plus z0 (S y2)) (\lambda (n: nat).((le x2 
z0) \to ((le O z0) \to ((eq nat (plus (minus z0 x2) y1) n) \to (eq nat (plus 
x2 (S y2)) y1))))) H2 (S (plus z0 y2)) (plus_n_Sm z0 y2)) in (let H4 \def 
(eq_ind_r nat (plus x2 (S y2)) (\lambda (n: nat).((le x2 z0) \to ((le O z0) 
\to ((eq nat (plus (minus z0 x2) y1) (S (plus z0 y2))) \to (eq nat n y1))))) 
H3 (S (plus x2 y2)) (plus_n_Sm x2 y2)) in (H4 (le_S_n x2 z0 H) (le_O_n z0) 
H1)))))))))) (\lambda (x4: nat).(\lambda (_: ((\forall (y1: nat).(\forall 
(y2: nat).((le (S x2) (S z0)) \to ((le x4 (S z0)) \to ((eq nat (plus (minus 
z0 x2) y1) (plus (match x4 with [O \Rightarrow (S z0) | (S l) \Rightarrow 
(minus z0 l)]) y2)) \to (eq nat (S (plus x2 y2)) (plus x4 
y1))))))))).(\lambda (y1: nat).(\lambda (y2: nat).(\lambda (H: (le (S x2) (S 
z0))).(\lambda (H0: (le (S x4) (S z0))).(\lambda (H1: (eq nat (plus (minus z0 
x2) y1) (plus (minus z0 x4) y2))).(f_equal nat nat S (plus x2 y2) (plus x4 
y1) (IH x2 x4 y1 y2 (le_S_n x2 z0 H) (le_S_n x4 z0 H0) H1))))))))) x3)))) 
x1)))) z).
(* COMMENTS
Initial nodes: 1495
END *)

theorem le_S_minus:
 \forall (d: nat).(\forall (h: nat).(\forall (n: nat).((le (plus d h) n) \to 
(le d (S (minus n h))))))
\def
 \lambda (d: nat).(\lambda (h: nat).(\lambda (n: nat).(\lambda (H: (le (plus 
d h) n)).(let H0 \def (le_trans d (plus d h) n (le_plus_l d h) H) in (let H1 
\def (eq_ind nat n (\lambda (n0: nat).(le d n0)) H0 (plus (minus n h) h) 
(le_plus_minus_sym h n (le_trans h (plus d h) n (le_plus_r d h) H))) in (le_S 
d (minus n h) (le_minus d n h H))))))).
(* COMMENTS
Initial nodes: 107
END *)

theorem lt_x_pred_y:
 \forall (x: nat).(\forall (y: nat).((lt x (pred y)) \to (lt (S x) y)))
\def
 \lambda (x: nat).(\lambda (y: nat).(nat_ind (\lambda (n: nat).((lt x (pred 
n)) \to (lt (S x) n))) (\lambda (H: (lt x O)).(lt_x_O x H (lt (S x) O))) 
(\lambda (n: nat).(\lambda (_: (((lt x (pred n)) \to (lt (S x) n)))).(\lambda 
(H0: (lt x n)).(le_S_n (S (S x)) (S n) (le_n_S (S (S x)) (S n) (le_n_S (S x) 
n H0)))))) y)).
(* COMMENTS
Initial nodes: 103
END *)

