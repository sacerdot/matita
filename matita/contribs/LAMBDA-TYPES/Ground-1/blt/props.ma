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

include "Ground-1/blt/defs.ma".

theorem lt_blt:
 \forall (x: nat).(\forall (y: nat).((lt y x) \to (eq bool (blt y x) true)))
\def
 \lambda (x: nat).(nat_ind (\lambda (n: nat).(\forall (y: nat).((lt y n) \to 
(eq bool (blt y n) true)))) (\lambda (y: nat).(\lambda (H: (lt y O)).(let H0 
\def (match H in le return (\lambda (n: nat).(\lambda (_: (le ? n)).((eq nat 
n O) \to (eq bool (blt y O) true)))) with [le_n \Rightarrow (\lambda (H0: (eq 
nat (S y) O)).(let H1 \def (eq_ind nat (S y) (\lambda (e: nat).(match e in 
nat return (\lambda (_: nat).Prop) with [O \Rightarrow False | (S _) 
\Rightarrow True])) I O H0) in (False_ind (eq bool (blt y O) true) H1))) | 
(le_S m H0) \Rightarrow (\lambda (H1: (eq nat (S m) O)).((let H2 \def (eq_ind 
nat (S m) (\lambda (e: nat).(match e in nat return (\lambda (_: nat).Prop) 
with [O \Rightarrow False | (S _) \Rightarrow True])) I O H1) in (False_ind 
((le (S y) m) \to (eq bool (blt y O) true)) H2)) H0))]) in (H0 (refl_equal 
nat O))))) (\lambda (n: nat).(\lambda (H: ((\forall (y: nat).((lt y n) \to 
(eq bool (blt y n) true))))).(\lambda (y: nat).(nat_ind (\lambda (n0: 
nat).((lt n0 (S n)) \to (eq bool (blt n0 (S n)) true))) (\lambda (_: (lt O (S 
n))).(refl_equal bool true)) (\lambda (n0: nat).(\lambda (_: (((lt n0 (S n)) 
\to (eq bool (match n0 with [O \Rightarrow true | (S m) \Rightarrow (blt m 
n)]) true)))).(\lambda (H1: (lt (S n0) (S n))).(H n0 (le_S_n (S n0) n H1))))) 
y)))) x).
(* COMMENTS
Initial nodes: 291
END *)

theorem le_bge:
 \forall (x: nat).(\forall (y: nat).((le x y) \to (eq bool (blt y x) false)))
\def
 \lambda (x: nat).(nat_ind (\lambda (n: nat).(\forall (y: nat).((le n y) \to 
(eq bool (blt y n) false)))) (\lambda (y: nat).(\lambda (_: (le O 
y)).(refl_equal bool false))) (\lambda (n: nat).(\lambda (H: ((\forall (y: 
nat).((le n y) \to (eq bool (blt y n) false))))).(\lambda (y: nat).(nat_ind 
(\lambda (n0: nat).((le (S n) n0) \to (eq bool (blt n0 (S n)) false))) 
(\lambda (H0: (le (S n) O)).(let H1 \def (match H0 in le return (\lambda (n0: 
nat).(\lambda (_: (le ? n0)).((eq nat n0 O) \to (eq bool (blt O (S n)) 
false)))) with [le_n \Rightarrow (\lambda (H1: (eq nat (S n) O)).(let H2 \def 
(eq_ind nat (S n) (\lambda (e: nat).(match e in nat return (\lambda (_: 
nat).Prop) with [O \Rightarrow False | (S _) \Rightarrow True])) I O H1) in 
(False_ind (eq bool (blt O (S n)) false) H2))) | (le_S m H1) \Rightarrow 
(\lambda (H2: (eq nat (S m) O)).((let H3 \def (eq_ind nat (S m) (\lambda (e: 
nat).(match e in nat return (\lambda (_: nat).Prop) with [O \Rightarrow False 
| (S _) \Rightarrow True])) I O H2) in (False_ind ((le (S n) m) \to (eq bool 
(blt O (S n)) false)) H3)) H1))]) in (H1 (refl_equal nat O)))) (\lambda (n0: 
nat).(\lambda (_: (((le (S n) n0) \to (eq bool (blt n0 (S n)) 
false)))).(\lambda (H1: (le (S n) (S n0))).(H n0 (le_S_n n n0 H1))))) y)))) 
x).
(* COMMENTS
Initial nodes: 293
END *)

theorem blt_lt:
 \forall (x: nat).(\forall (y: nat).((eq bool (blt y x) true) \to (lt y x)))
\def
 \lambda (x: nat).(nat_ind (\lambda (n: nat).(\forall (y: nat).((eq bool (blt 
y n) true) \to (lt y n)))) (\lambda (y: nat).(\lambda (H: (eq bool (blt y O) 
true)).(let H0 \def (match H in eq return (\lambda (b: bool).(\lambda (_: (eq 
? ? b)).((eq bool b true) \to (lt y O)))) with [refl_equal \Rightarrow 
(\lambda (H0: (eq bool (blt y O) true)).(let H1 \def (eq_ind bool (blt y O) 
(\lambda (e: bool).(match e in bool return (\lambda (_: bool).Prop) with 
[true \Rightarrow False | false \Rightarrow True])) I true H0) in (False_ind 
(lt y O) H1)))]) in (H0 (refl_equal bool true))))) (\lambda (n: nat).(\lambda 
(H: ((\forall (y: nat).((eq bool (blt y n) true) \to (lt y n))))).(\lambda 
(y: nat).(nat_ind (\lambda (n0: nat).((eq bool (blt n0 (S n)) true) \to (lt 
n0 (S n)))) (\lambda (_: (eq bool true true)).(le_S_n (S O) (S n) (le_n_S (S 
O) (S n) (le_n_S O n (le_O_n n))))) (\lambda (n0: nat).(\lambda (_: (((eq 
bool (match n0 with [O \Rightarrow true | (S m) \Rightarrow (blt m n)]) true) 
\to (lt n0 (S n))))).(\lambda (H1: (eq bool (blt n0 n) true)).(lt_n_S n0 n (H 
n0 H1))))) y)))) x).
(* COMMENTS
Initial nodes: 252
END *)

theorem bge_le:
 \forall (x: nat).(\forall (y: nat).((eq bool (blt y x) false) \to (le x y)))
\def
 \lambda (x: nat).(nat_ind (\lambda (n: nat).(\forall (y: nat).((eq bool (blt 
y n) false) \to (le n y)))) (\lambda (y: nat).(\lambda (_: (eq bool (blt y O) 
false)).(le_O_n y))) (\lambda (n: nat).(\lambda (H: ((\forall (y: nat).((eq 
bool (blt y n) false) \to (le n y))))).(\lambda (y: nat).(nat_ind (\lambda 
(n0: nat).((eq bool (blt n0 (S n)) false) \to (le (S n) n0))) (\lambda (H0: 
(eq bool (blt O (S n)) false)).(let H1 \def (match H0 in eq return (\lambda 
(b: bool).(\lambda (_: (eq ? ? b)).((eq bool b false) \to (le (S n) O)))) 
with [refl_equal \Rightarrow (\lambda (H1: (eq bool (blt O (S n)) 
false)).(let H2 \def (eq_ind bool (blt O (S n)) (\lambda (e: bool).(match e 
in bool return (\lambda (_: bool).Prop) with [true \Rightarrow True | false 
\Rightarrow False])) I false H1) in (False_ind (le (S n) O) H2)))]) in (H1 
(refl_equal bool false)))) (\lambda (n0: nat).(\lambda (_: (((eq bool (blt n0 
(S n)) false) \to (le (S n) n0)))).(\lambda (H1: (eq bool (blt (S n0) (S n)) 
false)).(le_S_n (S n) (S n0) (le_n_S (S n) (S n0) (le_n_S n n0 (H n0 
H1))))))) y)))) x).
(* COMMENTS
Initial nodes: 262
END *)

