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

include "ground_1/blt/defs.ma".

theorem lt_blt:
 \forall (x: nat).(\forall (y: nat).((lt y x) \to (eq bool (blt y x) true)))
\def
 \lambda (x: nat).(let TMP_2 \def (\lambda (n: nat).(\forall (y: nat).((lt y 
n) \to (let TMP_1 \def (blt y n) in (eq bool TMP_1 true))))) in (let TMP_13 
\def (\lambda (y: nat).(\lambda (H: (lt y O)).(let H0 \def (match H with 
[le_n \Rightarrow (\lambda (H0: (eq nat (S y) O)).(let TMP_8 \def (S y) in 
(let TMP_9 \def (\lambda (e: nat).(match e with [O \Rightarrow False | (S _) 
\Rightarrow True])) in (let H1 \def (eq_ind nat TMP_8 TMP_9 I O H0) in (let 
TMP_10 \def (blt y O) in (let TMP_11 \def (eq bool TMP_10 true) in (False_ind 
TMP_11 H1))))))) | (le_S m H0) \Rightarrow (\lambda (H1: (eq nat (S m) 
O)).(let TMP_3 \def (S m) in (let TMP_4 \def (\lambda (e: nat).(match e with 
[O \Rightarrow False | (S _) \Rightarrow True])) in (let H2 \def (eq_ind nat 
TMP_3 TMP_4 I O H1) in (let TMP_6 \def ((le (S y) m) \to (let TMP_5 \def (blt 
y O) in (eq bool TMP_5 true))) in (let TMP_7 \def (False_ind TMP_6 H2) in 
(TMP_7 H0)))))))]) in (let TMP_12 \def (refl_equal nat O) in (H0 TMP_12))))) 
in (let TMP_21 \def (\lambda (n: nat).(\lambda (H: ((\forall (y: nat).((lt y 
n) \to (eq bool (blt y n) true))))).(\lambda (y: nat).(let TMP_16 \def 
(\lambda (n0: nat).((lt n0 (S n)) \to (let TMP_14 \def (S n) in (let TMP_15 
\def (blt n0 TMP_14) in (eq bool TMP_15 true))))) in (let TMP_17 \def 
(\lambda (_: (lt O (S n))).(refl_equal bool true)) in (let TMP_20 \def 
(\lambda (n0: nat).(\lambda (_: (((lt n0 (S n)) \to (eq bool (match n0 with 
[O \Rightarrow true | (S m) \Rightarrow (blt m n)]) true)))).(\lambda (H1: 
(lt (S n0) (S n))).(let TMP_18 \def (S n0) in (let TMP_19 \def (le_S_n TMP_18 
n H1) in (H n0 TMP_19)))))) in (nat_ind TMP_16 TMP_17 TMP_20 y))))))) in 
(nat_ind TMP_2 TMP_13 TMP_21 x)))).

theorem le_bge:
 \forall (x: nat).(\forall (y: nat).((le x y) \to (eq bool (blt y x) false)))
\def
 \lambda (x: nat).(let TMP_2 \def (\lambda (n: nat).(\forall (y: nat).((le n 
y) \to (let TMP_1 \def (blt y n) in (eq bool TMP_1 false))))) in (let TMP_3 
\def (\lambda (y: nat).(\lambda (_: (le O y)).(refl_equal bool false))) in 
(let TMP_22 \def (\lambda (n: nat).(\lambda (H: ((\forall (y: nat).((le n y) 
\to (eq bool (blt y n) false))))).(\lambda (y: nat).(let TMP_6 \def (\lambda 
(n0: nat).((le (S n) n0) \to (let TMP_4 \def (S n) in (let TMP_5 \def (blt n0 
TMP_4) in (eq bool TMP_5 false))))) in (let TMP_19 \def (\lambda (H0: (le (S 
n) O)).(let H1 \def (match H0 with [le_n \Rightarrow (\lambda (H1: (eq nat (S 
n) O)).(let TMP_13 \def (S n) in (let TMP_14 \def (\lambda (e: nat).(match e 
with [O \Rightarrow False | (S _) \Rightarrow True])) in (let H2 \def (eq_ind 
nat TMP_13 TMP_14 I O H1) in (let TMP_15 \def (S n) in (let TMP_16 \def (blt 
O TMP_15) in (let TMP_17 \def (eq bool TMP_16 false) in (False_ind TMP_17 
H2)))))))) | (le_S m H1) \Rightarrow (\lambda (H2: (eq nat (S m) O)).(let 
TMP_7 \def (S m) in (let TMP_8 \def (\lambda (e: nat).(match e with [O 
\Rightarrow False | (S _) \Rightarrow True])) in (let H3 \def (eq_ind nat 
TMP_7 TMP_8 I O H2) in (let TMP_11 \def ((le (S n) m) \to (let TMP_9 \def (S 
n) in (let TMP_10 \def (blt O TMP_9) in (eq bool TMP_10 false)))) in (let 
TMP_12 \def (False_ind TMP_11 H3) in (TMP_12 H1)))))))]) in (let TMP_18 \def 
(refl_equal nat O) in (H1 TMP_18)))) in (let TMP_21 \def (\lambda (n0: 
nat).(\lambda (_: (((le (S n) n0) \to (eq bool (blt n0 (S n)) 
false)))).(\lambda (H1: (le (S n) (S n0))).(let TMP_20 \def (le_S_n n n0 H1) 
in (H n0 TMP_20))))) in (nat_ind TMP_6 TMP_19 TMP_21 y))))))) in (nat_ind 
TMP_2 TMP_3 TMP_22 x)))).

theorem blt_lt:
 \forall (x: nat).(\forall (y: nat).((eq bool (blt y x) true) \to (lt y x)))
\def
 \lambda (x: nat).(let TMP_1 \def (\lambda (n: nat).(\forall (y: nat).((eq 
bool (blt y n) true) \to (lt y n)))) in (let TMP_6 \def (\lambda (y: 
nat).(\lambda (H: (eq bool (blt y O) true)).(let H0 \def (match H with 
[refl_equal \Rightarrow (\lambda (H0: (eq bool (blt y O) true)).(let TMP_2 
\def (blt y O) in (let TMP_3 \def (\lambda (e: bool).(match e with [true 
\Rightarrow False | false \Rightarrow True])) in (let H1 \def (eq_ind bool 
TMP_2 TMP_3 I true H0) in (let TMP_4 \def (lt y O) in (False_ind TMP_4 
H1))))))]) in (let TMP_5 \def (refl_equal bool true) in (H0 TMP_5))))) in 
(let TMP_19 \def (\lambda (n: nat).(\lambda (H: ((\forall (y: nat).((eq bool 
(blt y n) true) \to (lt y n))))).(\lambda (y: nat).(let TMP_8 \def (\lambda 
(n0: nat).((eq bool (blt n0 (S n)) true) \to (let TMP_7 \def (S n) in (lt n0 
TMP_7)))) in (let TMP_16 \def (\lambda (_: (eq bool true true)).(let TMP_9 
\def (S O) in (let TMP_10 \def (S n) in (let TMP_11 \def (S O) in (let TMP_12 
\def (S n) in (let TMP_13 \def (le_O_n n) in (let TMP_14 \def (le_n_S O n 
TMP_13) in (let TMP_15 \def (le_n_S TMP_11 TMP_12 TMP_14) in (le_S_n TMP_9 
TMP_10 TMP_15))))))))) in (let TMP_18 \def (\lambda (n0: nat).(\lambda (_: 
(((eq bool (match n0 with [O \Rightarrow true | (S m) \Rightarrow (blt m n)]) 
true) \to (lt n0 (S n))))).(\lambda (H1: (eq bool (blt n0 n) true)).(let 
TMP_17 \def (H n0 H1) in (lt_n_S n0 n TMP_17))))) in (nat_ind TMP_8 TMP_16 
TMP_18 y))))))) in (nat_ind TMP_1 TMP_6 TMP_19 x)))).

theorem bge_le:
 \forall (x: nat).(\forall (y: nat).((eq bool (blt y x) false) \to (le x y)))
\def
 \lambda (x: nat).(let TMP_1 \def (\lambda (n: nat).(\forall (y: nat).((eq 
bool (blt y n) false) \to (le n y)))) in (let TMP_2 \def (\lambda (y: 
nat).(\lambda (_: (eq bool (blt y O) false)).(le_O_n y))) in (let TMP_20 \def 
(\lambda (n: nat).(\lambda (H: ((\forall (y: nat).((eq bool (blt y n) false) 
\to (le n y))))).(\lambda (y: nat).(let TMP_4 \def (\lambda (n0: nat).((eq 
bool (blt n0 (S n)) false) \to (let TMP_3 \def (S n) in (le TMP_3 n0)))) in 
(let TMP_11 \def (\lambda (H0: (eq bool (blt O (S n)) false)).(let H1 \def 
(match H0 with [refl_equal \Rightarrow (\lambda (H1: (eq bool (blt O (S n)) 
false)).(let TMP_5 \def (S n) in (let TMP_6 \def (blt O TMP_5) in (let TMP_7 
\def (\lambda (e: bool).(match e with [true \Rightarrow True | false 
\Rightarrow False])) in (let H2 \def (eq_ind bool TMP_6 TMP_7 I false H1) in 
(let TMP_8 \def (S n) in (let TMP_9 \def (le TMP_8 O) in (False_ind TMP_9 
H2))))))))]) in (let TMP_10 \def (refl_equal bool false) in (H1 TMP_10)))) in 
(let TMP_19 \def (\lambda (n0: nat).(\lambda (_: (((eq bool (blt n0 (S n)) 
false) \to (le (S n) n0)))).(\lambda (H1: (eq bool (blt (S n0) (S n)) 
false)).(let TMP_12 \def (S n) in (let TMP_13 \def (S n0) in (let TMP_14 \def 
(S n) in (let TMP_15 \def (S n0) in (let TMP_16 \def (H n0 H1) in (let TMP_17 
\def (le_n_S n n0 TMP_16) in (let TMP_18 \def (le_n_S TMP_14 TMP_15 TMP_17) 
in (le_S_n TMP_12 TMP_13 TMP_18))))))))))) in (nat_ind TMP_4 TMP_11 TMP_19 
y))))))) in (nat_ind TMP_1 TMP_2 TMP_20 x)))).

