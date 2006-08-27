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

(* Problematic objects for disambiguation/typechecking ********************)
(* FG: PLEASE COMMENT THE NON WORKING OBJECTS *****************************)

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/problems".

include "legacy/coq.ma".

(*

(* Problem 1: disambiguation/typechecking very slow *)

(*  - the "match" on "e" seems to be at the heart of the problem
 *  - all declararations are on "net" except the one of "e"
 *  - all equalities are on "nut"
 *  - there are two "nit"
 *  - all the oters instances of the natral numbers set are "nat"
 *)
 
alias id "nut" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias id "net" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias id "nit" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".

theorem nat_dec_patched: 
 \forall (n1: net).(\forall (n2: net).(or (eq nut n1 n2) ((eq nut n1 n2) \to (\forall (P: Prop).P))))
\def  
 \lambda (n1: net).(nat_ind (\lambda (n: net).(\forall (n2: net).(or (eq nut n n2) ((eq nut n n2) \to (\forall (P: Prop).P))))) (\lambda (n2: net).(nat_ind (\lambda (n: net).(or (eq nut O n) ((eq nut O n) \to (\forall (P: Prop).P)))) (or_introl (eq nut O O) ((eq nut O O) \to (\forall (P: Prop).P)) (refl_equal nat O)) (\lambda (n: net).(\lambda (_: (or (eq nut O n) ((eq nut O n) \to (\forall (P: Prop).P)))).(or_intror (eq nut O (S n)) ((eq nut O (S n)) \to (\forall (P: Prop).P)) (\lambda (H0: (eq nut O (S n))).(\lambda (P: Prop).(let H1 \def (eq_ind nat O (\lambda (ee: net).(match ee return Prop with [O \Rightarrow True | (S _) \Rightarrow False])) I (S n) H0) in (False_ind P H1))))))) n2)) (\lambda (n: net).(\lambda (H: ((\forall (n2: net).(or (eq nut n n2) ((eq nut n n2) \to (\forall (P: Prop).P)))))).(\lambda (n2: net).(nat_ind (\lambda (n0: net).(or (eq nut (S n) n0) ((eq nut (S n) n0) \to (\forall (P: Prop).P)))) (or_intror (eq nut (S n) O) ((eq nut (S n) O) \to (\forall (P: Prop).P)) (\lambda (H0: (eq nut (S n) O)).(\lambda (P: Prop).(let H1 \def (eq_ind nat (S n) (\lambda (ee: net).(match ee return Prop with [O \Rightarrow False | (S _) \Rightarrow True])) I O H0) in (False_ind P H1))))) (\lambda (n0: net).(\lambda (H0: (or (eq nut (S n) n0) ((eq nut (S n) n0) \to (\forall (P: Prop).P)))).(or_ind (eq nut n n0) ((eq nut n n0) \to (\forall (P: Prop).P)) (or (eq nut (S n) (S n0)) ((eq nut (S n) (S n0)) \to (\forall (P: Prop).P))) (\lambda (H1: (eq nut n n0)).(let H2 \def (eq_ind_r nat n0 (\lambda (n0: net).(or (eq nut (S n) n0) ((eq nut (S n) n0) \to (\forall (P: Prop).P)))) H0 n H1) in (eq_ind nat n (\lambda (n3: net).(or (eq nut (S n) (S n3)) ((eq nut (S n) (S n3)) \to (\forall (P: Prop).P)))) (or_introl (eq nut (S n) (S n)) ((eq nut (S n) (S n)) \to (\forall (P: Prop).P)) (refl_equal nat (S n))) n0 H1))) (\lambda (H1: (((eq nut n n0) \to (\forall (P: Prop).P)))).(or_intror (eq nut (S n) (S n0)) ((eq nut (S n) (S n0)) \to (\forall (P: Prop).P)) (\lambda (H2: (eq nut (S n) (S n0))).(\lambda (P: Prop).(let H3 \def (f_equal nat nat (\lambda (e: nit).(match (e:net) return nit with [O \Rightarrow n | (S n) \Rightarrow n])) (S n) (S n0) H2) in (let H4 \def (eq_ind_r nat n0 (\lambda (n0: net).((eq nut n n0) \to (\forall (P: Prop).P))) H1 n H3) in (let H5 \def (eq_ind_r nat n0 (\lambda (n0: net).(or (eq nut (S n) n0) ((eq nut (S n) n0) \to (\forall (P: Prop).P)))) H0 n H3) in (H4 (refl_equal nat n) P)))))))) (H n0)))) n2)))) n1).

(* Problem 2: several disambiguation errors *)

(*  Same object of problem 1 with "nut", "net", "nit" replaced by "nat" 
 *)

theorem nat_dec_real: 
 \forall (n1: nat).(\forall (n2: nat).(or (eq nat n1 n2) ((eq nat n1 n2) \to (\forall (P: Prop).P))))
\def  
 \lambda (n1: nat).(nat_ind (\lambda (n: nat).(\forall (n2: nat).(or (eq nat n n2) ((eq nat n n2) \to (\forall (P: Prop).P))))) (\lambda (n2: nat).(nat_ind (\lambda (n: nat).(or (eq nat O n) ((eq nat O n) \to (\forall (P: Prop).P)))) (or_introl (eq nat O O) ((eq nat O O) \to (\forall (P: Prop).P)) (refl_equal nat O)) (\lambda (n: nat).(\lambda (_: (or (eq nat O n) ((eq nat O n) \to (\forall (P: Prop).P)))).(or_intror (eq nat O (S n)) ((eq nat O (S n)) \to (\forall (P: Prop).P)) (\lambda (H0: (eq nat O (S n))).(\lambda (P: Prop).(let H1 \def (eq_ind nat O (\lambda (ee: nat).(match ee return Prop with [O \Rightarrow True | (S _) \Rightarrow False])) I (S n) H0) in (False_ind P H1))))))) n2)) (\lambda (n: nat).(\lambda (H: ((\forall (n2: nat).(or (eq nat n n2) ((eq nat n n2) \to (\forall (P: Prop).P)))))).(\lambda (n2: nat).(nat_ind (\lambda (n0: nat).(or (eq nat (S n) n0) ((eq nat (S n) n0) \to (\forall (P: Prop).P)))) (or_intror (eq nat (S n) O) ((eq nat (S n) O) \to (\forall (P: Prop).P)) (\lambda (H0: (eq nat (S n) O)).(\lambda (P: Prop).(let H1 \def (eq_ind nat (S n) (\lambda (ee: nat).(match ee return Prop with [O \Rightarrow False | (S _) \Rightarrow True])) I O H0) in (False_ind P H1))))) (\lambda (n0: nat).(\lambda (H0: (or (eq nat (S n) n0) ((eq nat (S n) n0) \to (\forall (P: Prop).P)))).(or_ind (eq nat n n0) ((eq nat n n0) \to (\forall (P: Prop).P)) (or (eq nat (S n) (S n0)) ((eq nat (S n) (S n0)) \to (\forall (P: Prop).P))) (\lambda (H1: (eq nat n n0)).(let H2 \def (eq_ind_r nat n0 (\lambda (n0: nat).(or (eq nat (S n) n0) ((eq nat (S n) n0) \to (\forall (P: Prop).P)))) H0 n H1) in (eq_ind nat n (\lambda (n3: nat).(or (eq nat (S n) (S n3)) ((eq nat (S n) (S n3)) \to (\forall (P: Prop).P)))) (or_introl (eq nat (S n) (S n)) ((eq nat (S n) (S n)) \to (\forall (P: Prop).P)) (refl_equal nat (S n))) n0 H1))) (\lambda (H1: (((eq nat n n0) \to (\forall (P: Prop).P)))).(or_intror (eq nat (S n) (S n0)) ((eq nat (S n) (S n0)) \to (\forall (P: Prop).P)) (\lambda (H2: (eq nat (S n) (S n0))).(\lambda (P: Prop).(let H3 \def (f_equal nat nat (\lambda (e: nat).(match (e:nat) return nat with [O \Rightarrow n | (S n) \Rightarrow n])) (S n) (S n0) H2) in (let H4 \def (eq_ind_r nat n0 (\lambda (n0: nat).((eq nat n n0) \to (\forall (P: Prop).P))) H1 n H3) in (let H5 \def (eq_ind_r nat n0 (\lambda (n0: nat).(or (eq nat (S n) n0) ((eq nat (S n) n0) \to (\forall (P: Prop).P)))) H0 n H3) in (H4 (refl_equal nat n) P)))))))) (H n0)))) n2)))) n1).

(* Problem 3: big problems with letins *)

theorem simpl_plus_r:
 \forall (n: nat).(\forall (m: nat).(\forall (p: nat).((eq nat (plus m n) (plus p n)) \to (eq nat m p))))
\def
 \lambda (n: nat).(\lambda (m: nat).(\lambda (p: nat).(\lambda (H: (eq nat (plus m n) (plus p n))).(plus_reg_l n m p (eq_ind_r nat (plus m n) (\lambda (n0: nat).(eq nat n0 (plus n p))) (eq_ind_r nat (plus p n) (\lambda (n0: nat).(eq nat n0 (plus n p))) (sym_eq nat (plus n p) (plus p n) (plus_comm n p)) (plus m n) H) (plus n m) (plus_comm n m)))))).

(* Problem 4: very slow and big problems with letins *)

theorem plus_O:
 \forall (x: nat).(\forall (y: nat).((eq nat (plus x y) O) \to ((cic:/Coq/Init/Logic/and.ind#xpointer(1/1)) (eq nat x O) (eq nat y O))))
\def
 \lambda (x: nat).(nat_ind (\lambda (n: nat).(\forall (y: nat).((eq nat (plus n y) O) \to ((cic:/Coq/Init/Logic/and.ind#xpointer(1/1)) (eq nat n O) (eq nat y O))))) (\lambda (y: nat).(\lambda (H: (eq nat (plus O y) O)).(conj (eq nat O O) (eq nat y O) (refl_equal nat O) H))) (\lambda (n: nat).(\lambda (_: ((\forall (y: nat).((eq nat (plus n y) O) \to ((cic:/Coq/Init/Logic/and.ind#xpointer(1/1)) (eq nat n O) (eq nat y O)))))).(\lambda (y: nat).(\lambda (H0: (eq nat (plus (S n) y) O)).(let H1 \def (match H0 return (\lambda (n0: nat).((eq nat n0 O) \to ((cic:/Coq/Init/Logic/and.ind#xpointer(1/1)) (eq nat (S n) O) (eq nat y O)))) with [refl_equal \Rightarrow (\lambda (H1: (eq nat (plus (S n) y) O)).(let H2 \def (eq_ind nat (plus (S n) y) (\lambda (e: nat).(match e return Prop with [O \Rightarrow False | (S _) \Rightarrow True])) I O H1) in (False_ind ((cic:/Coq/Init/Logic/and.ind#xpointer(1/1)) (eq nat (S n) O) (eq nat y O)) H2)))]) in (H1 (refl_equal nat O))))))) x).

(* Problem 5: slow and problems with letins *)

theorem minus_Sx_SO:
 \forall (x: nat).(eq nat (minus (S x) (S O)) x)
\def
 \lambda (x: nat).(eq_ind nat x (\lambda (n: nat).(eq nat n x)) (refl_equal nat x) (minus x O) (minus_n_O x)).

(* Problem 6: disambiguation problems *)

theorem eq_nat_dec:
 \forall (i: nat).(\forall (j: nat).(or (not (eq nat i j)) (eq nat i j)))
\def
 \lambda (i: nat).(nat_ind (\lambda (n: nat).(\forall (j: nat).(or (not (eq nat n j)) (eq nat n j)))) (\lambda (j: nat).(nat_ind (\lambda (n: nat).(or (not (eq nat O n)) (eq nat O n))) (or_intror (not (eq nat O O)) (eq nat O O) (refl_equal nat O)) (\lambda (n: nat).(\lambda (_: (or (not (eq nat O n)) (eq nat O n))).(or_introl (not (eq nat O (S n))) (eq nat O (S n)) (O_S n)))) j)) (\lambda (n: nat).(\lambda (H: ((\forall (j: nat).(or (not (eq nat n j)) (eq nat n j))))).(\lambda (j: nat).(nat_ind (\lambda (n0: nat).(or (not (eq nat (S n) n0)) (eq nat (S n) n0))) (or_introl (not (eq nat (S n) O)) (eq nat (S n) O) (sym_not_eq nat O (S n) (O_S n))) (\lambda (n0: nat).(\lambda (_: (or (not (eq nat (S n) n0)) (eq nat (S n) n0))).(or_ind (not (eq nat n n0)) (eq nat n n0) (or (not (eq nat (S n) (S n0))) (eq nat (S n) (S n0))) (\lambda (H1: (not (eq nat n n0))).(or_introl (not (eq nat (S n) (S n0))) (eq nat (S n) (S n0)) (not_eq_S n n0 H1))) (\lambda (H1: (eq nat n n0)).(or_intror (not (eq nat (S n) (S n0))) (eq nat (S n) (S n0)) (f_equal nat nat S n n0 H1))) (H n0)))) j)))) i).

(* Problem 7: very slow *)

theorem le_false:
 \forall (m: nat).(\forall (n: nat).(\forall (P: Prop).((le m n) \to ((le (S n) m) \to P))))
\def
 \lambda (m: nat).(nat_ind (\lambda (n: nat).(\forall (n0: nat).(\forall (P: Prop).((le n n0) \to ((le (S n0) n) \to P))))) (\lambda (n: nat).(\lambda (P: Prop).(\lambda (_: (le O n)).(\lambda (H0: (le (S n) O)).(let H1 \def (match H0 return (\lambda (n: nat).((eq nat n O) \to P)) with [le_n \Rightarrow (\lambda (H1: (eq nat (S n) O)).(let H2 \def (eq_ind nat (S n) (\lambda (e: nat).(match e return Prop with [O \Rightarrow False | (S _) \Rightarrow True])) I O H1) in (False_ind P H2))) | (le_S m H1) \Rightarrow (\lambda (H2: (eq nat (S m) O)).((let H3 \def (eq_ind nat (S m) (\lambda (e: nat).(match e return Prop with [O \Rightarrow False | (S _) \Rightarrow True])) I O H2) in (False_ind ((le (S n) m) \to P) H3)) H1))]) in (H1 (refl_equal nat O))))))) (\lambda (n: nat).(\lambda (H: ((\forall (n0: nat).(\forall (P: Prop).((le n n0) \to ((le (S n0) n) \to P)))))).(\lambda (n0: nat).(nat_ind (\lambda (n1: nat).(\forall (P: Prop).((le (S n) n1) \to ((le (S n1) (S n)) \to P)))) (\lambda (P: Prop).(\lambda (H0: (le (S n) O)).(\lambda (_: (le (S O) (S n))).(let H2 \def (match H0 return (\lambda (n: nat).((eq nat n O) \to P)) with [le_n \Rightarrow (\lambda (H2: (eq nat (S n) O)).(let H3 \def (eq_ind nat (S n) (\lambda (e: nat).(match e return Prop with [O \Rightarrow False | (S _) \Rightarrow True])) I O H2) in (False_ind P H3))) | (le_S m H2) \Rightarrow (\lambda (H3: (eq nat (S m) O)).((let H4 \def (eq_ind nat (S m) (\lambda (e: nat).(match e return Prop with [O \Rightarrow False | (S _) \Rightarrow True])) I O H3) in (False_ind ((le (S n) m) \to P) H4)) H2))]) in (H2 (refl_equal nat O)))))) (\lambda (n1: nat).(\lambda (_: ((\forall (P: Prop).((le (S n) n1) \to ((le (S n1) (S n)) \to P))))).(\lambda (P: Prop).(\lambda (H1: (le (S n) (S n1))).(\lambda (H2: (le (S (S n1)) (S n))).(H n1 P (le_S_n n n1 H1) (le_S_n (S n1) n H2))))))) n0)))) m).

(* Problem 8: disambiguation problems *)

theorem le_minus_minus:
 \forall (x: nat).(\forall (y: nat).((le x y) \to (\forall (z: nat).((le y z) \to (le (minus y x) (minus z x))))))
\def
 \lambda (x: nat).(\lambda (y: nat).(\lambda (H: (le x y)).(\lambda (z: nat).(\lambda (H0: (le y z)).(plus_le_reg_l x (minus y x) (minus z x) (eq_ind_r nat y (\lambda (n: nat).(le n (plus x (minus z x)))) (eq_ind_r nat z (\lambda (n: nat).(le y n)) H0 (plus x (minus z x)) (le_plus_minus_r x z (le_trans x y z H H0))) (plus x (minus y x)) (le_plus_minus_r x y H))))))).

(* Problem 9: very slow and disambiguation problems *)

theorem le_minus_plus:
 \forall (z: nat).(\forall (x: nat).((le z x) \to (\forall (y: nat).(eq nat (minus (plus x y) z) (plus (minus x z) y)))))
\def
 \lambda (z: nat).(nat_ind (\lambda (n: nat).(\forall (x: nat).((le n x) \to (\forall (y: nat).(eq nat (minus (plus x y) n) (plus (minus x n) y)))))) (\lambda (x: nat).(\lambda (H: (le O x)).(let H0 \def (match H return (\lambda (n: nat).((eq nat n x) \to (\forall (y: nat).(eq nat (minus (plus x y) O) (plus (minus x O) y))))) with [le_n \Rightarrow (\lambda (H0: (eq nat O x)).(eq_ind nat O (\lambda (n: nat).(\forall (y: nat).(eq nat (minus (plus n y) O) (plus (minus n O) y)))) (\lambda (y: nat).(sym_eq nat (plus (minus O O) y) (minus (plus O y) O) (minus_n_O (plus O y)))) x H0)) | (le_S m H0) \Rightarrow (\lambda (H1: (eq nat (S m) x)).(eq_ind nat (S m) (\lambda (n: nat).((le O m) \to (\forall (y: nat).(eq nat (minus (plus n y) O) (plus (minus n O) y))))) (\lambda (_: (le O m)).(\lambda (y: nat).(refl_equal nat (plus (minus (S m) O) y)))) x H1 H0))]) in (H0 (refl_equal nat x))))) (\lambda (z0: nat).(\lambda (H: ((\forall (x: nat).((le z0 x) \to (\forall (y: nat).(eq nat (minus (plus x y) z0) (plus (minus x z0) y))))))).(\lambda (x: nat).(nat_ind (\lambda (n: nat).((le (S z0) n) \to (\forall (y: nat).(eq nat (minus (plus n y) (S z0)) (plus (minus n (S z0)) y))))) (\lambda (H0: (le (S z0) O)).(\lambda (y: nat).(let H1 \def (match H0 return (\lambda (n: nat).((eq nat n O) \to (eq nat (minus (plus O y) (S z0)) (plus (minus O (S z0)) y)))) with [le_n \Rightarrow (\lambda (H1: (eq nat (S z0) O)).(let H2 \def (eq_ind nat (S z0) (\lambda (e: nat).(match e return Prop with [O \Rightarrow False | (S _) \Rightarrow True])) I O H1) in (False_ind (eq nat (minus (plus O y) (S z0)) (plus (minus O (S z0)) y)) H2))) | (le_S m H1) \Rightarrow (\lambda (H2: (eq nat (S m) O)).((let H3 \def (eq_ind nat (S m) (\lambda (e: nat).(match e return Prop with [O \Rightarrow False | (S _) \Rightarrow True])) I O H2) in (False_ind ((le (S z0) m) \to (eq nat (minus (plus O y) (S z0)) (plus (minus O (S z0)) y))) H3)) H1))]) in (H1 (refl_equal nat O))))) (\lambda (n: nat).(\lambda (_: (((le (S z0) n) \to (\forall (y: nat).(eq nat (minus (plus n y) (S z0)) (plus (minus n (S z0)) y)))))).(\lambda (H1: (le (S z0) (S n))).(\lambda (y: nat).(H n (le_S_n z0 n H1) y))))) x)))) z).

(* Problem 10: disambiguation problems *)

theorem le_gen_S:
 \forall (m: nat).(\forall (x: nat).((le (S m) x) \to (ex2 nat (\lambda (n: nat).(eq nat x (S n))) (\lambda (n: nat).(le m n)))))
\def
 \lambda (m: nat).(\lambda (x: nat).(\lambda (H: (le (S m) x)).(let H0 \def (match H return (\lambda (n: nat).((eq nat n x) \to (ex2 nat (\lambda (n0: nat).(eq nat x (S n0))) (\lambda (n0: nat).(le m n0))))) with [le_n \Rightarrow (\lambda (H0: (eq nat (S m) x)).(eq_ind nat (S m) (\lambda (n: nat).(ex2 nat (\lambda (n0: nat).(eq nat n (S n0))) (\lambda (n0: nat).(le m n0)))) (ex_intro2 nat (\lambda (n: nat).(eq nat (S m) (S n))) (\lambda (n: nat).(le m n)) m (refl_equal nat (S m)) (le_n m)) x H0)) | (le_S m0 H0) \Rightarrow (\lambda (H1: (eq nat (S m0) x)).(eq_ind nat (S m0) (\lambda (n: nat).((le (S m) m0) \to (ex2 nat (\lambda (n0: nat).(eq nat n (S n0))) (\lambda (n0: nat).(le m n0))))) (\lambda (H2: (le (S m) m0)).(ex_intro2 nat (\lambda (n: nat).(eq nat (S m0) (S n))) (\lambda (n: nat).(le m n)) m0 (refl_equal nat (S m0)) (le_S_n m m0 (le_S (S m) m0 H2)))) x H1 H0))]) in (H0 (refl_equal nat x))))).

(* Problem 11: unguarded recursion in the following objects *)

THeads, weight_map, CTail, lref_map, lifts, lifts1, next_plus, asucc, aplus,
sns3, sc3

(* Problem 12: assertion failure raised by type checker on this object *)

tau1

*)
