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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/problems".

include "legacy/coq.ma".

(* Problem 1: disambiguation/typechecking seems not to terminate *)

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
