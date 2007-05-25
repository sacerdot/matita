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

set "baseuri" "cic:/matita/tests/fguidi/".
include "../legacy/coq.ma".

alias id "O" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/1)".
alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias id "S" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/2)".
alias id "le" = "cic:/matita/fguidi/le.ind#xpointer(1/1)".
alias id "False_ind" = "cic:/Coq/Init/Logic/False_ind.con".
alias id "I" = "cic:/Coq/Init/Logic/True.ind#xpointer(1/1/1)". 
alias id "ex_intro" = "cic:/Coq/Init/Logic/ex.ind#xpointer(1/1/1)".
alias id "False" = "cic:/Coq/Init/Logic/False.ind#xpointer(1/1)".
alias id "True" = "cic:/Coq/Init/Logic/True.ind#xpointer(1/1)".

alias symbol "and" (instance 0) = "Coq's logical and".
alias symbol "eq" (instance 0) = "Coq's leibnitz's equality".
alias symbol "exists" (instance 0) = "Coq's exists".

definition is_S: nat \to Prop \def
   \lambda n. match n with 
      [ O     \Rightarrow False
      | (S n) \Rightarrow True
      ].

definition pred: nat \to nat \def
   \lambda n. match n with
      [ O     \Rightarrow O
      | (S n) \Rightarrow n
      ]. 

theorem eq_gen_S_O: \forall x. (S x = O) \to \forall P:Prop. P.
intros. apply False_ind. cut (is_S O). elim Hcut. rewrite < H. apply I.
qed.

theorem eq_gen_S_O_cc: (\forall P:Prop. P) \to \forall x. (S x = O).
intros. apply H.
qed.

theorem eq_gen_S_S: \forall m,n. (S m) = (S n) \to m = n. 
intros. cut ((pred (S m)) = (pred (S n))). 
assumption. elim H. auto paramodulation.
qed.

theorem eq_gen_S_S_cc: \forall m,n. m = n \to (S m) = (S n).
intros. elim H. auto paramodulation.
qed.

inductive le: nat \to nat \to Prop \def
     le_zero: \forall n. (le O n)
   | le_succ: \forall m, n. (le m n) \to (le (S m) (S n)).

theorem le_refl: \forall x. (le x x).
intros. elim x; auto new.
qed.

theorem le_gen_x_O_aux: \forall x, y. (le x y) \to (y =O) \to 
                        (x = O).
intros 3. elim H. auto paramodulation. apply eq_gen_S_O. exact n1. auto paramodulation.
qed.

theorem le_gen_x_O: \forall x. (le x O) \to (x = O).
intros. apply le_gen_x_O_aux. exact O. auto paramodulation. auto paramodulation.
qed.

theorem le_gen_x_O_cc: \forall x. (x = O) \to (le x O).
intros. elim H. auto new.
qed.

theorem le_gen_S_x_aux: \forall m,x,y. (le y x) \to (y = S m) \to 
                        (\exists n. x = (S n) \land (le m n)).
intros 4. elim H; clear H x y.
apply eq_gen_S_O. exact m. elim H1. auto paramodulation.
clear H2. cut (n = m).
elim Hcut. apply ex_intro. exact n1. split; autobatch.
apply eq_gen_S_S. autobatch.
qed.

theorem le_gen_S_x: \forall m,x. (le (S m) x) \to 
                    (\exists n. x = (S n) \land (le m n)).
intros. apply le_gen_S_x_aux. exact (S m). auto paramodulation. auto paramodulation.
qed.

theorem le_gen_S_x_cc: \forall m,x. (\exists n. x = (S n) \land (le m n)) \to
                       (le (S m) x).
intros. elim H. elim H1. cut ((S x1) = x). elim Hcut. auto new.
elim H2. auto paramodulation.
qed.

theorem le_gen_S_S: \forall m,n. (le (S m) (S n)) \to (le m n).
intros.
lapply le_gen_S_x to H as H0. elim H0. elim H1. 
lapply eq_gen_S_S to H2 as H4. rewrite > H4. assumption.
qed.

theorem le_gen_S_S_cc: \forall m,n. (le m n) \to (le (S m) (S n)).
intros. auto new.
qed.

(*
theorem le_trans: \forall x,y. (le x y) \to \forall z. (le y z) \to (le x z).
intros 1. elim x; clear H. clear x. 
auto paramodulation.
fwd H1 [H]. decompose.
*)
