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


include "coq.ma".

alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias num (instance 0) = "Coq natural number".
alias symbol "eq" (instance 0) = "Coq's leibnitz's equality". 
alias symbol "plus" (instance 0) = "Coq's natural plus".
alias id "plus_n_O" = "cic:/Coq/Init/Peano/plus_n_O.con".

theorem a:
  \forall a,b:nat.
  a = b \to b + a + b + a= (\lambda j.((\lambda w.((\lambda x.x + b + w + j) a)) b)) a.
intros.
rewrite < H in \vdash (? ? ? ((\lambda j.((\lambda w.%) ?)) ?)).

rewrite < H in \vdash (? ? % ?).

simplify in \vdash (? ? ? ((\lambda _.((\lambda _.%) ?)) ?)).

rewrite < H in \vdash (? ? ? (% ?)).
simplify.
reflexivity.
qed.
 
theorem t: \forall n. 0=0 \to n = n + 0.
 intros.
 apply plus_n_O.
qed.

(* In this test "rewrite < t" should open a new goal 0=0 and put it in *)
(* the goallist so that the THEN tactical closes it using reflexivity. *)
theorem foo: \forall n. n = n + 0.
 intros.
 rewrite < t; reflexivity.
qed.

theorem test_rewrite_in_hyp:
          \forall n,m. n + 0 = m \to m = n + 0 \to n=m \land m+0=n+0.
 intros.
 rewrite < plus_n_O in H.
 rewrite > plus_n_O in H1.
 split; [ exact H | exact H1].
qed.

theorem test_rewrite_in_hyp2:
          \forall n,m. n + 0 = m \to n + 0 = m \to n=m \land n+0=m.
 intros.
 rewrite < plus_n_O in H H1 \vdash (? ? %).
 split; [ exact H | exact H1].
qed.

alias id "O" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/1)".
theorem test_rewrite_under_pi: \forall x,y. x = O \to y = O \to x = x \to O = x.
intros 3.
rewrite > H in \vdash (? \to ? ? % % \to ? ? ? %).
intros. reflexivity.
qed.
