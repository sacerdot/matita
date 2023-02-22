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

alias symbol "plus" (instance 0) = "Coq's natural plus".
definition myplus \def \lambda x,y. x+y.

alias id "S" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/2)".
lemma lem: \forall n. S (n + n) = (S n) + n.
 intro; reflexivity.
qed.

theorem trivial: \forall n. S (myplus n n) = myplus (S n) n.
 unfold myplus in \vdash (\forall _.(? ? ? %)).
 intro.
 unfold myplus.
 rewrite > lem.
 reflexivity.
qed.

(* This test needs to parse "uno" in the context of the hypothesis H,
   not in the context of the goal. *)
alias id "O" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/1)".
theorem t: let uno \def S O in uno + uno = S uno \to uno=uno.
 intros. unfold uno in H.
 reflexivity.
qed.
