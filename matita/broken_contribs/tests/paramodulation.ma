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
alias symbol "eq" (instance 0) = "Coq's leibnitz's equality".
alias symbol "plus" (instance 0) = "Coq's natural plus".
alias num (instance 0) = "Coq natural number".
alias symbol "times" (instance 0) = "Coq's natural times".

theorem para1:
  \forall n,m,n1,m1:nat.
    n=m \to n1 = m1 \to (n + n1) = (m + m1).
intros. autobatch paramodulation.
qed.

theorem para2:
  \forall n:nat. n + n = 2 * n.
intros. autobatch paramodulation library.
qed.
