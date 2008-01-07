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
alias id "eq" = "cic:/Coq/Init/Logic/eq.ind#xpointer(1/1)".
alias id "eq_ind" = "cic:/Coq/Init/Logic/eq_ind.con".
alias id "eq_ind_r" = "cic:/Coq/Init/Logic/eq_ind_r.con".
alias id "sym_eq" = "cic:/Coq/Init/Logic/sym_eq.con".


theorem self:
  \forall A:Set.
  \forall f,g:A \to A.
  \forall H:(\forall x,y:A. x = y).
  \forall H:(\forall x,y,z:A. f x = y).
  \forall x,y:A. x=y.
intros.autobatch paramodulation.
qed.

theorem GRP049_simple:
  \forall A:Set.
  \forall inv: A \to A.
  \forall mult: A \to A \to A.
  \forall H: (\forall x,y,z:A.mult z (inv (mult (inv (mult (inv (mult z y)) x)) (inv (mult y (mult (inv y) y))))) = x).
  \forall a,b:A. mult (inv a) a = mult (inv b) b.
intros.autobatch paramodulation; exact a.
qed.

theorem GRP049 :
  \forall A:Set.
  \forall inv: A \to A.
  \forall mult: A \to A \to A.
  \forall H: (\forall x,y,z:A.mult z (inv (mult (inv (mult (inv (mult z y)) x)) (inv (mult y (mult (inv y) y))))) = x).
  \forall a,b:A. mult a (inv a)= mult b (inv b).
intros.autobatch paramodulation timeout = 600;exact a.
qed.
