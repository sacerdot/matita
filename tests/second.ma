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


alias id "nat" = "cic:/matita/tests/first/nat.ind#xpointer(1/1)".
alias id "O" = "cic:/matita/tests/first/nat.ind#xpointer(1/1/1)".
alias id "eq" = "cic:/matita/tests/first/eq.ind#xpointer(1/1)".
alias id "refl" = "cic:/matita/tests/first/eq.ind#xpointer(1/1/1)".

theorem ultrastupid : eq nat O O.
apply refl.
qed.

