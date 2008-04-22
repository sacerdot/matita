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
alias symbol "times" (instance 0) = "Coq's natural times".
alias id "mult_n_O" = "cic:/Coq/Init/Peano/mult_n_O.con".
alias id "plus_n_O" = "cic:/Coq/Init/Peano/plus_n_O.con".

theorem t: \forall x:nat. x * (x + 0) = (0 + x) * (x + x * 0).
 intro.
 replace in \vdash (? ? (? ? %) (? % %)) with x.
 reflexivity.
 rewrite < (mult_n_O x).
 rewrite < (plus_n_O x).
 reflexivity.
 reflexivity.
 autobatch library.
qed.

(* This test tests "replace in match t" where t contains some metavariables *)
theorem t2: 2 + (3 * 4) = (5 + 5) + 2 * 2.
 replace in match (5+?) with (6 + 4); [reflexivity | reflexivity].
qed.
