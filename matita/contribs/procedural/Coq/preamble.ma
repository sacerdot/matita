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

default "equality"
 cic:/Coq/Init/Logic/eq.ind
 cic:/Coq/Init/Logic/sym_eq.con
 cic:/Coq/Init/Logic/trans_eq.con
 cic:/Coq/Init/Logic/eq_ind.con
 cic:/Coq/Init/Logic/eq_ind_r.con
 cic:/Coq/Init/Logic/eq_rec.con
 cic:/Coq/Init/Logic/eq_rec_r.con
 cic:/Coq/Init/Logic/eq_rect.con
 cic:/Coq/Init/Logic/eq_rect_r.con
 cic:/Coq/Init/Logic/f_equal.con
 cic:/matita/procedural/Coq/preamble/f_equal1.con.

default "true"
 cic:/Coq/Init/Logic/True.ind. 
default "false"
 cic:/Coq/Init/Logic/False.ind. 
default "absurd"
 cic:/Coq/Init/Logic/absurd.con. 

interpretation "Coq's leibnitz's equality" 'eq x y = (cic:/Coq/Init/Logic/eq.ind#xpointer(1/1) ? x y).

theorem f_equal1 : \forall A,B:Type.\forall f:A\to B.\forall x,y:A.
  x = y \to (f y) = (f x).
  intros.
  symmetry.
  apply cic:/Coq/Init/Logic/f_equal.con.
  assumption.
qed.

alias id "land" = "cic:/matita/procedural/Coq/Init/Logic/and.ind#xpointer(1/1)".
