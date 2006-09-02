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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/Preamble".

(* FG: We should include legacy/coq.ma bit it is not working *)
(* include "legacy/coq.ma".                                  *)

default "equality"
 cic:/Coq/Init/Logic/eq.ind
 cic:/Coq/Init/Logic/sym_eq.con
 cic:/Coq/Init/Logic/trans_eq.con
 cic:/Coq/Init/Logic/eq_ind.con
 cic:/Coq/Init/Logic/eq_ind_r.con
 cic:/Coq/Init/Logic/f_equal.con
 cic:/Coq/Init/Logic/f_equal1.con.
       
default "true"
 cic:/Coq/Init/Logic/True.ind.

default "false"
 cic:/Coq/Init/Logic/False.ind.

default "absurd"
 cic:/Coq/Init/Logic/absurd.con.

interpretation "Coq's leibnitz's equality" 'eq x y = (cic:/Coq/Init/Logic/eq.ind#xpointer(1/1) _ x y).
interpretation "Coq's not equal to (leibnitz)" 'neq x y = (cic:/Coq/Init/Logic/not.con (cic:/Coq/Init/Logic/eq.ind#xpointer(1/1) _ x y)).
interpretation "Coq's natural plus" 'plus x y = (cic:/Coq/Init/Peano/plus.con x y).
interpretation "Coq's natural 'less or equal to'" 'leq x y = (cic:/Coq/Init/Peano/le.ind#xpointer(1/1) x y).

alias id "land" = "cic:/Coq/Init/Logic/and.ind#xpointer(1/1)".
	  
(* FG/CSC: These aliases should disappear: we would like to write something
 *         like: "disambiguate in cic:/Coq/*"
 *)
alias id "True" = "cic:/Coq/Init/Logic/True.ind#xpointer(1/1)".
alias id "or" = "cic:/Coq/Init/Logic/or.ind#xpointer(1/1)".
alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias id "eq" = "cic:/Coq/Init/Logic/eq.ind#xpointer(1/1)".
alias id "plus" = "cic:/Coq/Init/Peano/plus.con".
alias id "le_trans" = "cic:/Coq/Arith/Le/le_trans.con".
alias id "le_plus_r" = "cic:/Coq/Arith/Plus/le_plus_r.con".
alias id "le" = "cic:/Coq/Init/Peano/le.ind#xpointer(1/1)".
alias id "ex" = "cic:/Coq/Init/Logic/ex.ind#xpointer(1/1)".
alias id "ex2" = "cic:/Coq/Init/Logic/ex2.ind#xpointer(1/1)".
alias id "true" = "cic:/Coq/Init/Datatypes/bool.ind#xpointer(1/1/1)".
alias id "false" = "cic:/Coq/Init/Datatypes/bool.ind#xpointer(1/1/2)".
alias id "bool" = "cic:/Coq/Init/Datatypes/bool.ind#xpointer(1/1)".
alias id "O" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/1)".
alias id "S" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/2)".
alias id "eq_ind" = "cic:/Coq/Init/Logic/eq_ind.con".
alias id "or_introl" = "cic:/Coq/Init/Logic/or.ind#xpointer(1/1/1)".
alias id "or_intror" = "cic:/Coq/Init/Logic/or.ind#xpointer(1/1/2)".
alias id "False_ind" = "cic:/Coq/Init/Logic/False_ind.con".
alias id "False" = "cic:/Coq/Init/Logic/False.ind#xpointer(1/1)".
alias id "I" = "cic:/Coq/Init/Logic/True.ind#xpointer(1/1/1)".
alias id "minus" = "cic:/Coq/Init/Peano/minus.con".
alias id "le_n" = "cic:/Coq/Init/Peano/le.ind#xpointer(1/1/1)".
alias id "le_antisym" = "cic:/Coq/Arith/Le/le_antisym.con".
alias id "eq_ind_r" = "cic:/Coq/Init/Logic/eq_ind_r.con".

theorem f_equal: \forall A,B:Type. \forall f:A \to B.
                 \forall x,y:A. x = y \to f x = f y.
 intros. elim H. reflexivity.
qed.

theorem sym_eq: \forall A:Type. \forall x,y:A. x = y \to y = x.
 intros. rewrite > H. reflexivity.
qed.

theorem sym_not_eq: \forall A:Type. \forall x,y:A. x \neq y \to y \neq x.
 unfold not. intros. apply H. symmetry. assumption.
qed.

theorem plus_reg_l: \forall (n,m,p:nat). n + m = n + p \to m = p.
 intros. apply plus_reg_l; auto.
qed.

theorem plus_le_reg_l: \forall p,n,m. p + n <= p + m \to n <= m.
 intros. apply plus_le_reg_l; auto.
qed.

definition sym_equal \def sym_eq.
