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

set "baseuri" "cic:/matita/LAMBDA-TYPES/Level-1/Base/ext/preamble".

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
alias id "bool" = "cic:/Coq/Init/Datatypes/bool.ind#xpointer(1/1)".
alias id "conj" = "cic:/Coq/Init/Logic/and.ind#xpointer(1/1/1)".
alias id "eq_add_S" = "cic:/Coq/Init/Peano/eq_add_S.con".
alias id "eq" = "cic:/Coq/Init/Logic/eq.ind#xpointer(1/1)".
alias id "eq_ind" = "cic:/Coq/Init/Logic/eq_ind.con".
alias id "eq_ind_r" = "cic:/Coq/Init/Logic/eq_ind_r.con".
alias id "ex2" = "cic:/Coq/Init/Logic/ex2.ind#xpointer(1/1)".
alias id "ex2_ind" = "cic:/Coq/Init/Logic/ex2_ind.con".
alias id "ex" = "cic:/Coq/Init/Logic/ex.ind#xpointer(1/1)".
alias id "ex_intro2" = "cic:/Coq/Init/Logic/ex2.ind#xpointer(1/1/1)".
alias id "false" = "cic:/Coq/Init/Datatypes/bool.ind#xpointer(1/1/2)".
alias id "False" = "cic:/Coq/Init/Logic/False.ind#xpointer(1/1)".
alias id "False_ind" = "cic:/Coq/Init/Logic/False_ind.con".
alias id "I" = "cic:/Coq/Init/Logic/True.ind#xpointer(1/1/1)".
alias id "le_antisym" = "cic:/Coq/Arith/Le/le_antisym.con".
alias id "le" = "cic:/Coq/Init/Peano/le.ind#xpointer(1/1)".
alias id "le_lt_n_Sm" = "cic:/Coq/Arith/Lt/le_lt_n_Sm.con".
alias id "le_lt_or_eq" = "cic:/Coq/Arith/Lt/le_lt_or_eq.con".
alias id "le_n" = "cic:/Coq/Init/Peano/le.ind#xpointer(1/1/1)".
alias id "le_n_O_eq" = "cic:/Coq/Arith/Le/le_n_O_eq.con".
alias id "le_not_lt" = "cic:/Coq/Arith/Lt/le_not_lt.con".
alias id "le_n_S" = "cic:/Coq/Arith/Le/le_n_S.con".
alias id "le_O_n" = "cic:/Coq/Arith/Le/le_O_n.con".
alias id "le_or_lt" = "cic:/Coq/Arith/Lt/le_or_lt.con".
alias id "le_plus_l" = "cic:/Coq/Arith/Plus/le_plus_l.con".
alias id "le_plus_minus" = "cic:/Coq/Arith/Minus/le_plus_minus.con".
alias id "le_plus_minus_r" = "cic:/Coq/Arith/Minus/le_plus_minus_r.con".
alias id "le_plus_r" = "cic:/Coq/Arith/Plus/le_plus_r.con".
alias id "le_S" = "cic:/Coq/Init/Peano/le.ind#xpointer(1/1/2)".
alias id "le_S_n" = "cic:/Coq/Arith/Le/le_S_n.con".
alias id "le_Sn_n" = "cic:/Coq/Arith/Le/le_Sn_n.con".
alias id "le_trans" = "cic:/Coq/Arith/Le/le_trans.con".
alias id "lt" = "cic:/Coq/Init/Peano/lt.con".
alias id "lt_irrefl" = "cic:/Coq/Arith/Lt/lt_irrefl.con".
alias id "lt_le_S" = "cic:/Coq/Arith/Lt/lt_le_S.con".
alias id "lt_n_S" = "cic:/Coq/Arith/Lt/lt_n_S.con".
alias id "minus" = "cic:/Coq/Init/Peano/minus.con".
alias id "minus_n_O" = "cic:/Coq/Arith/Minus/minus_n_O.con".
alias id "minus_plus" = "cic:/Coq/Arith/Minus/minus_plus.con".
alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias id "nat_ind" = "cic:/Coq/Init/Datatypes/nat_ind.con".
alias id "not" = "cic:/Coq/Init/Logic/not.con".
alias id "not_eq_S" = "cic:/Coq/Init/Peano/not_eq_S.con".
alias id "O" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/1)".
alias id "or" = "cic:/Coq/Init/Logic/or.ind#xpointer(1/1)".
alias id "or_ind" = "cic:/Coq/Init/Logic/or_ind.con".
alias id "or_introl" = "cic:/Coq/Init/Logic/or.ind#xpointer(1/1/1)".
alias id "or_intror" = "cic:/Coq/Init/Logic/or.ind#xpointer(1/1/2)".
alias id "O_S" = "cic:/Coq/Init/Peano/O_S.con".
alias id "plus_assoc" = "cic:/Coq/Arith/Plus/plus_assoc.con".
alias id "plus_assoc_reverse" = "cic:/Coq/Arith/Plus/plus_assoc_reverse.con".
alias id "plus" = "cic:/Coq/Init/Peano/plus.con".
alias id "plus_comm" = "cic:/Coq/Arith/Plus/plus_comm.con".
alias id "plus_le_compat" = "cic:/Coq/Arith/Plus/plus_le_compat.con".
alias id "plus_le_reg_l" = "cic:/Coq/Arith/Plus/plus_le_reg_l.con".
alias id "plus_lt_reg_l" = "cic:/Coq/Arith/Plus/plus_lt_reg_l.con".
alias id "plus_n_Sm" = "cic:/Coq/Init/Peano/plus_n_Sm.con".
alias id "plus_reg_l" = "cic:/Coq/Arith/Plus/plus_reg_l.con".
alias id "pred" = "cic:/Coq/Init/Peano/pred.con".
alias id "refl_equal" = "cic:/Coq/Init/Logic/eq.ind#xpointer(1/1/1)".
alias id "S" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1/2)".
alias id "true" = "cic:/Coq/Init/Datatypes/bool.ind#xpointer(1/1/1)".
alias id "True" = "cic:/Coq/Init/Logic/True.ind#xpointer(1/1)".
alias id "plus_lt_compat_r" = "cic:/Coq/Arith/Plus/plus_lt_compat_r.con".
alias id "plus_n_O" = "cic:/Coq/Init/Peano/plus_n_O.con".
alias id "plus_le_lt_compat" = "cic:/Coq/Arith/Plus/plus_le_lt_compat.con".
alias id "lt_wf_ind" = "cic:/Coq/Arith/Wf_nat/lt_wf_ind.con".
alias id "minus_Sn_m" = "cic:/Coq/Arith/Minus/minus_Sn_m.con".
alias id "and_ind" = "cic:/Coq/Init/Logic/and_ind.con".
alias id "le_lt_trans" = "cic:/Coq/Arith/Lt/le_lt_trans.con".
alias id "lt_le_trans" = "cic:/Coq/Arith/Lt/lt_le_trans.con".
alias id "le_lt_trans" = "cic:/Coq/Arith/Lt/le_lt_trans.con".
alias id "plus_n_O" = "cic:/Coq/Init/Peano/plus_n_O.con".
alias id "f_equal3" = "cic:/Coq/Init/Logic/f_equal3.con".
alias id "S_pred" = "cic:/Coq/Arith/Lt/S_pred.con".
alias id "lt_le_trans" = "cic:/Coq/Arith/Lt/lt_le_trans.con".
alias id "plus_lt_compat_r" = "cic:/Coq/Arith/Plus/plus_lt_compat_r.con".
alias id "le_plus_trans" = "cic:/Coq/Arith/Plus/le_plus_trans.con".
alias id "f_equal2" = "cic:/Coq/Init/Logic/f_equal2.con".
alias id "le_plus_trans" = "cic:/Coq/Arith/Plus/le_plus_trans.con".
alias id "f_equal2" = "cic:/Coq/Init/Logic/f_equal2.con".
alias id "plus_n_O" = "cic:/Coq/Init/Peano/plus_n_O.con".
alias id "plus_n_O" = "cic:/Coq/Init/Peano/plus_n_O.con".
alias id "lt_trans" = "cic:/Coq/Arith/Lt/lt_trans.con".
alias id "minus_Sn_m" = "cic:/Coq/Arith/Minus/minus_Sn_m.con".
alias id "ex_intro" = "cic:/Coq/Init/Logic/ex.ind#xpointer(1/1/1)".
alias id "lt_trans" = "cic:/Coq/Arith/Lt/lt_trans.con".
alias id "lt_n_Sn" = "cic:/Coq/Arith/Lt/lt_n_Sn.con".
alias id "lt_le_trans" = "cic:/Coq/Arith/Lt/lt_le_trans.con".
alias id "lt_wf_ind" = "cic:/Coq/Arith/Wf_nat/lt_wf_ind.con".

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
