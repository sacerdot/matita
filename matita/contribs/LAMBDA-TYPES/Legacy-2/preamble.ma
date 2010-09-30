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

include "Legacy-1/theory.ma".

default "equality"
 cic:/matita/LAMBDA-TYPES/Legacy-1/coq/defs/eq.ind
 cic:/matita/LAMBDA-TYPES/Legacy-1/coq/props/sym_eq.con
 cic:/matita/LAMBDA-TYPES/Legacy-1/coq/props/trans_eq.con
 cic:/matita/LAMBDA-TYPES/Legacy-1/coq/defs/eq_ind.con
 cic:/matita/LAMBDA-TYPES/Legacy-1/coq/props/eq_ind_r.con
 cic:/matita/LAMBDA-TYPES/Legacy-1/coq/defs/eq_rec.con
 cic:/matita/LAMBDA-TYPES/Legacy-1/coq/props/eq_rec_r.con
 cic:/matita/LAMBDA-TYPES/Legacy-1/coq/defs/eq_rect.con
 cic:/matita/LAMBDA-TYPES/Legacy-1/coq/props/eq_rect_r.con
 cic:/matita/LAMBDA-TYPES/Legacy-1/coq/props/f_equal.con
 cic:/matita/LAMBDA-TYPES/Legacy-2/preamble/f_equal_sym.con.

default "true"
 cic:/matita/LAMBDA-TYPES/Legacy-1/coq/defs/True.ind. 
default "false"
 cic:/matita/LAMBDA-TYPES/Legacy-1/preamble/False.ind. 
default "absurd"
 cic:/matita/LAMBDA-TYPES/Legacy-1/coq/props/absurd.con. 

interpretation "Coq 7.3.1 natural plus" 'plus x y = (cic:/matita/LAMBDA-TYPES/Legacy-1/coq/defs/plus.con x y).
interpretation "Coq 7.3.1 natural minus" 'minus x y = (cic:/matita/LAMBDA-TYPES/Legacy-1/coq/defs/minus.con x y).
interpretation "Coq 7.3.1 logical and" 'and x y = (cic:/matita/LAMBDA-TYPES/Legacy-1/coq/defs/land.ind#xpointer(1/1) x y).
interpretation "Coq 7.3.1 logical or" 'or x y = (cic:/matita/LAMBDA-TYPES/Legacy-1/coq/defs/or.ind#xpointer(1/1) x y).
interpretation "Coq 7.3.1 logical not" 'not x = (cic:/matita/LAMBDA-TYPES/Legacy-1/coq/defs/not.con x).
interpretation "Coq 7.3.1 exists" 'exists \eta.x = (cic:/matita/LAMBDA-TYPES/Legacy-1/coq/defs/ex.ind#xpointer(1/1) ? x).
interpretation "Coq 7.3.1 natural 'less or equal to'" 'leq x y = (cic:/matita/LAMBDA-TYPES/Legacy-1/coq/defs/le.ind#xpointer(1/1) x y).
interpretation "Coq 7.3.1 natural 'less than'" 'lt x y = (cic:/matita/LAMBDA-TYPES/Legacy-1/coq/defs/lt.con x y).
interpretation "Coq 7.3.1 leibnitz's equality" 'eq t x y = (cic:/matita/LAMBDA-TYPES/Legacy-1/coq/defs/eq.ind#xpointer(1/1) t x y).

alias symbol "plus" = "Coq 7.3.1 natural plus".
alias symbol "minus" = "Coq 7.3.1 natural minus".
alias symbol "and" = "Coq 7.3.1 logical and".
alias symbol "or" = "Coq 7.3.1 logical or".
alias symbol "not" = "Coq 7.3.1 logical not".
alias symbol "exists" = "Coq 7.3.1 exists".
alias symbol "leq" = "Coq 7.3.1 natural 'less or equal to'".
alias symbol "lt" = "Coq 7.3.1 natural 'less than'".
alias symbol "eq" = "Coq 7.3.1 leibnitz's equality".

theorem f_equal_sym: \forall A,B:Set.\forall f:A\to B.\forall x,y.
                     x = y \to (f y) = (f x).
  intros; symmetry.
  apply cic:/matita/LAMBDA-TYPES/Legacy-1/coq/props/f_equal.con.
  assumption.
qed.
