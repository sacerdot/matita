(**************************************************************************)
(*       ___	                                                          *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
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
 cic:/matita/legacy/coq/f_equal1.con.

default "true"
 cic:/Coq/Init/Logic/True.ind. 
default "false"
 cic:/Coq/Init/Logic/False.ind. 
default "absurd"
 cic:/Coq/Init/Logic/absurd.con. 

(* aritmetic operators *)

interpretation "Coq's natural plus" 'plus x y = (cic:/Coq/Init/Peano/plus.con x y).
interpretation "Coq's real plus" 'plus x y = (cic:/Coq/Reals/Rdefinitions/Rplus.con x y).
interpretation "Coq's binary integer plus" 'plus x y = (cic:/Coq/ZArith/BinInt/Zplus.con x y).
interpretation "Coq's binary positive plus" 'plus x y = (cic:/Coq/NArith/BinPos/Pplus.con x y).
interpretation "Coq's natural minus" 'minus x y = (cic:/Coq/Init/Peano/minus.con x y).
interpretation "Coq's real minus" 'minus x y = (cic:/Coq/Reals/Rdefinitions/Rminus.con x y).
interpretation "Coq's binary integer minus" 'minus x y = (cic:/Coq/ZArith/BinInt/Zminus.con x y).
interpretation "Coq's binary positive minus" 'minus x y = (cic:/Coq/NArith/BinPos/Pminus.con x y).
interpretation "Coq's natural times" 'times x y = (cic:/Coq/Init/Peano/mult.con x y).
interpretation "Coq's real times" 'times x y = (cic:/Coq/Reals/Rdefinitions/Rmult.con x y).
interpretation "Coq's binary positive times" 'times x y = (cic:/Coq/NArith/BinPos/Pmult.con x y).
interpretation "Coq's binary integer times" 'times x y = (cic:/Coq/ZArith/BinInt/Zmult.con x y).
interpretation "Coq's real power" 'power x y = (cic:/Coq/Reals/Rfunctions/pow.con x y).
interpretation "Coq's integer power" 'power x y = (cic:/Coq/ZArith/Zpower/Zpower.con x y).
interpretation "Coq's real divide" 'divide x y = (cic:/Coq/Reals/Rdefinitions/Rdiv.con x y).
interpretation "Coq's real unary minus" 'uminus x = (cic:/Coq/Reals/Rdefinitions/Ropp.con x).
interpretation "Coq's binary integer negative sign" 'uminus x = (cic:/Coq/ZArith/BinInt/Z.ind#xpointer(1/1/3) x).
interpretation "Coq's binary integer unary minus" 'uminus x = (cic:/Coq/ZArith/BinInt/Zopp.con x).

(* logical operators *)

interpretation "Coq's logical and" 'and x y = (cic:/Coq/Init/Logic/and.ind#xpointer(1/1) x y).
interpretation "Coq's logical or" 'or x y = (cic:/Coq/Init/Logic/or.ind#xpointer(1/1) x y).
interpretation "Coq's logical not" 'not x = (cic:/Coq/Init/Logic/not.con x).
interpretation "Coq's exists" 'exists \eta.x = (cic:/Coq/Init/Logic/ex.ind#xpointer(1/1) _ x).

(* relational operators *)

interpretation "Coq's natural 'less or equal to'" 'leq x y = (cic:/Coq/Init/Peano/le.ind#xpointer(1/1) x y).
interpretation "Coq's real 'less or equal to'" 'leq x y = (cic:/Coq/Reals/Rdefinitions/Rle.con x y).
interpretation "Coq's natural 'greater or equal to'" 'geq x y = (cic:/Coq/Init/Peano/ge.con x y).
interpretation "Coq's real 'greater or equal to'" 'geq x y = (cic:/Coq/Reals/Rdefinitions/Rge.con x y).
interpretation "Coq's natural 'less than'" 'lt x y = (cic:/Coq/Init/Peano/lt.con x y).
interpretation "Coq's real 'less than'" 'lt x y = (cic:/Coq/Reals/Rdefinitions/Rlt.con x y).
interpretation "Coq's natural 'greater than'" 'gt x y = (cic:/Coq/Init/Peano/gt.con x y).
interpretation "Coq's real 'greater than'" 'gt x y = (cic:/Coq/Reals/Rdefinitions/Rgt.con x y).

interpretation "Coq's leibnitz's equality" 'eq x y = (cic:/Coq/Init/Logic/eq.ind#xpointer(1/1) _ x y).
interpretation "Coq's not equal to (leibnitz)" 'neq x y = (cic:/Coq/Init/Logic/not.con (cic:/Coq/Init/Logic/eq.ind#xpointer(1/1) _ x y)).

interpretation "Coq's natural 'not less or equal than'"
 'nleq x y = (cic:/Coq/Init/Logic/not.con 
               (cic:/Coq/Init/Peano/le.ind#xpointer(1/1) x y)).
               
theorem f_equal1 : \forall A,B:Type.\forall f:A\to B.\forall x,y:A.
  x = y \to (f y) = (f x).
  intros.
  symmetry.
  apply cic:/Coq/Init/Logic/f_equal.con.
  assumption.
qed.
(* aliases *)

(* FG: This is because "and" is a reserved keyword of the parser *)
alias id "land" = "cic:/Coq/Init/Logic/and.ind#xpointer(1/1)".

