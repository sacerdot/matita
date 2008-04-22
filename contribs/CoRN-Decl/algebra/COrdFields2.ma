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

(* This file was automatically generated: do not edit *********************)

set "baseuri" "cic:/matita/CoRN-Decl/algebra/COrdFields2".

include "CoRN.ma".

include "algebra/COrdFields.ma".

(*#* printing one_div_succ %\ensuremath{\frac1{\cdot+1}}% *)

(*#* printing Half %\ensuremath{\frac12}% #&frac12;# *)

(*#**********************************)

(* UNEXPORTED
Section Properties_of_leEq
*)

(*#**********************************)

(*#*
** Properties of [[<=]]
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/COrdFields2/Properties_of_leEq/R.var".

(* UNEXPORTED
Section addition
*)

(*#*
*** Addition and subtraction%\label{section:leEq-plus-minus}%
*)

inline "cic:/CoRN/algebra/COrdFields2/plus_resp_leEq.con".

inline "cic:/CoRN/algebra/COrdFields2/plus_resp_leEq_lft.con".

inline "cic:/CoRN/algebra/COrdFields2/minus_resp_leEq.con".

inline "cic:/CoRN/algebra/COrdFields2/inv_resp_leEq.con".

(* UNEXPORTED
Transparent cg_minus.
*)

inline "cic:/CoRN/algebra/COrdFields2/minus_resp_leEq_rht.con".

inline "cic:/CoRN/algebra/COrdFields2/plus_resp_leEq_both.con".

inline "cic:/CoRN/algebra/COrdFields2/plus_resp_less_leEq.con".

inline "cic:/CoRN/algebra/COrdFields2/plus_resp_leEq_less.con".

inline "cic:/CoRN/algebra/COrdFields2/minus_resp_less_leEq.con".

inline "cic:/CoRN/algebra/COrdFields2/minus_resp_leEq_both.con".

(*#* Cancellation properties
*)

inline "cic:/CoRN/algebra/COrdFields2/plus_cancel_leEq_rht.con".

inline "cic:/CoRN/algebra/COrdFields2/inv_cancel_leEq.con".

(*#* Laws for shifting
*)

inline "cic:/CoRN/algebra/COrdFields2/shift_plus_leEq.con".

inline "cic:/CoRN/algebra/COrdFields2/shift_leEq_plus.con".

inline "cic:/CoRN/algebra/COrdFields2/shift_plus_leEq'.con".

inline "cic:/CoRN/algebra/COrdFields2/shift_leEq_plus'.con".

inline "cic:/CoRN/algebra/COrdFields2/shift_leEq_rht.con".

inline "cic:/CoRN/algebra/COrdFields2/shift_leEq_lft.con".

inline "cic:/CoRN/algebra/COrdFields2/shift_minus_leEq.con".

inline "cic:/CoRN/algebra/COrdFields2/shift_leEq_minus.con".

inline "cic:/CoRN/algebra/COrdFields2/shift_leEq_minus'.con".

inline "cic:/CoRN/algebra/COrdFields2/shift_zero_leEq_minus.con".

inline "cic:/CoRN/algebra/COrdFields2/shift_zero_leEq_minus'.con".

(* UNEXPORTED
End addition
*)

(* UNEXPORTED
Section multiplication
*)

(*#*
*** Multiplication and division

Multiplication and division respect [[<=]]
*)

inline "cic:/CoRN/algebra/COrdFields2/mult_resp_leEq_rht.con".

inline "cic:/CoRN/algebra/COrdFields2/mult_resp_leEq_lft.con".

inline "cic:/CoRN/algebra/COrdFields2/mult_resp_leEq_both.con".

inline "cic:/CoRN/algebra/COrdFields2/recip_resp_leEq.con".

inline "cic:/CoRN/algebra/COrdFields2/div_resp_leEq.con".

(* UNEXPORTED
Hint Resolve recip_resp_leEq: algebra.
*)

(*#* Cancellation properties
*)

inline "cic:/CoRN/algebra/COrdFields2/mult_cancel_leEq.con".

(*#* Laws for shifting
*)

inline "cic:/CoRN/algebra/COrdFields2/shift_mult_leEq.con".

inline "cic:/CoRN/algebra/COrdFields2/shift_mult_leEq'.con".

inline "cic:/CoRN/algebra/COrdFields2/shift_leEq_mult'.con".

inline "cic:/CoRN/algebra/COrdFields2/shift_div_leEq.con".

inline "cic:/CoRN/algebra/COrdFields2/shift_div_leEq'.con".

inline "cic:/CoRN/algebra/COrdFields2/shift_leEq_div.con".

(* UNEXPORTED
Hint Resolve shift_leEq_div: algebra.
*)

inline "cic:/CoRN/algebra/COrdFields2/eps_div_leEq_eps.con".

inline "cic:/CoRN/algebra/COrdFields2/nonneg_div_two.con".

inline "cic:/CoRN/algebra/COrdFields2/nonneg_div_two'.con".

inline "cic:/CoRN/algebra/COrdFields2/nonneg_div_three.con".

inline "cic:/CoRN/algebra/COrdFields2/nonneg_div_three'.con".

inline "cic:/CoRN/algebra/COrdFields2/nonneg_div_four.con".

inline "cic:/CoRN/algebra/COrdFields2/nonneg_div_four'.con".

(* UNEXPORTED
End multiplication
*)

(* UNEXPORTED
Section misc
*)

(*#*
*** Miscellaneous Properties
*)

inline "cic:/CoRN/algebra/COrdFields2/sqr_nonneg.con".

inline "cic:/CoRN/algebra/COrdFields2/nring_nonneg.con".

inline "cic:/CoRN/algebra/COrdFields2/suc_leEq_dub.con".

inline "cic:/CoRN/algebra/COrdFields2/leEq_nring.con".

inline "cic:/CoRN/algebra/COrdFields2/cc_abs_aid.con".

include "tactics/Transparent_algebra.ma".

inline "cic:/CoRN/algebra/COrdFields2/nexp_resp_pos.con".

include "tactics/Opaque_algebra.ma".

inline "cic:/CoRN/algebra/COrdFields2/mult_resp_nonneg.con".

include "tactics/Transparent_algebra.ma".

inline "cic:/CoRN/algebra/COrdFields2/nexp_resp_nonneg.con".

inline "cic:/CoRN/algebra/COrdFields2/power_resp_leEq.con".

inline "cic:/CoRN/algebra/COrdFields2/nexp_resp_less.con".

inline "cic:/CoRN/algebra/COrdFields2/power_cancel_leEq.con".

inline "cic:/CoRN/algebra/COrdFields2/power_cancel_less.con".

inline "cic:/CoRN/algebra/COrdFields2/nat_less_bin_nexp.con".

inline "cic:/CoRN/algebra/COrdFields2/Sum_resp_leEq.con".

inline "cic:/CoRN/algebra/COrdFields2/Sumx_resp_leEq.con".

inline "cic:/CoRN/algebra/COrdFields2/Sum2_resp_leEq.con".

inline "cic:/CoRN/algebra/COrdFields2/approach_zero.con".

inline "cic:/CoRN/algebra/COrdFields2/approach_zero_weak.con".

(* UNEXPORTED
End misc
*)

inline "cic:/CoRN/algebra/COrdFields2/equal_less_leEq.con".

(* UNEXPORTED
End Properties_of_leEq
*)

(*#**********************************)

(* UNEXPORTED
Section PosP_properties
*)

(*#**********************************)

(*#*
** Properties of positive numbers
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/COrdFields2/PosP_properties/R.var".

(* begin hide *)

(* NOTATION
Notation ZeroR := (Zero:R).
*)

(* NOTATION
Notation OneR := (One:R).
*)

(* end hide *)

inline "cic:/CoRN/algebra/COrdFields2/mult_pos_imp.con".

inline "cic:/CoRN/algebra/COrdFields2/plus_resp_pos_nonneg.con".

inline "cic:/CoRN/algebra/COrdFields2/plus_resp_nonneg_pos.con".

inline "cic:/CoRN/algebra/COrdFields2/pos_square.con".

inline "cic:/CoRN/algebra/COrdFields2/mult_cancel_pos_rht.con".

inline "cic:/CoRN/algebra/COrdFields2/mult_cancel_pos_lft.con".

inline "cic:/CoRN/algebra/COrdFields2/pos_wd.con".

inline "cic:/CoRN/algebra/COrdFields2/even_power_pos.con".

inline "cic:/CoRN/algebra/COrdFields2/odd_power_cancel_pos.con".

inline "cic:/CoRN/algebra/COrdFields2/plus_resp_pos.con".

inline "cic:/CoRN/algebra/COrdFields2/pos_nring_S.con".

inline "cic:/CoRN/algebra/COrdFields2/square_eq_pos.con".

inline "cic:/CoRN/algebra/COrdFields2/square_eq_neg.con".

(* UNEXPORTED
End PosP_properties
*)

(* UNEXPORTED
Hint Resolve mult_resp_nonneg.
*)

(*#*
** Properties of one over successor
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

inline "cic:/CoRN/algebra/COrdFields2/one_div_succ.con".

(* UNEXPORTED
Implicit Arguments one_div_succ [R].
*)

(* UNEXPORTED
Section One_div_succ_properties
*)

alias id "R" = "cic:/CoRN/algebra/COrdFields2/One_div_succ_properties/R.var".

inline "cic:/CoRN/algebra/COrdFields2/one_div_succ_resp_leEq.con".

inline "cic:/CoRN/algebra/COrdFields2/one_div_succ_pos.con".

inline "cic:/CoRN/algebra/COrdFields2/one_div_succ_resp_less.con".

(* UNEXPORTED
End One_div_succ_properties
*)

(*#*
** Properties of [Half]
*)

inline "cic:/CoRN/algebra/COrdFields2/Half.con".

(* UNEXPORTED
Implicit Arguments Half [R].
*)

(* UNEXPORTED
Section Half_properties
*)

(*#*
%\begin{convention}%
Let [R] be an ordered field.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/COrdFields2/Half_properties/R.var".

inline "cic:/CoRN/algebra/COrdFields2/half_1.con".

(* UNEXPORTED
Hint Resolve half_1: algebra.
*)

inline "cic:/CoRN/algebra/COrdFields2/pos_half.con".

inline "cic:/CoRN/algebra/COrdFields2/half_1'.con".

inline "cic:/CoRN/algebra/COrdFields2/half_2.con".

inline "cic:/CoRN/algebra/COrdFields2/half_lt1.con".

inline "cic:/CoRN/algebra/COrdFields2/half_3.con".

(* UNEXPORTED
End Half_properties
*)

(* UNEXPORTED
Hint Resolve half_1 half_1' half_2: algebra.
*)

