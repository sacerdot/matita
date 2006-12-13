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

set "baseuri" "cic:/matita/CoRN-Decl/reals/Cauchy_CReals".

include "CoRN.ma".

(* $Id: Cauchy_CReals.v,v 1.5 2004/04/23 10:01:04 lcf Exp $ *)

include "algebra/Cauchy_COF.ma".

include "reals/CReals.ma".

(* UNEXPORTED
Section R_CReals
*)

(*#* * The Real Number Structure

We will now apply our Cauchy sequence construction to an archimedean ordered field in order to obtain a model of the real numbers.

** Injection of [Q]

We start by showing how to inject the rational numbers in the field of Cauchy sequences; this embedding preserves the algebraic operations.

%\begin{convention}% Let [F] be an ordered field.
%\end{convention}%
*)

alias id "F" = "cic:/CoRN/reals/Cauchy_CReals/R_CReals/F.var".

(* NOTATION
Notation "'R_COrdField''" := (R_COrdField F).
*)

inline "cic:/CoRN/reals/Cauchy_CReals/inject_Q.con".

inline "cic:/CoRN/reals/Cauchy_CReals/ing_eq.con".

inline "cic:/CoRN/reals/Cauchy_CReals/ing_plus.con".

inline "cic:/CoRN/reals/Cauchy_CReals/ing_min.con".

inline "cic:/CoRN/reals/Cauchy_CReals/ing_lt.con".

inline "cic:/CoRN/reals/Cauchy_CReals/ing_ap.con".

inline "cic:/CoRN/reals/Cauchy_CReals/ing_cancel_eq.con".

inline "cic:/CoRN/reals/Cauchy_CReals/ing_cancel_less.con".

inline "cic:/CoRN/reals/Cauchy_CReals/ing_le.con".

inline "cic:/CoRN/reals/Cauchy_CReals/ing_cancel_leEq.con".

inline "cic:/CoRN/reals/Cauchy_CReals/ing_cancel_AbsSmall.con".

inline "cic:/CoRN/reals/Cauchy_CReals/ing_One.con".

inline "cic:/CoRN/reals/Cauchy_CReals/ing_nring'.con".

inline "cic:/CoRN/reals/Cauchy_CReals/ing_nring.con".

inline "cic:/CoRN/reals/Cauchy_CReals/ing_mult.con".

(* UNEXPORTED
Opaque R_COrdField.
*)

inline "cic:/CoRN/reals/Cauchy_CReals/ing_div_three.con".

(* UNEXPORTED
Transparent R_COrdField.
*)

inline "cic:/CoRN/reals/Cauchy_CReals/ing_n.con".

inline "cic:/CoRN/reals/Cauchy_CReals/expand_Q_R.con".

inline "cic:/CoRN/reals/Cauchy_CReals/conv_modulus.con".

inline "cic:/CoRN/reals/Cauchy_CReals/R_CReals/T.con" "R_CReals__".

(*#* We now assume our original field is archimedean and prove that the
resulting one is, too.
*)

alias id "F_is_archemaedian" = "cic:/CoRN/reals/Cauchy_CReals/R_CReals/F_is_archemaedian.var".

inline "cic:/CoRN/reals/Cauchy_CReals/R_is_archemaedian.con".

(* begin hide *)

inline "cic:/CoRN/reals/Cauchy_CReals/R_CReals/PT.con" "R_CReals__".

(* end hide *)

inline "cic:/CoRN/reals/Cauchy_CReals/modulus_property.con".

inline "cic:/CoRN/reals/Cauchy_CReals/modulus_property_2.con".

inline "cic:/CoRN/reals/Cauchy_CReals/expand_Q_R_2.con".

inline "cic:/CoRN/reals/Cauchy_CReals/CS_seq_diagonal.con".

(*#* ** Cauchy Completeness
We can also define a limit operator.
*)

inline "cic:/CoRN/reals/Cauchy_CReals/Q_dense_in_R.con".

inline "cic:/CoRN/reals/Cauchy_CReals/LimR_CauchySeq.con".

inline "cic:/CoRN/reals/Cauchy_CReals/R_is_complete.con".

inline "cic:/CoRN/reals/Cauchy_CReals/R_is_CReals.con".

inline "cic:/CoRN/reals/Cauchy_CReals/R_as_CReals.con".

(* UNEXPORTED
End R_CReals
*)

