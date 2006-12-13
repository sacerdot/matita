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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/Expon".

include "CoRN.ma".

(* $Id: Expon.v,v 1.5 2004/04/23 10:00:54 lcf Exp $ *)

(*#* printing [^^] %\ensuremath{\hat{\ }}% #^# *)

include "algebra/COrdCauchy.ma".

include "tactics/Transparent_algebra.ma".

(*#* *Exponentiation
**More properties about [nexp]
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

(* UNEXPORTED
Section More_Nexp
*)

alias id "R" = "cic:/CoRN/algebra/Expon/More_Nexp/R.var".

inline "cic:/CoRN/algebra/Expon/nexp_resp_ap_zero.con".

(* UNEXPORTED
Hint Resolve nexp_resp_ap_zero: algebra.
*)

inline "cic:/CoRN/algebra/Expon/nexp_distr_div.con".

inline "cic:/CoRN/algebra/Expon/nexp_distr_div'.con".

inline "cic:/CoRN/algebra/Expon/small_nexp_resp_lt.con".

inline "cic:/CoRN/algebra/Expon/great_nexp_resp_lt.con".

inline "cic:/CoRN/algebra/Expon/small_nexp_resp_le.con".

inline "cic:/CoRN/algebra/Expon/great_nexp_resp_le.con".

inline "cic:/CoRN/algebra/Expon/nexp_resp_leEq.con".

inline "cic:/CoRN/algebra/Expon/nexp_resp_leEq_one.con".

inline "cic:/CoRN/algebra/Expon/nexp_resp_leEq_neg_even.con".

inline "cic:/CoRN/algebra/Expon/nexp_resp_leEq_neg_odd.con".

inline "cic:/CoRN/algebra/Expon/nexp_distr_recip.con".

(* UNEXPORTED
Hint Resolve nexp_distr_recip: algebra.
*)

inline "cic:/CoRN/algebra/Expon/nexp_even_nonneg.con".

inline "cic:/CoRN/algebra/Expon/nexp_resp_le'.con".

inline "cic:/CoRN/algebra/Expon/nexp_resp_le.con".

inline "cic:/CoRN/algebra/Expon/bin_less_un.con".

(* UNEXPORTED
End More_Nexp
*)

(* UNEXPORTED
Hint Resolve nexp_distr_div nexp_distr_recip: algebra.
*)

(* UNEXPORTED
Implicit Arguments nexp_resp_ap_zero [R x].
*)

(*#* **Definition of [zexp]: integer exponentiation
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

(* UNEXPORTED
Section Zexp_def
*)

alias id "R" = "cic:/CoRN/algebra/Expon/Zexp_def/R.var".

(*#*
It would be nicer to define [zexp] using [caseZdiff], but we already
have most properties now.
*)

inline "cic:/CoRN/algebra/Expon/zexp.con".

(* UNEXPORTED
End Zexp_def
*)

(* UNEXPORTED
Implicit Arguments zexp [R].
*)

(* NOTATION
Notation "( x [//] Hx ) [^^] n" := (zexp x Hx n) (at level 0).
*)

(*#* **Properties of [zexp]
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

(* UNEXPORTED
Section Zexp_properties
*)

alias id "R" = "cic:/CoRN/algebra/Expon/Zexp_properties/R.var".

inline "cic:/CoRN/algebra/Expon/zexp_zero.con".

(* UNEXPORTED
Hint Resolve zexp_zero: algebra.
*)

inline "cic:/CoRN/algebra/Expon/zexp_nexp.con".

(* UNEXPORTED
Hint Resolve zexp_nexp: algebra.
*)

inline "cic:/CoRN/algebra/Expon/zexp_inv_nexp.con".

(* UNEXPORTED
Hint Resolve zexp_inv_nexp: algebra.
*)

inline "cic:/CoRN/algebra/Expon/zexp_inv_nexp'.con".

(* UNEXPORTED
Hint Resolve zexp_inv_nexp': algebra.
*)

inline "cic:/CoRN/algebra/Expon/zexp_strext.con".

inline "cic:/CoRN/algebra/Expon/zexp_wd.con".

(* UNEXPORTED
Hint Resolve zexp_wd: algebra_c.
*)

inline "cic:/CoRN/algebra/Expon/zexp_plus1.con".

(* UNEXPORTED
Hint Resolve zexp_plus1: algebra.
*)

inline "cic:/CoRN/algebra/Expon/zexp_resp_ap_zero.con".

(* UNEXPORTED
Hint Resolve zexp_resp_ap_zero: algebra.
*)

inline "cic:/CoRN/algebra/Expon/zexp_inv.con".

(* UNEXPORTED
Hint Resolve zexp_inv: algebra.
*)

inline "cic:/CoRN/algebra/Expon/zexp_inv1.con".

(* UNEXPORTED
Hint Resolve zexp_inv1: algebra.
*)

inline "cic:/CoRN/algebra/Expon/zexp_plus.con".

(* UNEXPORTED
Hint Resolve zexp_plus: algebra.
*)

inline "cic:/CoRN/algebra/Expon/zexp_minus.con".

(* UNEXPORTED
Hint Resolve zexp_minus: algebra.
*)

inline "cic:/CoRN/algebra/Expon/one_zexp.con".

(* UNEXPORTED
Hint Resolve one_zexp: algebra.
*)

inline "cic:/CoRN/algebra/Expon/mult_zexp.con".

(* UNEXPORTED
Hint Resolve mult_zexp: algebra.
*)

inline "cic:/CoRN/algebra/Expon/zexp_mult.con".

(* UNEXPORTED
Hint Resolve zexp_mult: algebra.
*)

inline "cic:/CoRN/algebra/Expon/zexp_two.con".

(* UNEXPORTED
Hint Resolve zexp_two: algebra.
*)

inline "cic:/CoRN/algebra/Expon/inv_zexp_even.con".

(* UNEXPORTED
Hint Resolve inv_zexp_even: algebra.
*)

inline "cic:/CoRN/algebra/Expon/inv_zexp_two.con".

(* UNEXPORTED
Hint Resolve inv_zexp_two: algebra.
*)

inline "cic:/CoRN/algebra/Expon/inv_zexp_odd.con".

inline "cic:/CoRN/algebra/Expon/zexp_one.con".

(* UNEXPORTED
Hint Resolve zexp_one: algebra.
*)

inline "cic:/CoRN/algebra/Expon/zexp_funny.con".

(* UNEXPORTED
Hint Resolve zexp_funny: algebra.
*)

inline "cic:/CoRN/algebra/Expon/zexp_funny'.con".

(* UNEXPORTED
Hint Resolve zexp_funny': algebra.
*)

inline "cic:/CoRN/algebra/Expon/zexp_pos.con".

(* UNEXPORTED
End Zexp_properties
*)

(* UNEXPORTED
Hint Resolve nexp_resp_ap_zero zexp_zero zexp_nexp zexp_inv_nexp
  zexp_inv_nexp' zexp_plus1 zexp_resp_ap_zero zexp_inv zexp_inv1 zexp_plus
  zexp_minus one_zexp mult_zexp zexp_mult zexp_two inv_zexp_even inv_zexp_two
  zexp_one zexp_funny zexp_funny': algebra.
*)

(* UNEXPORTED
Hint Resolve zexp_wd: algebra_c.
*)

(* UNEXPORTED
Section Root_Unique
*)

alias id "R" = "cic:/CoRN/algebra/Expon/Root_Unique/R.var".

inline "cic:/CoRN/algebra/Expon/root_unique.con".

inline "cic:/CoRN/algebra/Expon/root_one.con".

(* UNEXPORTED
End Root_Unique
*)

