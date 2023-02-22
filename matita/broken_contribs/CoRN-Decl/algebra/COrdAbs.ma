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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/COrdAbs".

include "CoRN.ma".

include "algebra/COrdFields2.ma".

(*#*
** Properties of [AbsSmall]
*)

(* Begin_SpecReals *)

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall.con".

(* UNEXPORTED
Implicit Arguments AbsSmall [R].
*)

(* End_SpecReals *)

(* UNEXPORTED
Section AbsSmall_properties
*)

(*#*
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/COrdAbs/AbsSmall_properties/R.var".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_wdr.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_wdr_unfolded.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_wdl.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_wdl_unfolded.con".

(* UNEXPORTED
Declare Left Step AbsSmall_wdl_unfolded.
*)

(* UNEXPORTED
Declare Right Step AbsSmall_wdr_unfolded.
*)

(* begin hide *)

(* NOTATION
Notation ZeroR := (Zero:R).
*)

(* end hide *)

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_leEq_trans.con".

inline "cic:/CoRN/algebra/COrdAbs/zero_AbsSmall.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_trans.con".

inline "cic:/CoRN/algebra/COrdAbs/leEq_imp_AbsSmall.con".

inline "cic:/CoRN/algebra/COrdAbs/inv_resp_AbsSmall.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_minus.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_plus.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_eps_div_two.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_x_plus_delta.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_x_minus_delta.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_x_plus_eps_div2.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_x_minus_eps_div2.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_intermediate.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_eps_div2.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_nonneg.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_mult.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_cancel_mult.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsSmall_approach_zero.con".

(* UNEXPORTED
End AbsSmall_properties
*)

(* UNEXPORTED
Declare Left Step AbsSmall_wdl_unfolded.
*)

(* UNEXPORTED
Declare Right Step AbsSmall_wdr_unfolded.
*)

(*#* ** Properties of [AbsBig] *)

inline "cic:/CoRN/algebra/COrdAbs/absBig.con".

(* NOTATION
Notation AbsBig := (absBig _).
*)

inline "cic:/CoRN/algebra/COrdAbs/AbsBigSmall_minus.con".

(* UNEXPORTED
Section absBig_wd_properties
*)

(*#*
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/COrdAbs/absBig_wd_properties/R.var".

inline "cic:/CoRN/algebra/COrdAbs/AbsBig_wdr.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsBig_wdl.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsBig_wdr_unfolded.con".

inline "cic:/CoRN/algebra/COrdAbs/AbsBig_wdl_unfolded.con".

(* UNEXPORTED
End absBig_wd_properties
*)

(* UNEXPORTED
Declare Left Step AbsBig_wdl_unfolded.
*)

(* UNEXPORTED
Declare Right Step AbsBig_wdr_unfolded.
*)

