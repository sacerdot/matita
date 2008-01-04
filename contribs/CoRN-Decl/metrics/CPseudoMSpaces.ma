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

set "baseuri" "cic:/matita/CoRN-Decl/metrics/CPseudoMSpaces".

include "CoRN.ma".

(* $Id: CPseudoMSpaces.v,v 1.3 2004/04/23 10:01:02 lcf Exp $ *)

include "reals/Intervals.ma".

(*#* *Metric Spaces
*)

(* UNEXPORTED
Section Relations
*)

(*#* **Relations necessary for Pseudo Metric Spaces and Metric Spaces
%\begin{convention}%
Let [A : CSetoid], [d : (CSetoid_bin_fun A A IR)].
%\end{convention}%
*)

alias id "A" = "cic:/CoRN/metrics/CPseudoMSpaces/Relations/A.var".

alias id "d" = "cic:/CoRN/metrics/CPseudoMSpaces/Relations/d.var".

(* UNEXPORTED
Set Implicit Arguments.
*)

(* UNEXPORTED
Unset Strict Implicit.
*)

inline "cic:/CoRN/metrics/CPseudoMSpaces/com.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/nneg.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/pos_imp_ap.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/tri_ineq.con".

(* UNEXPORTED
Set Strict Implicit.
*)

(* UNEXPORTED
Unset Implicit Arguments.
*)

inline "cic:/CoRN/metrics/CPseudoMSpaces/diag_zero.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/apdiag_imp_grzero.con".

(* UNEXPORTED
End Relations
*)

(* UNEXPORTED
Section Definition_PsMS0
*)

(*#* **Definition of Pseudo Metric Space
*)

(*#*
A pseudo metric space consists of a setoid and a %''pseudo metric''% #"pseudo metric"#, also called
%''distance''% #"distance"#, a binairy function that fulfils certain properties.
*)

inline "cic:/CoRN/metrics/CPseudoMSpaces/is_CPsMetricSpace.ind".

inline "cic:/CoRN/metrics/CPseudoMSpaces/CPsMetricSpace.ind".

coercion cic:/matita/CoRN-Decl/metrics/CPseudoMSpaces/cms_crr.con 0 (* compounds *).

(* UNEXPORTED
End Definition_PsMS0
*)

(* UNEXPORTED
Implicit Arguments cms_d [c].
*)

(* NOTATION
Infix "[-d]" := cms_d (at level 68, left associativity).
*)

(* UNEXPORTED
Section PsMS_axioms
*)

(*#* **Pseudo Metric Space axioms
%\begin{convention}%
Let [A] be a pseudo metric space.
%\end{convention}%
*)

alias id "A" = "cic:/CoRN/metrics/CPseudoMSpaces/PsMS_axioms/A.var".

inline "cic:/CoRN/metrics/CPseudoMSpaces/CPsMetricSpace_is_CPsMetricSpace.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/d_com.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/d_nneg.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/d_pos_imp_ap.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/d_tri_ineq.con".

(* UNEXPORTED
End PsMS_axioms
*)

(* UNEXPORTED
Section PsMS_basics
*)

(*#* **Pseudo Metric Space basics
%\begin{convention}%
Let [Y] be a pseudo metric space.
%\end{convention}%
*)

alias id "Y" = "cic:/CoRN/metrics/CPseudoMSpaces/PsMS_basics/Y.var".

inline "cic:/CoRN/metrics/CPseudoMSpaces/rev_tri_ineq.con".

(*#*
Instead of taking [pos_imp_ap] as axiom, 
we could as well have taken [diag_zero]. 
*)

inline "cic:/CoRN/metrics/CPseudoMSpaces/diag_zero_imp_pos_imp_ap.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/pos_imp_ap_imp_diag_zero.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/is_CPsMetricSpace_diag_zero.con".

(* UNEXPORTED
End PsMS_basics
*)

(* UNEXPORTED
Section Zerof
*)

(*#* **Zero function
*)

(*#*
Every setoid forms with the binary function that always returns zero, 
a pseudo metric space. 
*)

inline "cic:/CoRN/metrics/CPseudoMSpaces/zero_fun.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/zero_fun_strext.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/Zero_fun.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/zero_fun_com.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/zero_fun_nneg.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/zero_fun_pos_imp_ap.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/zero_fun_tri_ineq.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/zf_is_CPsMetricSpace.con".

inline "cic:/CoRN/metrics/CPseudoMSpaces/zf_as_CPsMetricSpace.con".

(* UNEXPORTED
End Zerof
*)

