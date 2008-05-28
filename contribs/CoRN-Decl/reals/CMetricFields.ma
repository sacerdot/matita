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

set "baseuri" "cic:/matita/CoRN-Decl/reals/CMetricFields".

include "CoRN.ma".

(* $Id: CMetricFields.v,v 1.6 2004/04/23 10:01:03 lcf Exp $ *)

include "reals/CReals1.ma".

(* UNEXPORTED
Section CMetric_Fields
*)

(*#* *Metric Fields *)

inline "cic:/CoRN/reals/CMetricFields/is_CMetricField.ind".

inline "cic:/CoRN/reals/CMetricFields/CMetricField.ind".

coercion cic:/matita/CoRN-Decl/reals/CMetricFields/cmf_crr.con 0 (* compounds *).

(* UNEXPORTED
End CMetric_Fields
*)

(* NOTATION
Notation MAbs := (cmf_abs _).
*)

(* UNEXPORTED
Section basics
*)

inline "cic:/CoRN/reals/CMetricFields/MAbs_one.con".

inline "cic:/CoRN/reals/CMetricFields/Hulp.con".

inline "cic:/CoRN/reals/CMetricFields/MAbs_one_recip_one.con".

(* end hide *)

(* UNEXPORTED
End basics
*)

(* UNEXPORTED
Section CMetric_Field_Cauchy
*)

alias id "F" = "cic:/CoRN/reals/CMetricFields/CMetric_Field_Cauchy/F.var".

(*#*
%\begin{convention}% Let [F:CMetricField].
%\end{convention}%
*)

inline "cic:/CoRN/reals/CMetricFields/MCauchy_prop.con".

inline "cic:/CoRN/reals/CMetricFields/MCauchySeq.ind".

coercion cic:/matita/CoRN-Decl/reals/CMetricFields/MCS_seq.con 0 (* compounds *).

inline "cic:/CoRN/reals/CMetricFields/MseqLimit.con".

inline "cic:/CoRN/reals/CMetricFields/is_MCauchyCompl.con".

(* UNEXPORTED
End CMetric_Field_Cauchy
*)

(* UNEXPORTED
Implicit Arguments MseqLimit [F].
*)

