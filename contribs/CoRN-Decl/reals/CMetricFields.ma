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

(* $Id: CMetricFields.v,v 1.6 2004/04/23 10:01:03 lcf Exp $ *)

(* INCLUDE
CReals1
*)

(* UNEXPORTED
Section CMetric_Fields.
*)

(*#* *Metric Fields *)

inline cic:/CoRN/reals/CMetricFields/is_CMetricField.ind.

inline cic:/CoRN/reals/CMetricFields/CMetricField.ind.

(* UNEXPORTED
End CMetric_Fields.
*)

(* UNEXPORTED
Section basics.
*)

inline cic:/CoRN/reals/CMetricFields/MAbs_one.con.

inline cic:/CoRN/reals/CMetricFields/Hulp.con.

inline cic:/CoRN/reals/CMetricFields/MAbs_one_recip_one.con.

(* end hide *)

(* UNEXPORTED
End basics.
*)

(* UNEXPORTED
Section CMetric_Field_Cauchy.
*)

inline cic:/CoRN/reals/CMetricFields/F.var.

(*#*
%\begin{convention}% Let [F:CMetricField].
%\end{convention}%
*)

inline cic:/CoRN/reals/CMetricFields/MCauchy_prop.con.

inline cic:/CoRN/reals/CMetricFields/MCauchySeq.ind.

inline cic:/CoRN/reals/CMetricFields/MseqLimit.con.

inline cic:/CoRN/reals/CMetricFields/is_MCauchyCompl.con.

(* UNEXPORTED
End CMetric_Field_Cauchy.
*)

(* UNEXPORTED
Implicit Arguments MseqLimit [F].
*)

