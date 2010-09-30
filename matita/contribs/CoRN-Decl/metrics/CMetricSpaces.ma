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

set "baseuri" "cic:/matita/CoRN-Decl/metrics/CMetricSpaces".

include "CoRN.ma".

(* $Id: CMetricSpaces.v,v 1.4 2004/04/23 10:01:01 lcf Exp $ *)

include "metrics/Prod_Sub.ma".

include "metrics/Equiv.ma".

(* UNEXPORTED
Section Definition_MS
*)

(*#* **Definition of Metric Space
*)

inline "cic:/CoRN/metrics/CMetricSpaces/CMetricSpace.ind".

coercion cic:/matita/CoRN-Decl/metrics/CMetricSpaces/scms_crr.con 0 (* compounds *).

(* UNEXPORTED
End Definition_MS
*)

(* UNEXPORTED
Section MS_basics
*)

(*#* **Metric Space basics
*)

inline "cic:/CoRN/metrics/CMetricSpaces/d_CMetricSpace_apdiag_imp_grzero.con".

inline "cic:/CoRN/metrics/CMetricSpaces/d_zero_imp_eq.con".

inline "cic:/CoRN/metrics/CMetricSpaces/is_CMetricSpace_diag_zero.con".

(* UNEXPORTED
End MS_basics
*)

(* UNEXPORTED
Section prodandsub
*)

(*#* **Product-Metric-Spaces and Sub-Metric-Spaces
*)

(*#*
The product of two metric spaces is again a metric space.
*)

inline "cic:/CoRN/metrics/CMetricSpaces/Prod0CMetricSpaces_apdiag_grzero.con".

inline "cic:/CoRN/metrics/CMetricSpaces/Prod0CMetricSpace.con".

(*#*
A subspace of a metric space is again a metric space.
*)

(* UNEXPORTED
Implicit Arguments SubPsMetricSpace [X].
*)

inline "cic:/CoRN/metrics/CMetricSpaces/SubMetricSpace_apdiag_grzero.con".

inline "cic:/CoRN/metrics/CMetricSpaces/SubMetricSpace.con".

(* UNEXPORTED
Implicit Arguments SubMetricSpace [X].
*)

(* UNEXPORTED
End prodandsub
*)

(* UNEXPORTED
Section Zeroff
*)

(*#* **Pseudo Metric Spaces vs Metric Spaces
*)

(*#*
Not all pseudo metric spaces are a metric space:
*)

inline "cic:/CoRN/metrics/CMetricSpaces/zf_nis_CMetricSpace.con".

(*#*
But a pseudo metric space induces a metric space:
*)

inline "cic:/CoRN/metrics/CMetricSpaces/metric_ap.con".

inline "cic:/CoRN/metrics/CMetricSpaces/metric_eq.con".

inline "cic:/CoRN/metrics/CMetricSpaces/metric_ap_irreflexive.con".

inline "cic:/CoRN/metrics/CMetricSpaces/metric_ap_symmetric.con".

inline "cic:/CoRN/metrics/CMetricSpaces/metric_ap_cotransitive.con".

inline "cic:/CoRN/metrics/CMetricSpaces/metric_ap_tight.con".

inline "cic:/CoRN/metrics/CMetricSpaces/Metric_CSet_is_CSetoid.con".

inline "cic:/CoRN/metrics/CMetricSpaces/Metric_CSetoid.con".

inline "cic:/CoRN/metrics/CMetricSpaces/metric_d.con".

inline "cic:/CoRN/metrics/CMetricSpaces/metric_d_strext.con".

inline "cic:/CoRN/metrics/CMetricSpaces/Metric_d.con".

inline "cic:/CoRN/metrics/CMetricSpaces/Metric_d_com.con".

inline "cic:/CoRN/metrics/CMetricSpaces/Metric_d_nneg.con".

inline "cic:/CoRN/metrics/CMetricSpaces/Metric_d_pos_imp_ap.con".

inline "cic:/CoRN/metrics/CMetricSpaces/Metric_d_tri_ineq.con".

inline "cic:/CoRN/metrics/CMetricSpaces/QuotientCSetoid_is_CPsMetricSpace.con".

inline "cic:/CoRN/metrics/CMetricSpaces/QuotientCPsMetricSpace.con".

inline "cic:/CoRN/metrics/CMetricSpaces/Metric_d_apdiag_grzero.con".

inline "cic:/CoRN/metrics/CMetricSpaces/QuotientCMetricSpace.con".

(*#*
Some pseudo metric spaces already are a metric space:
*)

inline "cic:/CoRN/metrics/CMetricSpaces/dIR_apdiag_grzero.con".

inline "cic:/CoRN/metrics/CMetricSpaces/IR_as_CMetricSpace.con".

(*#*
In that case the induced metric space is equivalent to the original one:
*)

inline "cic:/CoRN/metrics/CMetricSpaces/emb.con".

inline "cic:/CoRN/metrics/CMetricSpaces/emb_strext.con".

inline "cic:/CoRN/metrics/CMetricSpaces/Emb.con".

inline "cic:/CoRN/metrics/CMetricSpaces/Quotient_pres_CMetricSpace.con".

(* UNEXPORTED
End Zeroff
*)

(* UNEXPORTED
Section Limitt
*)

(*#* **Limit
*)

(*#*
A sequence in a metric space has at most one limit.
*)

(* UNEXPORTED
Implicit Arguments MSseqLimit [X].
*)

(* begin hide *)

inline "cic:/CoRN/metrics/CMetricSpaces/nz.con".

(* end hide *)

(* begin hide *)

inline "cic:/CoRN/metrics/CMetricSpaces/d_wd.con".

(* end hide *)

inline "cic:/CoRN/metrics/CMetricSpaces/unique_MSseqLim.con".

(* UNEXPORTED
End Limitt
*)

