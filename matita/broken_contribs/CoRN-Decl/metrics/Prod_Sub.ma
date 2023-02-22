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

set "baseuri" "cic:/matita/CoRN-Decl/metrics/Prod_Sub".

include "CoRN.ma".

(* $Id: Prod_Sub.v,v 1.4 2004/04/23 10:01:02 lcf Exp $ *)

include "metrics/IR_CPMSpace.ma".

(* UNEXPORTED
Section prodpsmetrics
*)

(*#* **Product-Pseudo-Metric-Spaces
*)

(*#*
The product metric here defined is:
$ d_{prod}((a_1,b_1),(a_2,b_2)):= d_A(a_1,a_2)+d_B(b_1,b_2)$
# d<SUB>prod</SUB>((a<SUB>1</SUB>,b<SUB>1</SUB>),(a<SUB>2</SUB>,b<SUB>2</SUB>)):= d<SUB>A</SUB>(a<SUB>1</SUB>,b<SUB>1</SUB>)+d<SUB>B</SUB>(b<SUB>1</SUB>,b<SUB>2</SUB>)#.
This is %\emph{not}% #<I>not</I># the one used to make the metric of 
$\RR^{2}$ #IR<SUP>2</SUP># out of the metric of $\RR$ #IR#. 
*)

inline "cic:/CoRN/metrics/Prod_Sub/dprod0.con".

inline "cic:/CoRN/metrics/Prod_Sub/dprod0_strext.con".

inline "cic:/CoRN/metrics/Prod_Sub/d_prod0.con".

inline "cic:/CoRN/metrics/Prod_Sub/prod0cpsmetricspace_is_CPsMetricSpace.con".

inline "cic:/CoRN/metrics/Prod_Sub/Prod0CPsMetricSpace.con".

(* UNEXPORTED
End prodpsmetrics
*)

(* UNEXPORTED
Section subpsmetrics
*)

(*#* **Sub-Pseudo-Metric-Spaces
*)

(*#*
The pseudo metric on a subspace $Y$ #Y# of a pseudo metric space $X$ #X# is 
the pseudo metric on $X$ #X# restricted to $Y$ #Y#.
*)

inline "cic:/CoRN/metrics/Prod_Sub/restr_bin_fun.con".

(* UNEXPORTED
Implicit Arguments restr_bin_fun [X].
*)

inline "cic:/CoRN/metrics/Prod_Sub/restr_bin_fun'.con".

(* UNEXPORTED
Implicit Arguments restr_bin_fun' [X].
*)

inline "cic:/CoRN/metrics/Prod_Sub/restr_bin_fun_strext.con".

inline "cic:/CoRN/metrics/Prod_Sub/Build_SubCSetoid_bin_fun.con".

inline "cic:/CoRN/metrics/Prod_Sub/dsub.con".

(* UNEXPORTED
Implicit Arguments dsub [X].
*)

inline "cic:/CoRN/metrics/Prod_Sub/dsub_com.con".

inline "cic:/CoRN/metrics/Prod_Sub/dsub_nneg.con".

inline "cic:/CoRN/metrics/Prod_Sub/dsub_pos_imp_ap.con".

inline "cic:/CoRN/metrics/Prod_Sub/dsub_tri_ineq.con".

inline "cic:/CoRN/metrics/Prod_Sub/is_SubPsMetricSpace.con".

inline "cic:/CoRN/metrics/Prod_Sub/SubPsMetricSpace.con".

(* UNEXPORTED
Implicit Arguments SubPsMetricSpace [X].
*)

inline "cic:/CoRN/metrics/Prod_Sub/from_SubPsMetricSpace.con".

(*#*
The function [dsub'] is used in the definition of %''located''% #"located"#. 
It enables one to speak about a distance between an element of a 
pseudo metric space and a certain subspace.
*)

inline "cic:/CoRN/metrics/Prod_Sub/dsub'.con".

(* UNEXPORTED
Implicit Arguments dsub' [X].
*)

inline "cic:/CoRN/metrics/Prod_Sub/dsub'_strext.con".

inline "cic:/CoRN/metrics/Prod_Sub/dsub'_as_cs_fun.con".

(* UNEXPORTED
Implicit Arguments dsub'_as_cs_fun [X].
*)

inline "cic:/CoRN/metrics/Prod_Sub/dsub'_uni_continuous''.con".

(* UNEXPORTED
End subpsmetrics
*)

