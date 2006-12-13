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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/Cauchy_COF".

include "CoRN.ma".

(* $Id: Cauchy_COF.v,v 1.8 2004/04/23 10:00:54 lcf Exp $ *)

include "algebra/COrdCauchy.ma".

include "tactics/RingReflection.ma".

(*#*
* The Field of Cauchy Sequences

In this chapter we will prove that whenever we start from an ordered
field [F], we can define a new ordered field of Cauchy sequences over [F].

%\begin{convention}% Let [F] be an ordered field.
%\end{convention}%
*)

(* UNEXPORTED
Section Structure
*)

alias id "F" = "cic:/CoRN/algebra/Cauchy_COF/Structure/F.var".

(*#*
** Setoid Structure

[R_Set] is the setoid of Cauchy sequences over [F]; given two sequences
[x,y] over [F], we say that [x] is smaller than [y] if from some point
onwards [(y n) [-] (x n)] is greater than some fixed, positive
[e].  Apartness of two sequences means that one of them is smaller
than the other, equality is the negation of the apartness.
*)

inline "cic:/CoRN/algebra/Cauchy_COF/R_Set.con".

(* UNEXPORTED
Section CSetoid_Structure
*)

inline "cic:/CoRN/algebra/Cauchy_COF/R_lt.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_ap.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_eq.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_lt_cotrans.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_ap_cotrans.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_ap_symmetric.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_lt_irreflexive.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_ap_irreflexive.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_ap_eq_tight.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_CSetoid.con".

(* UNEXPORTED
End CSetoid_Structure
*)

(* UNEXPORTED
Section Group_Structure
*)

(*#*
** Group Structure
The group structure is just the expected one; the lemmas which
are specifically proved are just the necessary ones to get the group axioms.
*)

inline "cic:/CoRN/algebra/Cauchy_COF/R_plus.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_zero.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_plus_lft_ext.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_plus_assoc.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_zero_lft_unit.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_plus_comm.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_inv.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_inv_is_inv.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_inv_ext.con".

inline "cic:/CoRN/algebra/Cauchy_COF/Rinv.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_CAbGroup.con".

(* UNEXPORTED
End Group_Structure
*)

(* UNEXPORTED
Section Ring_Structure
*)

(*#* ** Ring Structure
Same comments as previously.
*)

inline "cic:/CoRN/algebra/Cauchy_COF/R_mult.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_one.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_one_ap_zero.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_mult_dist_plus.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_mult_dist_minus.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_one_rht_unit.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_mult_comm.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_mult_ap_zero'.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_mult_lft_ext.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_mult_rht_ext.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_mult_strext.con".

inline "cic:/CoRN/algebra/Cauchy_COF/Rmult.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_mult_assoc.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_one_lft_unit.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_CRing.con".

(* UNEXPORTED
End Ring_Structure
*)

(* UNEXPORTED
Section Field_Structure
*)

(*#* ** Field Structure
For the field structure, it is technically easier to first prove
that our ring is actually an integral domain.  The rest then follows
quite straightforwardly.
*)

inline "cic:/CoRN/algebra/Cauchy_COF/R_integral_domain.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_recip.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_recip_inverse.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_recip_strext.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_recip_inverse'.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_CField.con".

(* UNEXPORTED
End Field_Structure
*)

(* UNEXPORTED
Section Order
*)

(*#* ** Order Structure
Finally, we extend the field structure with the ordering we
defined at the beginning.
*)

inline "cic:/CoRN/algebra/Cauchy_COF/R_lt_strext.con".

inline "cic:/CoRN/algebra/Cauchy_COF/Rlt.con".

inline "cic:/CoRN/algebra/Cauchy_COF/Rlt_transitive.con".

inline "cic:/CoRN/algebra/Cauchy_COF/Rlt_strict.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_plus_resp_lt.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_mult_resp_lt.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_COrdField.con".

(* UNEXPORTED
End Order
*)

(*#*
** Other Results
Auxiliary characterizations of the main relations on [R_Set].
*)

(* UNEXPORTED
Section Auxiliary
*)

inline "cic:/CoRN/algebra/Cauchy_COF/Rlt_alt_1.con".

inline "cic:/CoRN/algebra/Cauchy_COF/Rlt_alt_2.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_ap_alt_1.con".

inline "cic:/CoRN/algebra/Cauchy_COF/Eq_alt_1.con".

inline "cic:/CoRN/algebra/Cauchy_COF/R_ap_alt_2.con".

inline "cic:/CoRN/algebra/Cauchy_COF/Eq_alt_2_1.con".

inline "cic:/CoRN/algebra/Cauchy_COF/Eq_alt_2_2.con".

(* UNEXPORTED
End Auxiliary
*)

(* UNEXPORTED
End Structure
*)

