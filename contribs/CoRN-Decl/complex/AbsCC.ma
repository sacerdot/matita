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

set "baseuri" "cic:/matita/CoRN-Decl/complex/AbsCC".

include "CoRN.ma".

(* $Id: AbsCC.v,v 1.2 2004/04/23 10:00:54 lcf Exp $ *)

include "complex/CComplex.ma".

(*#* * Absolute value on [CC]
** Properties of [AbsCC] *)

(* UNEXPORTED
Section AbsCC_properties
*)

inline "cic:/CoRN/complex/AbsCC/AbsCC_nonneg.con".

inline "cic:/CoRN/complex/AbsCC/AbsCC_ap_zero_imp_pos.con".

inline "cic:/CoRN/complex/AbsCC/AbsCC_wd.con".

(* UNEXPORTED
Hint Resolve AbsCC_wd: algebra_c.
*)

inline "cic:/CoRN/complex/AbsCC/cc_inv_abs.con".

(* UNEXPORTED
Hint Resolve cc_inv_abs: algebra.
*)

inline "cic:/CoRN/complex/AbsCC/cc_minus_abs.con".

inline "cic:/CoRN/complex/AbsCC/cc_mult_abs.con".

(* UNEXPORTED
Hint Resolve cc_mult_abs: algebra.
*)

inline "cic:/CoRN/complex/AbsCC/AbsCC_minzero.con".

inline "cic:/CoRN/complex/AbsCC/AbsCC_IR.con".

(* UNEXPORTED
Hint Resolve AbsCC_IR: algebra.
*)

inline "cic:/CoRN/complex/AbsCC/cc_div_abs.con".

inline "cic:/CoRN/complex/AbsCC/cc_div_abs'.con".

inline "cic:/CoRN/complex/AbsCC/AbsCC_zero.con".

(* UNEXPORTED
Hint Resolve AbsCC_zero: algebra.
*)

inline "cic:/CoRN/complex/AbsCC/AbsCC_one.con".

inline "cic:/CoRN/complex/AbsCC/cc_pow_abs.con".

inline "cic:/CoRN/complex/AbsCC/AbsCC_pos.con".

inline "cic:/CoRN/complex/AbsCC/AbsCC_ap_zero.con".

inline "cic:/CoRN/complex/AbsCC/AbsCC_small_imp_eq.con".

(* begin hide *)

inline "cic:/CoRN/complex/AbsCC/AbsCC_properties/l_1_1_2.con" "AbsCC_properties__".

(* end hide *)

(* UNEXPORTED
Hint Resolve l_1_1_2: algebra.
*)

inline "cic:/CoRN/complex/AbsCC/AbsCC_square_Re_Im.con".

(* UNEXPORTED
Hint Resolve AbsCC_square_Re_Im: algebra.
*)

(* begin hide *)

inline "cic:/CoRN/complex/AbsCC/AbsCC_properties/l_1_2_3_CC.con" "AbsCC_properties__".

(* end hide *)

(* UNEXPORTED
Hint Resolve l_1_2_3_CC: algebra.
*)

inline "cic:/CoRN/complex/AbsCC/AbsCC_mult_conj.con".

(* UNEXPORTED
Hint Resolve CC_conj_mult: algebra.
*)

(* begin hide *)

inline "cic:/CoRN/complex/AbsCC/l_2_1_2.con".

(* UNEXPORTED
Hint Resolve l_2_1_2: algebra.
*)

(* end hide *)

inline "cic:/CoRN/complex/AbsCC/AbsCC_mult_square.con".

inline "cic:/CoRN/complex/AbsCC/AbsCC_square_ap_zero.con".

inline "cic:/CoRN/complex/AbsCC/cc_recip_char.con".

inline "cic:/CoRN/complex/AbsCC/AbsCC_strext.con".

inline "cic:/CoRN/complex/AbsCC/AbsSmallCC.con".

inline "cic:/CoRN/complex/AbsCC/Cexis_AFS_CC.con".

(* The following lemmas are just auxiliary results *)

(* begin hide *)

inline "cic:/CoRN/complex/AbsCC/AbsCC_properties/l_4_1_2.con" "AbsCC_properties__".

inline "cic:/CoRN/complex/AbsCC/AbsCC_properties/l_4_2_3.con" "AbsCC_properties__".

inline "cic:/CoRN/complex/AbsCC/AbsCC_properties/l_4_3_4.con" "AbsCC_properties__".

(* end hide *)

(* UNEXPORTED
End AbsCC_properties
*)

(* UNEXPORTED
Hint Resolve AbsCC_wd: algebra_c.
*)

(* UNEXPORTED
Hint Resolve cc_inv_abs cc_mult_abs cc_div_abs cc_div_abs' cc_pow_abs
  AbsCC_zero AbsCC_one AbsCC_IR AbsCC_mult_conj AbsCC_mult_square
  cc_recip_char: algebra.
*)

(*#* ** The triangle inequality *)

inline "cic:/CoRN/complex/AbsCC/triangle.con".

inline "cic:/CoRN/complex/AbsCC/triangle_Sum.con".

