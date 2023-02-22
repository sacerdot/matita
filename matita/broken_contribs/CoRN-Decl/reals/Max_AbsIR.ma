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

set "baseuri" "cic:/matita/CoRN-Decl/reals/Max_AbsIR".

include "CoRN.ma".

(* $Id: Max_AbsIR.v,v 1.13 2004/04/23 10:01:04 lcf Exp $ *)

(*#* printing Max %\ensuremath{\max}% *)

(*#* printing Min %\ensuremath{\min}% *)

include "reals/CauchySeq.ma".

(* UNEXPORTED
Section Maximum
*)

(* UNEXPORTED
Section Max_function
*)

(*#* ** Maximum, Minimum and Absolute Value

%\begin{convention}%
Let [x] and [y] be reals
(we will define the maximum of [x] and [y]).
%\end{convention}%
*)

alias id "x" = "cic:/CoRN/reals/Max_AbsIR/Maximum/Max_function/x.var".

alias id "y" = "cic:/CoRN/reals/Max_AbsIR/Maximum/Max_function/y.var".

inline "cic:/CoRN/reals/Max_AbsIR/Max_seq.con".

inline "cic:/CoRN/reals/Max_AbsIR/Max_seq_char.con".

inline "cic:/CoRN/reals/Max_AbsIR/Cauchy_Max_seq.con".

inline "cic:/CoRN/reals/Max_AbsIR/Max_CauchySeq.con".

inline "cic:/CoRN/reals/Max_AbsIR/MAX.con".

(*#*
Constructively, the elementary properties of the maximum function are:
- [x [<=] Max (x,y)],
- [x [<=] Max (y,x)],
- [z [<] Max(x,y) -> z [<] x or z [<] y].

(This can be more concisely expressed as
[z [<] Max(x,y) Iff z [<] x or z [<] y]).
From these elementary properties we can prove all other properties, including
strong extensionality.
With strong extensionality, we can make the binary operation [Max].
(So [Max] is [MAX] coupled with some proofs.)
*)

inline "cic:/CoRN/reals/Max_AbsIR/lft_leEq_MAX.con".

inline "cic:/CoRN/reals/Max_AbsIR/rht_leEq_MAX.con".

inline "cic:/CoRN/reals/Max_AbsIR/less_MAX_imp.con".

(* UNEXPORTED
End Max_function
*)

inline "cic:/CoRN/reals/Max_AbsIR/MAX_strext.con".

inline "cic:/CoRN/reals/Max_AbsIR/MAX_wd.con".

(* UNEXPORTED
Section properties_of_Max
*)

(*#* *** Maximum *)

inline "cic:/CoRN/reals/Max_AbsIR/Max.con".

inline "cic:/CoRN/reals/Max_AbsIR/Max_wd_unfolded.con".

inline "cic:/CoRN/reals/Max_AbsIR/lft_leEq_Max.con".

inline "cic:/CoRN/reals/Max_AbsIR/rht_leEq_Max.con".

inline "cic:/CoRN/reals/Max_AbsIR/less_Max_imp.con".

inline "cic:/CoRN/reals/Max_AbsIR/Max_leEq.con".

inline "cic:/CoRN/reals/Max_AbsIR/Max_less.con".

inline "cic:/CoRN/reals/Max_AbsIR/equiv_imp_eq_max.con".

inline "cic:/CoRN/reals/Max_AbsIR/Max_id.con".

inline "cic:/CoRN/reals/Max_AbsIR/Max_comm.con".

inline "cic:/CoRN/reals/Max_AbsIR/leEq_imp_Max_is_rht.con".

inline "cic:/CoRN/reals/Max_AbsIR/Max_is_rht_imp_leEq.con".

inline "cic:/CoRN/reals/Max_AbsIR/Max_minus_eps_leEq.con".

inline "cic:/CoRN/reals/Max_AbsIR/max_one_ap_zero.con".

inline "cic:/CoRN/reals/Max_AbsIR/pos_max_one.con".

inline "cic:/CoRN/reals/Max_AbsIR/x_div_Max_leEq_x.con".

(* UNEXPORTED
End properties_of_Max
*)

(* UNEXPORTED
End Maximum
*)

(* UNEXPORTED
Hint Resolve Max_id: algebra.
*)

(* UNEXPORTED
Section Minimum
*)

(*#* *** Mininum

The minimum is defined by the formula 
[Min(x,y) [=] [--]Max( [--]x,[--]y)].
*)

inline "cic:/CoRN/reals/Max_AbsIR/MIN.con".

inline "cic:/CoRN/reals/Max_AbsIR/MIN_wd.con".

inline "cic:/CoRN/reals/Max_AbsIR/MIN_strext.con".

inline "cic:/CoRN/reals/Max_AbsIR/Min.con".

inline "cic:/CoRN/reals/Max_AbsIR/Min_wd_unfolded.con".

inline "cic:/CoRN/reals/Max_AbsIR/Min_strext_unfolded.con".

inline "cic:/CoRN/reals/Max_AbsIR/Min_leEq_lft.con".

inline "cic:/CoRN/reals/Max_AbsIR/Min_leEq_rht.con".

inline "cic:/CoRN/reals/Max_AbsIR/Min_less_imp.con".

inline "cic:/CoRN/reals/Max_AbsIR/leEq_Min.con".

inline "cic:/CoRN/reals/Max_AbsIR/less_Min.con".

inline "cic:/CoRN/reals/Max_AbsIR/equiv_imp_eq_min.con".

inline "cic:/CoRN/reals/Max_AbsIR/Min_id.con".

inline "cic:/CoRN/reals/Max_AbsIR/Min_comm.con".

inline "cic:/CoRN/reals/Max_AbsIR/leEq_imp_Min_is_lft.con".

inline "cic:/CoRN/reals/Max_AbsIR/Min_is_lft_imp_leEq.con".

inline "cic:/CoRN/reals/Max_AbsIR/leEq_Min_plus_eps.con".

alias id "a" = "cic:/CoRN/reals/Max_AbsIR/Minimum/a.var".

alias id "b" = "cic:/CoRN/reals/Max_AbsIR/Minimum/b.var".

inline "cic:/CoRN/reals/Max_AbsIR/Min_leEq_Max.con".

inline "cic:/CoRN/reals/Max_AbsIR/Min_leEq_Max'.con".

inline "cic:/CoRN/reals/Max_AbsIR/Min3_leEq_Max3.con".

inline "cic:/CoRN/reals/Max_AbsIR/Min_less_Max.con".

inline "cic:/CoRN/reals/Max_AbsIR/ap_imp_Min_less_Max.con".

inline "cic:/CoRN/reals/Max_AbsIR/Min_less_Max_imp_ap.con".

(* UNEXPORTED
End Minimum
*)

(*#**********************************)

(* UNEXPORTED
Section Absolute
*)

(*#**********************************)

(*#* *** Absolute value *)

inline "cic:/CoRN/reals/Max_AbsIR/ABSIR.con".

inline "cic:/CoRN/reals/Max_AbsIR/ABSIR_strext.con".

inline "cic:/CoRN/reals/Max_AbsIR/ABSIR_wd.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_wd.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_wdl.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_wdr.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIRz_isz.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_nonneg.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_pos.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_cancel_ap_zero.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_resp_ap_zero.con".

inline "cic:/CoRN/reals/Max_AbsIR/leEq_AbsIR.con".

inline "cic:/CoRN/reals/Max_AbsIR/inv_leEq_AbsIR.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsSmall_e.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsSmall_imp_AbsIR.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_eq_AbsSmall.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_imp_AbsSmall.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsSmall_transitive.con".

inline "cic:/CoRN/reals/Max_AbsIR/zero_less_AbsIR_plus_one.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_inv.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_minus.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_eq_x.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_eq_inv_x.con".

inline "cic:/CoRN/reals/Max_AbsIR/less_AbsIR.con".

inline "cic:/CoRN/reals/Max_AbsIR/leEq_distr_AbsIR.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_approach_zero.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_eq_zero.con".

inline "cic:/CoRN/reals/Max_AbsIR/Abs_Max.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_str_bnd.con".

inline "cic:/CoRN/reals/Max_AbsIR/AbsIR_bnd.con".

(* UNEXPORTED
End Absolute
*)

(* UNEXPORTED
Hint Resolve AbsIRz_isz: algebra.
*)

(* UNEXPORTED
Section Part_Function_Max
*)

(*#* *** Functional Operators

The existence of these operators allows us to lift them to functions.  We will define the maximum, minimum and absolute value of two partial functions.

%\begin{convention}%
Let [F,G:PartIR] and denote by [P] and [Q] their respective domains.
%\end{convention}%
*)

alias id "F" = "cic:/CoRN/reals/Max_AbsIR/Part_Function_Max/F.var".

alias id "G" = "cic:/CoRN/reals/Max_AbsIR/Part_Function_Max/G.var".

(* begin hide *)

inline "cic:/CoRN/reals/Max_AbsIR/Part_Function_Max/P.con" "Part_Function_Max__".

inline "cic:/CoRN/reals/Max_AbsIR/Part_Function_Max/Q.con" "Part_Function_Max__".

(* end hide *)

inline "cic:/CoRN/reals/Max_AbsIR/part_function_Max_strext.con".

inline "cic:/CoRN/reals/Max_AbsIR/FMax.con".

(* UNEXPORTED
End Part_Function_Max
*)

(* UNEXPORTED
Section Part_Function_Abs
*)

alias id "F" = "cic:/CoRN/reals/Max_AbsIR/Part_Function_Abs/F.var".

alias id "G" = "cic:/CoRN/reals/Max_AbsIR/Part_Function_Abs/G.var".

(* begin hide *)

inline "cic:/CoRN/reals/Max_AbsIR/Part_Function_Abs/P.con" "Part_Function_Abs__".

inline "cic:/CoRN/reals/Max_AbsIR/Part_Function_Abs/Q.con" "Part_Function_Abs__".

(* end hide *)

inline "cic:/CoRN/reals/Max_AbsIR/FMin.con".

inline "cic:/CoRN/reals/Max_AbsIR/FAbs.con".

(* UNEXPORTED
Opaque Max.
*)

inline "cic:/CoRN/reals/Max_AbsIR/FMin_char.con".

(* UNEXPORTED
Transparent Max.
*)

inline "cic:/CoRN/reals/Max_AbsIR/FAbs_char.con".

(* UNEXPORTED
End Part_Function_Abs
*)

(* UNEXPORTED
Hint Resolve FAbs_char: algebra.
*)

inline "cic:/CoRN/reals/Max_AbsIR/FAbs_char'.con".

inline "cic:/CoRN/reals/Max_AbsIR/FAbs_nonneg.con".

(* UNEXPORTED
Hint Resolve FAbs_char': algebra.
*)

(* UNEXPORTED
Section Inclusion
*)

alias id "F" = "cic:/CoRN/reals/Max_AbsIR/Inclusion/F.var".

alias id "G" = "cic:/CoRN/reals/Max_AbsIR/Inclusion/G.var".

(* begin hide *)

inline "cic:/CoRN/reals/Max_AbsIR/Inclusion/P.con" "Inclusion__".

inline "cic:/CoRN/reals/Max_AbsIR/Inclusion/Q.con" "Inclusion__".

(* end hide *)

(*#*
%\begin{convention}% Let [R:IR->CProp].
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/reals/Max_AbsIR/Inclusion/R.var".

inline "cic:/CoRN/reals/Max_AbsIR/included_FMax.con".

inline "cic:/CoRN/reals/Max_AbsIR/included_FMax'.con".

inline "cic:/CoRN/reals/Max_AbsIR/included_FMax''.con".

inline "cic:/CoRN/reals/Max_AbsIR/included_FMin.con".

inline "cic:/CoRN/reals/Max_AbsIR/included_FMin'.con".

inline "cic:/CoRN/reals/Max_AbsIR/included_FMin''.con".

inline "cic:/CoRN/reals/Max_AbsIR/included_FAbs.con".

inline "cic:/CoRN/reals/Max_AbsIR/included_FAbs'.con".

(* UNEXPORTED
End Inclusion
*)

(* UNEXPORTED
Hint Resolve included_FMax included_FMin included_FAbs : included.
*)

(* UNEXPORTED
Hint Immediate included_FMax' included_FMin' included_FAbs'
  included_FMax'' included_FMin'' : included.
*)

