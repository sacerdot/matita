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

set "baseuri" "cic:/matita/CoRN-Decl/tactics/FieldReflection".

include "CoRN.ma".

(* $Id: FieldReflection.v,v 1.4 2004/04/23 10:01:06 lcf Exp $ *)

(* begin hide *)

include "algebra/CFields.ma".

include "tactics/AlgReflection.ma".

(* UNEXPORTED
Section Field_Interpretation_Function
*)

alias id "F" = "cic:/CoRN/tactics/FieldReflection/Field_Interpretation_Function/F.var".

alias id "val" = "cic:/CoRN/tactics/FieldReflection/Field_Interpretation_Function/val.var".

alias id "unop" = "cic:/CoRN/tactics/FieldReflection/Field_Interpretation_Function/unop.var".

alias id "binop" = "cic:/CoRN/tactics/FieldReflection/Field_Interpretation_Function/binop.var".

alias id "pfun" = "cic:/CoRN/tactics/FieldReflection/Field_Interpretation_Function/pfun.var".

inline "cic:/CoRN/tactics/FieldReflection/interpF.ind".

inline "cic:/CoRN/tactics/FieldReflection/wfF.con".

inline "cic:/CoRN/tactics/FieldReflection/xexprF.ind".

inline "cic:/CoRN/tactics/FieldReflection/xforgetF.con".

inline "cic:/CoRN/tactics/FieldReflection/xinterpF.con".

inline "cic:/CoRN/tactics/FieldReflection/xexprF2interpF.con".

inline "cic:/CoRN/tactics/FieldReflection/xexprF_diagram_commutes.con".

inline "cic:/CoRN/tactics/FieldReflection/xexprF2wfF.con".

inline "cic:/CoRN/tactics/FieldReflection/fexprF.ind".

inline "cic:/CoRN/tactics/FieldReflection/fexprF_var.con".

inline "cic:/CoRN/tactics/FieldReflection/fexprF_int.con".

inline "cic:/CoRN/tactics/FieldReflection/fexprF_plus.con".

inline "cic:/CoRN/tactics/FieldReflection/fexprF_mult.con".

inline "cic:/CoRN/tactics/FieldReflection/fforgetF.con".

inline "cic:/CoRN/tactics/FieldReflection/fexprF2interpF.con".

inline "cic:/CoRN/tactics/FieldReflection/fexprF2wfF.con".

include "tactics/Opaque_algebra.ma".

inline "cic:/CoRN/tactics/FieldReflection/refl_interpF.con".

inline "cic:/CoRN/tactics/FieldReflection/interpF_wd.con".

(* UNEXPORTED
End Field_Interpretation_Function
*)

(* UNEXPORTED
Section Field_NormCorrect
*)

alias id "F" = "cic:/CoRN/tactics/FieldReflection/Field_NormCorrect/F.var".

alias id "val" = "cic:/CoRN/tactics/FieldReflection/Field_NormCorrect/val.var".

alias id "unop" = "cic:/CoRN/tactics/FieldReflection/Field_NormCorrect/unop.var".

alias id "binop" = "cic:/CoRN/tactics/FieldReflection/Field_NormCorrect/binop.var".

alias id "pfun" = "cic:/CoRN/tactics/FieldReflection/Field_NormCorrect/pfun.var".

(* NOTATION
Notation II := (interpF F val unop binop pfun).
*)

(*
four kinds of exprs:

  I	(expr_int _)
  V	(expr_var _)
  M	(expr_mult V M)
	I
  P	(expr_plus M P)
	I

M: sorted on V
P: sorted on M, all M's not an I
*)

(* UNEXPORTED
Opaque Zmult.
*)

inline "cic:/CoRN/tactics/FieldReflection/MI_mult_corr_F.con".

(* UNEXPORTED
Transparent Zmult.
*)

(* UNEXPORTED
Opaque MI_mult.
*)

inline "cic:/CoRN/tactics/FieldReflection/MV_mult_corr_F.con".

(* UNEXPORTED
Transparent MI_mult.
*)

(* UNEXPORTED
Opaque MV_mult MI_mult.
*)

inline "cic:/CoRN/tactics/FieldReflection/MM_mult_corr_F.con".

(* UNEXPORTED
Transparent MV_mult MI_mult.
*)

(* UNEXPORTED
Opaque MV_mult.
*)

inline "cic:/CoRN/tactics/FieldReflection/MM_plus_corr_F.con".

(* UNEXPORTED
Transparent MV_mult.
*)

(* UNEXPORTED
Opaque MM_plus.
*)

inline "cic:/CoRN/tactics/FieldReflection/PM_plus_corr_F.con".

(* UNEXPORTED
Transparent MM_plus.
*)

(* UNEXPORTED
Opaque PM_plus.
*)

inline "cic:/CoRN/tactics/FieldReflection/PP_plus_corr_F.con".

(* UNEXPORTED
Transparent PM_plus.
*)

(* UNEXPORTED
Opaque PM_plus MM_mult MI_mult.
*)

inline "cic:/CoRN/tactics/FieldReflection/PM_mult_corr_F.con".

(* UNEXPORTED
Opaque PM_mult.
*)

inline "cic:/CoRN/tactics/FieldReflection/PP_mult_corr_F.con".

(* UNEXPORTED
Transparent PP_plus PM_mult PP_mult PM_plus MI_mult.
*)

inline "cic:/CoRN/tactics/FieldReflection/FF_plus_corr_F.con".

inline "cic:/CoRN/tactics/FieldReflection/FF_mult_corr_F.con".

(* UNEXPORTED
Transparent FF_div.
*)

inline "cic:/CoRN/tactics/FieldReflection/FF_div_corr_F.con".

inline "cic:/CoRN/tactics/FieldReflection/NormF_corr.con".

inline "cic:/CoRN/tactics/FieldReflection/Norm_wfF.con".

inline "cic:/CoRN/tactics/FieldReflection/expr_is_zero_corr_F.con".

inline "cic:/CoRN/tactics/FieldReflection/Tactic_lemma_zero_F.con".

inline "cic:/CoRN/tactics/FieldReflection/Tactic_lemmaF.con".

(* UNEXPORTED
End Field_NormCorrect
*)

(* end hide *)

