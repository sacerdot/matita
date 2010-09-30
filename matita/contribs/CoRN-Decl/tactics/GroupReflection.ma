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

set "baseuri" "cic:/matita/CoRN-Decl/tactics/GroupReflection".

include "CoRN.ma".

(* $Id: GroupReflection.v,v 1.3 2004/04/23 10:01:06 lcf Exp $ *)

(* begin hide *)

include "algebra/CAbGroups.ma".

include "tactics/AlgReflection.ma".

(* UNEXPORTED
Section Group_Interpretation_Function
*)

alias id "G" = "cic:/CoRN/tactics/GroupReflection/Group_Interpretation_Function/G.var".

alias id "val" = "cic:/CoRN/tactics/GroupReflection/Group_Interpretation_Function/val.var".

alias id "unop" = "cic:/CoRN/tactics/GroupReflection/Group_Interpretation_Function/unop.var".

alias id "binop" = "cic:/CoRN/tactics/GroupReflection/Group_Interpretation_Function/binop.var".

alias id "pfun" = "cic:/CoRN/tactics/GroupReflection/Group_Interpretation_Function/pfun.var".

inline "cic:/CoRN/tactics/GroupReflection/interpG.ind".

inline "cic:/CoRN/tactics/GroupReflection/wfG.con".

inline "cic:/CoRN/tactics/GroupReflection/xexprG.ind".

inline "cic:/CoRN/tactics/GroupReflection/xforgetG.con".

inline "cic:/CoRN/tactics/GroupReflection/xinterpG.con".

inline "cic:/CoRN/tactics/GroupReflection/xexprG2interpG.con".

inline "cic:/CoRN/tactics/GroupReflection/xexprG_diagram_commutes.con".

inline "cic:/CoRN/tactics/GroupReflection/xexprG2wfG.con".

inline "cic:/CoRN/tactics/GroupReflection/fexprG.ind".

inline "cic:/CoRN/tactics/GroupReflection/fexprG_var.con".

inline "cic:/CoRN/tactics/GroupReflection/fexprG_zero.con".

inline "cic:/CoRN/tactics/GroupReflection/fexprG_plus.con".

inline "cic:/CoRN/tactics/GroupReflection/fexprG_mult_int.con".

inline "cic:/CoRN/tactics/GroupReflection/fforgetG.con".

inline "cic:/CoRN/tactics/GroupReflection/fexprG2interp.con".

inline "cic:/CoRN/tactics/GroupReflection/fexprG2wf.con".

(* UNEXPORTED
Opaque csg_crr.
*)

(* UNEXPORTED
Opaque cm_crr.
*)

(* UNEXPORTED
Opaque cg_crr.
*)

(* UNEXPORTED
Opaque csf_fun.
*)

(* UNEXPORTED
Opaque csbf_fun.
*)

(* UNEXPORTED
Opaque csr_rel.
*)

(* UNEXPORTED
Opaque cs_eq.
*)

(* UNEXPORTED
Opaque cs_neq.
*)

(* UNEXPORTED
Opaque cs_ap.
*)

(* UNEXPORTED
Opaque cm_unit.
*)

(* UNEXPORTED
Opaque csg_op.
*)

(* UNEXPORTED
Opaque cg_inv.
*)

(* UNEXPORTED
Opaque cg_minus.
*)

inline "cic:/CoRN/tactics/GroupReflection/refl_interpG.con".

inline "cic:/CoRN/tactics/GroupReflection/interpG_wd.con".

(* UNEXPORTED
End Group_Interpretation_Function
*)

(* UNEXPORTED
Section Group_NormCorrect
*)

alias id "G" = "cic:/CoRN/tactics/GroupReflection/Group_NormCorrect/G.var".

alias id "val" = "cic:/CoRN/tactics/GroupReflection/Group_NormCorrect/val.var".

alias id "unop" = "cic:/CoRN/tactics/GroupReflection/Group_NormCorrect/unop.var".

alias id "binop" = "cic:/CoRN/tactics/GroupReflection/Group_NormCorrect/binop.var".

alias id "pfun" = "cic:/CoRN/tactics/GroupReflection/Group_NormCorrect/pfun.var".

(* NOTATION
Notation II := (interpG G val unop binop pfun).
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

inline "cic:/CoRN/tactics/GroupReflection/MI_mult_comm_int.con".

(* UNEXPORTED
Opaque Zmult.
*)

inline "cic:/CoRN/tactics/GroupReflection/MI_mult_corr_G.con".

(* UNEXPORTED
Transparent Zmult.
*)

(* UNEXPORTED
Opaque MI_mult.
*)

inline "cic:/CoRN/tactics/GroupReflection/MV_mult_corr_G.con".

(* UNEXPORTED
Opaque MV_mult.
*)

inline "cic:/CoRN/tactics/GroupReflection/MM_mult_corr_G.con".

(* UNEXPORTED
Transparent MV_mult MI_mult.
*)

(* UNEXPORTED
Opaque MV_mult.
*)

inline "cic:/CoRN/tactics/GroupReflection/MM_plus_corr_G.con".

(* UNEXPORTED
Transparent MV_mult.
*)

(* UNEXPORTED
Opaque MM_plus.
*)

inline "cic:/CoRN/tactics/GroupReflection/PM_plus_corr_G.con".

(* UNEXPORTED
Transparent MM_plus.
*)

(* UNEXPORTED
Opaque PM_plus.
*)

inline "cic:/CoRN/tactics/GroupReflection/PP_plus_corr_G.con".

(* UNEXPORTED
Transparent PM_plus.
*)

(* UNEXPORTED
Opaque PM_plus MM_mult MI_mult.
*)

inline "cic:/CoRN/tactics/GroupReflection/PM_mult_corr_G.con".

(* UNEXPORTED
Opaque PM_mult.
*)

inline "cic:/CoRN/tactics/GroupReflection/PP_mult_corr_G.con".

inline "cic:/CoRN/tactics/GroupReflection/NormG_corr_G.con".

inline "cic:/CoRN/tactics/GroupReflection/Tactic_lemmaG.con".

(* UNEXPORTED
End Group_NormCorrect
*)

(* end hide *)

