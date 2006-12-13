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

set "baseuri" "cic:/matita/CoRN-Decl/tactics/RingReflection".

include "CoRN.ma".

(* $Id: RingReflection.v,v 1.4 2004/04/23 10:01:06 lcf Exp $ *)

(* begin hide *)

include "algebra/CRings.ma".

include "tactics/AlgReflection.ma".

(* UNEXPORTED
Section Ring_Interpretation_Function
*)

alias id "R" = "cic:/CoRN/tactics/RingReflection/Ring_Interpretation_Function/R.var".

alias id "val" = "cic:/CoRN/tactics/RingReflection/Ring_Interpretation_Function/val.var".

alias id "unop" = "cic:/CoRN/tactics/RingReflection/Ring_Interpretation_Function/unop.var".

alias id "binop" = "cic:/CoRN/tactics/RingReflection/Ring_Interpretation_Function/binop.var".

alias id "pfun" = "cic:/CoRN/tactics/RingReflection/Ring_Interpretation_Function/pfun.var".

inline "cic:/CoRN/tactics/RingReflection/interpR.ind".

inline "cic:/CoRN/tactics/RingReflection/wfR.con".

inline "cic:/CoRN/tactics/RingReflection/xexprR.ind".

inline "cic:/CoRN/tactics/RingReflection/xforgetR.con".

inline "cic:/CoRN/tactics/RingReflection/xinterpR.con".

inline "cic:/CoRN/tactics/RingReflection/xexprR2interpR.con".

inline "cic:/CoRN/tactics/RingReflection/xexprR_diagram_commutes.con".

inline "cic:/CoRN/tactics/RingReflection/xexprR2wfR.con".

inline "cic:/CoRN/tactics/RingReflection/fexprR.ind".

inline "cic:/CoRN/tactics/RingReflection/fexprR_var.con".

inline "cic:/CoRN/tactics/RingReflection/fexprR_int.con".

inline "cic:/CoRN/tactics/RingReflection/fexprR_plus.con".

inline "cic:/CoRN/tactics/RingReflection/fexprR_mult.con".

inline "cic:/CoRN/tactics/RingReflection/fforgetR.con".

inline "cic:/CoRN/tactics/RingReflection/fexprR2interp.con".

inline "cic:/CoRN/tactics/RingReflection/fexprR2wf.con".

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
Opaque cr_crr.
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

(* UNEXPORTED
Opaque cr_one.
*)

(* UNEXPORTED
Opaque cr_mult.
*)

(* UNEXPORTED
Opaque nexp_op.
*)

inline "cic:/CoRN/tactics/RingReflection/refl_interpR.con".

inline "cic:/CoRN/tactics/RingReflection/interpR_wd.con".

(* UNEXPORTED
End Ring_Interpretation_Function
*)

(* UNEXPORTED
Section Ring_NormCorrect
*)

alias id "R" = "cic:/CoRN/tactics/RingReflection/Ring_NormCorrect/R.var".

alias id "val" = "cic:/CoRN/tactics/RingReflection/Ring_NormCorrect/val.var".

alias id "unop" = "cic:/CoRN/tactics/RingReflection/Ring_NormCorrect/unop.var".

alias id "binop" = "cic:/CoRN/tactics/RingReflection/Ring_NormCorrect/binop.var".

alias id "pfun" = "cic:/CoRN/tactics/RingReflection/Ring_NormCorrect/pfun.var".

(* NOTATION
Notation II := (interpR R val unop binop pfun).
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

inline "cic:/CoRN/tactics/RingReflection/MI_mult_corr_R.con".

(* UNEXPORTED
Transparent Zmult.
*)

(* UNEXPORTED
Opaque MI_mult.
*)

inline "cic:/CoRN/tactics/RingReflection/MV_mult_corr_R.con".

(* UNEXPORTED
Transparent MI_mult.
*)

(* UNEXPORTED
Opaque MV_mult MI_mult.
*)

inline "cic:/CoRN/tactics/RingReflection/MM_mult_corr_R.con".

(* UNEXPORTED
Transparent MV_mult MI_mult.
*)

(* UNEXPORTED
Opaque MV_mult.
*)

inline "cic:/CoRN/tactics/RingReflection/MM_plus_corr_R.con".

(* UNEXPORTED
Transparent MV_mult.
*)

(* UNEXPORTED
Opaque MM_plus.
*)

inline "cic:/CoRN/tactics/RingReflection/PM_plus_corr_R.con".

(* UNEXPORTED
Transparent MM_plus.
*)

(* UNEXPORTED
Opaque PM_plus.
*)

inline "cic:/CoRN/tactics/RingReflection/PP_plus_corr_R.con".

(* UNEXPORTED
Transparent PM_plus.
*)

(* UNEXPORTED
Opaque PM_plus MM_mult MI_mult.
*)

inline "cic:/CoRN/tactics/RingReflection/PM_mult_corr_R.con".

(* UNEXPORTED
Opaque PM_mult.
*)

inline "cic:/CoRN/tactics/RingReflection/PP_mult_corr_R.con".

(*
Transparent PP_plus PM_mult PP_mult PM_plus MI_mult.
Lemma FF_plus_corr_R : (e,f:expr; x,y:R)
  (II e x)->(II f y)->(II (FF_plus e f) x[+]y).
Cut (e1,e2,f1,f2:expr; x,y:R)
     (II (expr_div e1 e2) x)
     ->(II (expr_div f1 f2) y)
     ->(II
         (expr_div (PP_plus (PP_mult e1 f2) (PP_mult e2 f1))
           (PP_mult e2 f2)) x[+]y).
Cut (e,f:expr; x,y:R)(II e x)->(II f y)->(II (expr_plus e f) x[+]y).
Intros H H0 e f.
Elim e; Elim f; Intros; Simpl; Auto.
Intros. Apply interpR_plus with x y; Algebra.
Intros. Inversion H. Inversion H0.
Apply interpR_div_one with x[+]y.
Algebra.
Apply interpR_wd with x0[*]One[+]One[*]x1.
Apply PP_plus_corr_R; Apply PP_mult_corr_R; Auto;
  Apply interpR_int with k:=`1`; Algebra.
Step_final x0[+]x1.
Apply interpR_wd with (One::R)[*]One; Algebra.
Apply PP_mult_corr_R; Auto.
Qed.

Lemma FF_mult_corr_R : (e,f:expr; x,y:R)
  (II e x)->(II f y)->(II (FF_mult e f) x[*]y).
Cut (e1,e2,f1,f2:expr; x,y:R)
     (II (expr_div e1 e2) x)
     ->(II (expr_div f1 f2) y)
     ->(II (expr_div (PP_mult e1 f1) (PP_mult e2 f2)) x[*]y).
Cut (e,f:expr; x,y:R)(II e x)->(II f y)->(II (expr_mult e f) x[*]y).
Intros H H0 e f.
Elim e; Elim f; Intros; Simpl; Auto.
Intros. Apply interpR_mult with x y; Algebra.
Intros. Inversion H. Inversion H0.
Apply interpR_div_one with x0[*]x1.
Algebra.
Apply PP_mult_corr_R; Auto.
Apply interpR_wd with (One::R)[*]One; Algebra.
Apply PP_mult_corr_R; Auto.
Qed.

Transparent FF_div.
Lemma FF_div_corr_R : (e,f:expr; x:R)
  (II (expr_div e f) x)->(II (FF_div e f) x).
Intro e; Case e; Simpl; Auto.
Intros e0 e1 f; Case f; Simpl; Auto.
Intros.
Inversion H; Simpl.
Inversion H3; Inversion H5.
Apply interpR_div_one with x1[*]One.
astepl x1. Step_final x0.
Apply PP_mult_corr_R; Auto.
Apply interpR_wd with One[*]x2.
Apply PP_mult_corr_R; Auto.
Step_final x2.
Qed.
*)

inline "cic:/CoRN/tactics/RingReflection/NormR_corr.con".

inline "cic:/CoRN/tactics/RingReflection/Tactic_lemmaR.con".

(* UNEXPORTED
End Ring_NormCorrect
*)

(* end hide *)

