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

set "baseuri" "cic:/matita/CoRN-Decl/complex/CComplex".

include "CoRN.ma".

(* $Id: CComplex.v,v 1.8 2004/04/23 10:00:55 lcf Exp $ *)

(*#* printing Re %\ensuremath{\Re}% #&real;# *)

(*#* printing Im %\ensuremath{\Im}% #&image;# *)

(*#* printing CC %\ensuremath{\mathbb C}% #<b>C</b># *)

(*#* printing II %\ensuremath{\imath}% #i# *)

(*#* printing [+I*] %\ensuremath{+\imath}% *)

(*#* printing AbsCC %\ensuremath{|\cdot|_{\mathbb C}}% *)

(*#* printing CCX %\ensuremath{\mathbb C[X]}% #<b>C</b>[X]# *)

include "reals/NRootIR.ma".

(*#* * Complex Numbers
** Algebraic structure
*)

(* UNEXPORTED
Section Complex_Numbers
*)

inline "cic:/CoRN/complex/CComplex/CC_set.ind".

inline "cic:/CoRN/complex/CComplex/cc_ap.con".

inline "cic:/CoRN/complex/CComplex/cc_eq.con".

inline "cic:/CoRN/complex/CComplex/cc_is_CSetoid.con".

inline "cic:/CoRN/complex/CComplex/cc_csetoid.con".

inline "cic:/CoRN/complex/CComplex/cc_plus.con".

inline "cic:/CoRN/complex/CComplex/cc_mult.con".

inline "cic:/CoRN/complex/CComplex/cc_zero.con".

inline "cic:/CoRN/complex/CComplex/cc_one.con".

inline "cic:/CoRN/complex/CComplex/cc_i.con".

inline "cic:/CoRN/complex/CComplex/cc_inv.con".

(* not needed anymore
Lemma cc_plus_op_proof : (bin_op_wd cc_csetoid cc_plus).
Unfold bin_op_wd. Unfold bin_fun_wd.
Intros x1 x2 y1 y2. Elim x1. Elim x2. Elim y1. Elim y2.
Simpl. Unfold cc_eq. Simpl. Intros.
Elim H. Clear H. Intros. Elim H0. Clear H0. Intros.
Split; Algebra.
Qed.

Lemma cc_mult_op_proof : (bin_op_wd cc_csetoid cc_mult).
Unfold bin_op_wd. Unfold bin_fun_wd.
Intros x1 x2 y1 y2. Elim x1. Elim x2. Elim y1. Elim y2.
Simpl. Unfold cc_eq. Simpl. Intros.
Elim H. Clear H. Intros. Elim H0. Clear H0. Intros.
Split; Algebra.
Qed.

Lemma cc_inv_op_proof : (un_op_wd cc_csetoid cc_inv).
Unfold un_op_wd. Unfold fun_wd.
Intros x y. Elim x. Elim y.
Simpl. Unfold cc_eq. Simpl. Intros.
Elim H. Clear H. Intros.
Split; Algebra.
Qed.
*)

inline "cic:/CoRN/complex/CComplex/cc_inv_strext.con".

inline "cic:/CoRN/complex/CComplex/cc_plus_strext.con".

inline "cic:/CoRN/complex/CComplex/cc_mult_strext.con".

inline "cic:/CoRN/complex/CComplex/cc_inv_op.con".

inline "cic:/CoRN/complex/CComplex/cc_plus_op.con".

inline "cic:/CoRN/complex/CComplex/cc_mult_op.con".

inline "cic:/CoRN/complex/CComplex/cc_csg_associative.con".

inline "cic:/CoRN/complex/CComplex/cc_cr_mult_associative.con".

inline "cic:/CoRN/complex/CComplex/cc_csemi_grp.con".

inline "cic:/CoRN/complex/CComplex/cc_cm_proof.con".

inline "cic:/CoRN/complex/CComplex/cc_cmonoid.con".

inline "cic:/CoRN/complex/CComplex/cc_cg_proof.con".

inline "cic:/CoRN/complex/CComplex/cc_cr_dist.con".

inline "cic:/CoRN/complex/CComplex/cc_cr_non_triv.con".

inline "cic:/CoRN/complex/CComplex/cc_cgroup.con".

inline "cic:/CoRN/complex/CComplex/cc_cabgroup.con".

inline "cic:/CoRN/complex/CComplex/cc_cr_mult_mon.con".

inline "cic:/CoRN/complex/CComplex/cc_mult_commutes.con".

inline "cic:/CoRN/complex/CComplex/cc_isCRing.con".

inline "cic:/CoRN/complex/CComplex/cc_cring.con".

inline "cic:/CoRN/complex/CComplex/cc_ap_zero.con".

inline "cic:/CoRN/complex/CComplex/cc_inv_aid.con".

(*#*
If [x [~=] Zero] or [y [~=] Zero], then  [x [/] x[^]2 [+] y[^]2 [~=] Zero] or
[[--]y[/]x[^]2[+]y[^]2 [~=] Zero].
*)

inline "cic:/CoRN/complex/CComplex/cc_inv_aid2.con".

(*
REMARK KEPT FOR SENTIMENTAL REASONS...

This definition seems clever.  Even though we *cannot* construct an
element of (NonZeros cc_cring) (a Set) by deciding which part of the
input (Re or Im) is NonZero (a Prop), we manage to construct the
actual function.
*)

inline "cic:/CoRN/complex/CComplex/cc_recip.con".

inline "cic:/CoRN/complex/CComplex/cc_cfield_proof.con".

inline "cic:/CoRN/complex/CComplex/cc_Recip_proof.con".

(* UNEXPORTED
Opaque cc_recip.
*)

(* UNEXPORTED
Opaque cc_inv.
*)

inline "cic:/CoRN/complex/CComplex/cc_cfield.con".

inline "cic:/CoRN/complex/CComplex/CC.con".

(*#*
Maps from reals to complex and vice-versa are defined, as well as conjugate,
absolute value and the imaginary unit [I] *)

inline "cic:/CoRN/complex/CComplex/cc_set_CC.con".

inline "cic:/CoRN/complex/CComplex/cc_IR.con".

inline "cic:/CoRN/complex/CComplex/CC_conj.con".

(* old def
Definition CC_conj' : CC->CC := [z:CC_set] (CC_set_rec [_:CC_set]CC_set [Re0,Im0:IR] (Build_CC_set Re0 [--]Im0) z).
*)

inline "cic:/CoRN/complex/CComplex/AbsCC.con".

inline "cic:/CoRN/complex/CComplex/TwoCC_ap_zero.con".

(* UNEXPORTED
End Complex_Numbers
*)

(* begin hide *)

(* NOTATION
Notation CCX := (cpoly_cring CC).
*)

(* end hide *)

inline "cic:/CoRN/complex/CComplex/II.con".

(* NOTATION
Infix "[+I*]" := cc_set_CC (at level 48, no associativity).
*)

(*#* ** Properties of [II] *)

(* UNEXPORTED
Section I_properties
*)

inline "cic:/CoRN/complex/CComplex/I_square.con".

(* UNEXPORTED
Hint Resolve I_square: algebra.
*)

inline "cic:/CoRN/complex/CComplex/I_square'.con".

inline "cic:/CoRN/complex/CComplex/I_recip_lft.con".

inline "cic:/CoRN/complex/CComplex/I_recip_rht.con".

inline "cic:/CoRN/complex/CComplex/mult_I.con".

inline "cic:/CoRN/complex/CComplex/I_wd.con".

(*#* ** Properties of [Re] and [Im] *)

inline "cic:/CoRN/complex/CComplex/calculate_norm.con".

inline "cic:/CoRN/complex/CComplex/calculate_Re.con".

inline "cic:/CoRN/complex/CComplex/calculate_Im.con".

inline "cic:/CoRN/complex/CComplex/Re_wd.con".

inline "cic:/CoRN/complex/CComplex/Im_wd.con".

inline "cic:/CoRN/complex/CComplex/Re_resp_plus.con".

inline "cic:/CoRN/complex/CComplex/Re_resp_inv.con".

inline "cic:/CoRN/complex/CComplex/Im_resp_plus.con".

inline "cic:/CoRN/complex/CComplex/Im_resp_inv.con".

inline "cic:/CoRN/complex/CComplex/cc_calculate_square.con".

(* UNEXPORTED
End I_properties
*)

(* UNEXPORTED
Hint Resolve I_square I_square' I_recip_lft I_recip_rht mult_I calculate_norm
  cc_calculate_square: algebra.
*)

(* UNEXPORTED
Hint Resolve I_wd Re_wd Im_wd: algebra_c.
*)

(*#* ** Properties of conjugation *)

(* UNEXPORTED
Section Conj_properties
*)

inline "cic:/CoRN/complex/CComplex/CC_conj_plus.con".

inline "cic:/CoRN/complex/CComplex/CC_conj_mult.con".

(* UNEXPORTED
Hint Resolve CC_conj_mult: algebra.
*)

inline "cic:/CoRN/complex/CComplex/CC_conj_strext.con".

inline "cic:/CoRN/complex/CComplex/CC_conj_conj.con".

inline "cic:/CoRN/complex/CComplex/CC_conj_zero.con".

inline "cic:/CoRN/complex/CComplex/CC_conj_one.con".

(* UNEXPORTED
Hint Resolve CC_conj_one: algebra.
*)

inline "cic:/CoRN/complex/CComplex/CC_conj_nexp.con".

(* UNEXPORTED
End Conj_properties
*)

(* UNEXPORTED
Hint Resolve CC_conj_plus CC_conj_mult CC_conj_nexp CC_conj_conj
  CC_conj_zero: algebra.
*)

(*#* ** Properties of the real axis *)

(* UNEXPORTED
Section cc_IR_properties
*)

inline "cic:/CoRN/complex/CComplex/Re_cc_IR.con".

inline "cic:/CoRN/complex/CComplex/Im_cc_IR.con".

inline "cic:/CoRN/complex/CComplex/cc_IR_wd.con".

(* UNEXPORTED
Hint Resolve cc_IR_wd: algebra_c.
*)

inline "cic:/CoRN/complex/CComplex/cc_IR_resp_ap.con".

inline "cic:/CoRN/complex/CComplex/cc_IR_mult.con".

(* UNEXPORTED
Hint Resolve cc_IR_mult: algebra.
*)

inline "cic:/CoRN/complex/CComplex/cc_IR_mult_lft.con".

inline "cic:/CoRN/complex/CComplex/cc_IR_mult_rht.con".

inline "cic:/CoRN/complex/CComplex/cc_IR_plus.con".

(* UNEXPORTED
Hint Resolve cc_IR_plus: algebra.
*)

inline "cic:/CoRN/complex/CComplex/cc_IR_minus.con".

inline "cic:/CoRN/complex/CComplex/cc_IR_zero.con".

(* UNEXPORTED
Hint Resolve cc_IR_zero: algebra.
*)

inline "cic:/CoRN/complex/CComplex/cc_IR_one.con".

(* UNEXPORTED
Hint Resolve cc_IR_one: algebra.
*)

inline "cic:/CoRN/complex/CComplex/cc_IR_nring.con".

inline "cic:/CoRN/complex/CComplex/cc_IR_nexp.con".

(* UNEXPORTED
End cc_IR_properties
*)

(* UNEXPORTED
Hint Resolve Re_cc_IR Im_cc_IR: algebra.
*)

(* UNEXPORTED
Hint Resolve cc_IR_wd: algebra_c.
*)

(* UNEXPORTED
Hint Resolve cc_IR_mult cc_IR_nexp cc_IR_mult_lft cc_IR_mult_rht cc_IR_plus
  cc_IR_minus: algebra.
*)

(* UNEXPORTED
Hint Resolve cc_IR_nring cc_IR_zero: algebra.
*)

(*#* ** [CC] has characteristic zero *)

include "tactics/Transparent_algebra.ma".

inline "cic:/CoRN/complex/CComplex/char0_CC.con".

include "tactics/Opaque_algebra.ma".

inline "cic:/CoRN/complex/CComplex/poly_apzero_CC.con".

inline "cic:/CoRN/complex/CComplex/poly_CC_extensional.con".

