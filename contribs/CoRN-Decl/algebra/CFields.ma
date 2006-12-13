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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CFields".

include "CoRN.ma".

(* $Id: CFields.v,v 1.12 2004/04/23 10:00:52 lcf Exp $ *)

(*#* printing [/] %\ensuremath{/}% #/# *)

(*#* printing [//] %\ensuremath\ddagger% #&Dagger;# *)

(*#* printing {/} %\ensuremath{/}% #/# *)

(*#* printing {1/} %\ensuremath{\frac1\cdot}% #1/# *)

(*#* printing [/]?[//] %\ensuremath{/?\ddagger}% #/?&Dagger;# *)

include "algebra/CRings.ma".

(* UNEXPORTED
Transparent sym_eq.
*)

(* UNEXPORTED
Transparent f_equal.
*)

(* UNEXPORTED
Transparent cs_crr.
*)

(* UNEXPORTED
Transparent csg_crr.
*)

(* UNEXPORTED
Transparent cm_crr.
*)

(* UNEXPORTED
Transparent cg_crr.
*)

(* UNEXPORTED
Transparent cr_crr.
*)

(* UNEXPORTED
Transparent csf_fun.
*)

(* UNEXPORTED
Transparent csbf_fun.
*)

(* UNEXPORTED
Transparent csr_rel.
*)

(* UNEXPORTED
Transparent cs_eq.
*)

(* UNEXPORTED
Transparent cs_neq.
*)

(* UNEXPORTED
Transparent cs_ap.
*)

(* UNEXPORTED
Transparent cm_unit.
*)

(* UNEXPORTED
Transparent csg_op.
*)

(* UNEXPORTED
Transparent cg_inv.
*)

(* UNEXPORTED
Transparent cg_minus.
*)

(* UNEXPORTED
Transparent cr_one.
*)

(* UNEXPORTED
Transparent cr_mult.
*)

(* UNEXPORTED
Transparent nexp_op.
*)

(* Begin_SpecReals *)

(* FIELDS *)

(*#*
* Fields %\label{section:fields}%
** Definition of the notion Field
*)

inline "cic:/CoRN/algebra/CFields/is_CField.con".

inline "cic:/CoRN/algebra/CFields/CField.ind".

coercion cic:/matita/CoRN-Decl/algebra/CFields/cf_crr.con 0 (* compounds *).

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CFields/f_rcpcl'.con".

inline "cic:/CoRN/algebra/CFields/f_rcpcl.con".

(* UNEXPORTED
Implicit Arguments f_rcpcl [F].
*)

(*#*
[cf_div] is the division in a field. It is defined in terms of
multiplication and the reciprocal. [x[/]y] is only defined if
we have a proof of [y [#] Zero].
*)

inline "cic:/CoRN/algebra/CFields/cf_div.con".

(* UNEXPORTED
Implicit Arguments cf_div [F].
*)

(* NOTATION
Notation "x [/] y [//] Hy" := (cf_div x y Hy) (at level 80).
*)

(*#*
%\begin{convention}\label{convention:div-form}%
- Division in fields is a (type dependent) ternary function: [(cf_div x y Hy)] is denoted infix by [x [/] y [//] Hy].
- In lemmas, a hypothesis that [t [#] Zero] will be named [t_].
- We do not use [NonZeros], but write the condition [ [#] Zero] separately.
- In each lemma, we use only variables for proof objects, and these variables
 are universally quantified.
For example, the informal lemma
$\frac{1}{x}\cdot\frac{1}{y} = \frac{1}{x\cdot y}$
#(1/x).(1/y) = 1/(x.y)# for all [x] and [y]is formalized as
[[
forall (x y : F) x_ y_ xy_, (1[/]x[//]x_) [*] (1[/]y[//]y_) [=] 1[/] (x[*]y)[//]xy_
]]
and not as
[[
forall (x y : F) x_ y_, (1[/]x[//]x_) [*] (1[/]y[//]y_) [=] 1[/] (x[*]y)[//](prod_nz x y x_ y_)
]]
We have made this choice to make it easier to apply lemmas; this can
be quite awkward if we would use the last formulation.
- So every division occurring in the formulation of a lemma is of the
form [e[/]e'[//]H] where [H] is a variable.  Only exceptions: we may
write [e[/] (Snring n)] and [e[/]TwoNZ], [e[/]ThreeNZ] and so on.
(Constants like [TwoNZ] will be defined later on.)

%\end{convention}%

** Field axioms
%\begin{convention}% Let [F] be a field.
%\end{convention}%
*)

(* UNEXPORTED
Section Field_axioms
*)

alias id "F" = "cic:/CoRN/algebra/CFields/Field_axioms/F.var".

inline "cic:/CoRN/algebra/CFields/CField_is_CField.con".

inline "cic:/CoRN/algebra/CFields/rcpcl_is_inverse.con".

(* UNEXPORTED
End Field_axioms
*)

(* UNEXPORTED
Section Field_basics
*)

(*#* ** Field basics
%\begin{convention}% Let [F] be a field.
%\end{convention}%
*)

alias id "F" = "cic:/CoRN/algebra/CFields/Field_basics/F.var".

inline "cic:/CoRN/algebra/CFields/rcpcl_is_inverse_unfolded.con".

inline "cic:/CoRN/algebra/CFields/field_mult_inv.con".

(* UNEXPORTED
Hint Resolve field_mult_inv: algebra.
*)

inline "cic:/CoRN/algebra/CFields/field_mult_inv_op.con".

(* UNEXPORTED
End Field_basics
*)

(* UNEXPORTED
Hint Resolve field_mult_inv field_mult_inv_op: algebra.
*)

(* UNEXPORTED
Section Field_multiplication
*)

(*#*
** Properties of multiplication
%\begin{convention}% Let [F] be a field.
%\end{convention}%
*)

alias id "F" = "cic:/CoRN/algebra/CFields/Field_multiplication/F.var".

inline "cic:/CoRN/algebra/CFields/mult_resp_ap_zero.con".

inline "cic:/CoRN/algebra/CFields/mult_lft_resp_ap.con".

inline "cic:/CoRN/algebra/CFields/mult_rht_resp_ap.con".

inline "cic:/CoRN/algebra/CFields/mult_resp_neq_zero.con".

inline "cic:/CoRN/algebra/CFields/mult_resp_neq.con".

inline "cic:/CoRN/algebra/CFields/mult_eq_zero.con".

inline "cic:/CoRN/algebra/CFields/mult_cancel_lft.con".

inline "cic:/CoRN/algebra/CFields/mult_cancel_rht.con".

inline "cic:/CoRN/algebra/CFields/square_eq_aux.con".

inline "cic:/CoRN/algebra/CFields/square_eq_weak.con".

inline "cic:/CoRN/algebra/CFields/cond_square_eq.con".

(* UNEXPORTED
End Field_multiplication
*)

(* UNEXPORTED
Section x_square
*)

inline "cic:/CoRN/algebra/CFields/x_xminone.con".

inline "cic:/CoRN/algebra/CFields/square_id.con".

(* UNEXPORTED
End x_square
*)

(* UNEXPORTED
Hint Resolve mult_resp_ap_zero: algebra.
*)

(* UNEXPORTED
Section Rcpcl_properties
*)

(*#*
** Properties of reciprocal
%\begin{convention}% Let [F] be a field.
%\end{convention}%
*)

alias id "F" = "cic:/CoRN/algebra/CFields/Rcpcl_properties/F.var".

inline "cic:/CoRN/algebra/CFields/inv_one.con".

inline "cic:/CoRN/algebra/CFields/f_rcpcl_wd.con".

inline "cic:/CoRN/algebra/CFields/f_rcpcl_mult.con".

inline "cic:/CoRN/algebra/CFields/f_rcpcl_resp_ap_zero.con".

inline "cic:/CoRN/algebra/CFields/f_rcpcl_f_rcpcl.con".

(* UNEXPORTED
End Rcpcl_properties
*)

(* UNEXPORTED
Section MultipGroup
*)

(*#*
** The multiplicative group of nonzeros of a field.
%\begin{convention}% Let [F] be a field
%\end{convention}%
*)

alias id "F" = "cic:/CoRN/algebra/CFields/MultipGroup/F.var".

(*#*
The multiplicative monoid of NonZeros.
*)

inline "cic:/CoRN/algebra/CFields/NonZeroMonoid.con".

inline "cic:/CoRN/algebra/CFields/fmg_cs_inv.con".

inline "cic:/CoRN/algebra/CFields/plus_nonzeros_eq_mult_dom.con".

inline "cic:/CoRN/algebra/CFields/cfield_to_mult_cgroup.con".

(* UNEXPORTED
End MultipGroup
*)

(* UNEXPORTED
Section Div_properties
*)

(*#*
** Properties of division
%\begin{convention}% Let [F] be a field.
%\end{convention}%

%\begin{nameconvention}%
In the names of lemmas, we denote [[/]] by [div], and
[One[/]] by [recip].
%\end{nameconvention}%
*)

alias id "F" = "cic:/CoRN/algebra/CFields/Div_properties/F.var".

inline "cic:/CoRN/algebra/CFields/div_prop.con".

inline "cic:/CoRN/algebra/CFields/div_1.con".

inline "cic:/CoRN/algebra/CFields/div_1'.con".

inline "cic:/CoRN/algebra/CFields/div_1''.con".

(* UNEXPORTED
Hint Resolve div_1: algebra.
*)

inline "cic:/CoRN/algebra/CFields/x_div_x.con".

(* UNEXPORTED
Hint Resolve x_div_x: algebra.
*)

inline "cic:/CoRN/algebra/CFields/x_div_one.con".

(*#*
The next lemma says $x\cdot\frac{y}{z} = \frac{x\cdot y}{z}$
#x.(y/z) = (x.y)/z#.
*)

inline "cic:/CoRN/algebra/CFields/x_mult_y_div_z.con".

(* UNEXPORTED
Hint Resolve x_mult_y_div_z: algebra.
*)

inline "cic:/CoRN/algebra/CFields/div_wd.con".

(* UNEXPORTED
Hint Resolve div_wd: algebra_c.
*)

(*#*
The next lemma says $\frac{\frac{x}{y}}{z} = \frac{x}{y\cdot z}$
#[(x/y)/z = x/(y.z)]#
*)

inline "cic:/CoRN/algebra/CFields/div_div.con".

inline "cic:/CoRN/algebra/CFields/div_resp_ap_zero_rev.con".

inline "cic:/CoRN/algebra/CFields/div_resp_ap_zero.con".

(*#*
The next lemma says $\frac{x}{\frac{y}{z}} = \frac{x\cdot z}{y}$
#[x/(y/z) = (x.z)/y]#
*)

inline "cic:/CoRN/algebra/CFields/div_div2.con".

(*#*
The next lemma says $\frac{x\cdot p}{y\cdot q} = \frac{x}{y}\cdot \frac{p}{q}$
#[(x.p)/(y.q) = (x/y).(p/q)]#
*)

inline "cic:/CoRN/algebra/CFields/mult_of_divs.con".

inline "cic:/CoRN/algebra/CFields/div_dist.con".

inline "cic:/CoRN/algebra/CFields/div_dist'.con".

inline "cic:/CoRN/algebra/CFields/div_semi_sym.con".

(* UNEXPORTED
Hint Resolve div_semi_sym: algebra.
*)

inline "cic:/CoRN/algebra/CFields/eq_div.con".

inline "cic:/CoRN/algebra/CFields/div_strext.con".

(* UNEXPORTED
End Div_properties
*)

(* UNEXPORTED
Hint Resolve div_1 div_1' div_1'' div_wd x_div_x x_div_one div_div div_div2
  mult_of_divs x_mult_y_div_z mult_of_divs div_dist div_dist' div_semi_sym
  div_prop: algebra.
*)

(*#*
** Cancellation laws for apartness and multiplication
%\begin{convention}% Let [F] be a field
%\end{convention}%
*)

(* UNEXPORTED
Section Mult_Cancel_Ap_Zero
*)

alias id "F" = "cic:/CoRN/algebra/CFields/Mult_Cancel_Ap_Zero/F.var".

inline "cic:/CoRN/algebra/CFields/mult_cancel_ap_zero_lft.con".

inline "cic:/CoRN/algebra/CFields/mult_cancel_ap_zero_rht.con".

inline "cic:/CoRN/algebra/CFields/recip_ap_zero.con".

inline "cic:/CoRN/algebra/CFields/recip_resp_ap.con".

(* UNEXPORTED
End Mult_Cancel_Ap_Zero
*)

(* UNEXPORTED
Section CField_Ops
*)

(*#*
** Functional Operations

We now move on to lifting these operations to functions.  As we are
dealing with %\emph{partial}% #<i>partial</i># functions, we don't
have to worry explicitly about the function by which we are dividing
being non-zero everywhere; this will simply be encoded in its domain.

%\begin{convention}%
Let [X] be a Field and [F,G:(PartFunct X)] have domains respectively
[P] and [Q].
%\end{convention}%
*)

alias id "X" = "cic:/CoRN/algebra/CFields/CField_Ops/X.var".

alias id "F" = "cic:/CoRN/algebra/CFields/CField_Ops/F.var".

alias id "G" = "cic:/CoRN/algebra/CFields/CField_Ops/G.var".

(* begin hide *)

inline "cic:/CoRN/algebra/CFields/CField_Ops/P.con" "CField_Ops__".

inline "cic:/CoRN/algebra/CFields/CField_Ops/Q.con" "CField_Ops__".

(* end hide *)

(* UNEXPORTED
Section Part_Function_Recip
*)

(*#*
Some auxiliary notions are helpful in defining the domain.
*)

inline "cic:/CoRN/algebra/CFields/CField_Ops/Part_Function_Recip/R.con" "CField_Ops__Part_Function_Recip__".

inline "cic:/CoRN/algebra/CFields/CField_Ops/Part_Function_Recip/Ext2R.con" "CField_Ops__Part_Function_Recip__".

inline "cic:/CoRN/algebra/CFields/part_function_recip_strext.con".

inline "cic:/CoRN/algebra/CFields/part_function_recip_pred_wd.con".

inline "cic:/CoRN/algebra/CFields/Frecip.con".

(* UNEXPORTED
End Part_Function_Recip
*)

(* UNEXPORTED
Section Part_Function_Div
*)

(*#*
For division things work out almost in the same way.
*)

inline "cic:/CoRN/algebra/CFields/CField_Ops/Part_Function_Div/R.con" "CField_Ops__Part_Function_Div__".

inline "cic:/CoRN/algebra/CFields/CField_Ops/Part_Function_Div/Ext2R.con" "CField_Ops__Part_Function_Div__".

inline "cic:/CoRN/algebra/CFields/part_function_div_strext.con".

inline "cic:/CoRN/algebra/CFields/part_function_div_pred_wd.con".

inline "cic:/CoRN/algebra/CFields/Fdiv.con".

(* UNEXPORTED
End Part_Function_Div
*)

(*#*
%\begin{convention}% Let [R:X->CProp].
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/CFields/CField_Ops/R.var".

inline "cic:/CoRN/algebra/CFields/included_FRecip.con".

inline "cic:/CoRN/algebra/CFields/included_FRecip'.con".

inline "cic:/CoRN/algebra/CFields/included_FDiv.con".

inline "cic:/CoRN/algebra/CFields/included_FDiv'.con".

inline "cic:/CoRN/algebra/CFields/included_FDiv''.con".

(* UNEXPORTED
End CField_Ops
*)

(* UNEXPORTED
Implicit Arguments Frecip [X].
*)

(* NOTATION
Notation "{1/} x" := (Frecip x) (at level 2, right associativity).
*)

(* UNEXPORTED
Implicit Arguments Fdiv [X].
*)

(* NOTATION
Infix "{/}" := Fdiv (at level 41, no associativity).
*)

(* UNEXPORTED
Hint Resolve included_FRecip included_FDiv : included.
*)

(* UNEXPORTED
Hint Immediate included_FRecip' included_FDiv' included_FDiv'' : included.
*)

