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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/MoreIntegrals".

include "CoRN.ma".

(* $Id: MoreIntegrals.v,v 1.6 2004/04/23 10:00:59 lcf Exp $ *)

include "ftc/Integral.ma".

include "ftc/MoreFunctions.ma".

(* UNEXPORTED
Section Lemmas.
*)

(*#* printing Integral %\ensuremath{\int}% #&int;# *)

(*#* printing integral' %\ensuremath{\int}% #&int;# *)

(*#* *The generalized integral

In this file we extend the definition of integral to allow for
arbitrary integration domains (that is, not requiring that the lower
endpoint of integration be less or equal than the upper endpoint) and
we prove the fundamental properties of the new operator.

%\begin{convention}% Let [a, b : IR] and assume that [F] and [G] are two 
partial functions continuous in [[Min(a,b),Max(a,b)]].
%\end{convention}%

** Definitions

Before we define the new integral we need to some trivial interval inclusions.
*)

inline "cic:/CoRN/ftc/MoreIntegrals/a.var".

inline "cic:/CoRN/ftc/MoreIntegrals/b.var".

inline "cic:/CoRN/ftc/MoreIntegrals/Hab.var".

inline "cic:/CoRN/ftc/MoreIntegrals/compact_inc_Min_lft.con".

inline "cic:/CoRN/ftc/MoreIntegrals/compact_inc_Min_rht.con".

(* UNEXPORTED
End Lemmas.
*)

(* UNEXPORTED
Section Definitions.
*)

(*#*
The integral is defined by the formula
$\int_a^bf=\int_{\min(a,b)}^bf-\int_{\min(a,b)}^af$#&int;<sub>a</sub><sup>b</sup>f=&int;<sub>min(a,b)</sub><sup>b</sup>f-&int;<sub>min(a,b)</sub><sup>a</sup>f#,
inspired by the domain union rule; obviously it coincides with the
classical definition, and it collapses to the old one in the case [a
 [<=]  b].
*)

inline "cic:/CoRN/ftc/MoreIntegrals/a.var".

inline "cic:/CoRN/ftc/MoreIntegrals/b.var".

inline "cic:/CoRN/ftc/MoreIntegrals/Hab.var".

inline "cic:/CoRN/ftc/MoreIntegrals/F.var".

inline "cic:/CoRN/ftc/MoreIntegrals/HF.var".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_inc1.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_inc2.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_integral.con".

(* UNEXPORTED
End Definitions.
*)

(* UNEXPORTED
Implicit Arguments Integral [a b Hab F].
*)

(* UNEXPORTED
Section Properties_of_Integral.
*)

(*#* **Properties of the Integral

All our old properties carry over to this new definition---and some
new ones, too.  We begin with (strong) extensionality.
*)

inline "cic:/CoRN/ftc/MoreIntegrals/a.var".

inline "cic:/CoRN/ftc/MoreIntegrals/b.var".

inline "cic:/CoRN/ftc/MoreIntegrals/Hab.var".

inline "cic:/CoRN/ftc/MoreIntegrals/F.var".

inline "cic:/CoRN/ftc/MoreIntegrals/G.var".

inline "cic:/CoRN/ftc/MoreIntegrals/contF.var".

inline "cic:/CoRN/ftc/MoreIntegrals/contG.var".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_strext.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_strext'.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_wd.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_wd'.con".

(*#*
The integral is a linear operator.
*)

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_const.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_comm_scal.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_plus.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_inv.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_minus.con".

inline "cic:/CoRN/ftc/MoreIntegrals/linear_Integral.con".

(*#*
If the endpoints are equal then the integral vanishes.
*)

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_empty.con".

(*#*
And the norm provides an upper bound for the absolute value of the integral.
*)

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_leEq_norm.con".

(* UNEXPORTED
End Properties_of_Integral.
*)

(* UNEXPORTED
Section More_Properties.
*)

(*#*
Two other ways of stating the addition law for domains.
*)

inline "cic:/CoRN/ftc/MoreIntegrals/integral_plus_Integral.con".

inline "cic:/CoRN/ftc/MoreIntegrals/integral_plus_integral'.con".

(*#*
And now we can prove the addition law for domains with our general operator.

%\begin{convention}% Assume [c : IR].
%\end{convention}%
*)

inline "cic:/CoRN/ftc/MoreIntegrals/a.var".

inline "cic:/CoRN/ftc/MoreIntegrals/b.var".

inline "cic:/CoRN/ftc/MoreIntegrals/c.var".

(* begin show *)

inline "cic:/CoRN/ftc/MoreIntegrals/Hab'.var".

inline "cic:/CoRN/ftc/MoreIntegrals/Hac'.var".

inline "cic:/CoRN/ftc/MoreIntegrals/Hcb'.var".

inline "cic:/CoRN/ftc/MoreIntegrals/Habc'.var".

(* end show *)

inline "cic:/CoRN/ftc/MoreIntegrals/F.var".

(* begin show *)

inline "cic:/CoRN/ftc/MoreIntegrals/Hab.var".

inline "cic:/CoRN/ftc/MoreIntegrals/Hac.var".

inline "cic:/CoRN/ftc/MoreIntegrals/Hcb.var".

inline "cic:/CoRN/ftc/MoreIntegrals/Habc.var".

(* end show *)

(* begin hide *)

inline "cic:/CoRN/ftc/MoreIntegrals/le_abc_ab.con".

inline "cic:/CoRN/ftc/MoreIntegrals/le_abc_ac.con".

inline "cic:/CoRN/ftc/MoreIntegrals/le_abc_cb.con".

inline "cic:/CoRN/ftc/MoreIntegrals/le_abc_a.con".

inline "cic:/CoRN/ftc/MoreIntegrals/le_abc_b.con".

inline "cic:/CoRN/ftc/MoreIntegrals/le_abc_c.con".

inline "cic:/CoRN/ftc/MoreIntegrals/le_ab_a.con".

inline "cic:/CoRN/ftc/MoreIntegrals/le_cb_c.con".

inline "cic:/CoRN/ftc/MoreIntegrals/le_ac_a.con".

inline "cic:/CoRN/ftc/MoreIntegrals/le_ab_b.con".

inline "cic:/CoRN/ftc/MoreIntegrals/le_cb_b.con".

inline "cic:/CoRN/ftc/MoreIntegrals/le_ac_c.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Habc_abc.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Habc_ab.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Habc_ac.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Habc_cb.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Habc_a.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Habc_b.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Habc_c.con".

(* end hide *)

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_plus_Integral.con".

(*#*
Notice that, unlike in the classical case, an extra hypothesis (the
continuity of [F] in the interval [[Min(a,b,c),Max(a,b,c)]]) must be assumed.
*)

(* UNEXPORTED
End More_Properties.
*)

(* UNEXPORTED
Section Corollaries.
*)

inline "cic:/CoRN/ftc/MoreIntegrals/a.var".

inline "cic:/CoRN/ftc/MoreIntegrals/b.var".

inline "cic:/CoRN/ftc/MoreIntegrals/Hab.var".

inline "cic:/CoRN/ftc/MoreIntegrals/F.var".

inline "cic:/CoRN/ftc/MoreIntegrals/contF.var".

(*#* As a corollary, we get the following rule: *)

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_op.con".

(*#* Finally, some miscellaneous results: *)

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_less_norm.con".

inline "cic:/CoRN/ftc/MoreIntegrals/ub_Integral.con".

(* UNEXPORTED
End Corollaries.
*)

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_ap_zero.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_eq_zero.con".

