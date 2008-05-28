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
Section Lemmas
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

alias id "a" = "cic:/CoRN/ftc/MoreIntegrals/Lemmas/a.var".

alias id "b" = "cic:/CoRN/ftc/MoreIntegrals/Lemmas/b.var".

alias id "Hab" = "cic:/CoRN/ftc/MoreIntegrals/Lemmas/Hab.var".

inline "cic:/CoRN/ftc/MoreIntegrals/compact_inc_Min_lft.con".

inline "cic:/CoRN/ftc/MoreIntegrals/compact_inc_Min_rht.con".

(* UNEXPORTED
End Lemmas
*)

(* UNEXPORTED
Section Definitions
*)

(*#*
The integral is defined by the formula
$\int_a^bf=\int_{\min(a,b)}^bf-\int_{\min(a,b)}^af$#&int;<sub>a</sub><sup>b</sup>f=&int;<sub>min(a,b)</sub><sup>b</sup>f-&int;<sub>min(a,b)</sub><sup>a</sup>f#,
inspired by the domain union rule; obviously it coincides with the
classical definition, and it collapses to the old one in the case [a
 [<=]  b].
*)

alias id "a" = "cic:/CoRN/ftc/MoreIntegrals/Definitions/a.var".

alias id "b" = "cic:/CoRN/ftc/MoreIntegrals/Definitions/b.var".

alias id "Hab" = "cic:/CoRN/ftc/MoreIntegrals/Definitions/Hab.var".

alias id "F" = "cic:/CoRN/ftc/MoreIntegrals/Definitions/F.var".

alias id "HF" = "cic:/CoRN/ftc/MoreIntegrals/Definitions/HF.var".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_inc1.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_inc2.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_integral.con".

(* UNEXPORTED
End Definitions
*)

(* UNEXPORTED
Implicit Arguments Integral [a b Hab F].
*)

(* UNEXPORTED
Section Properties_of_Integral
*)

(*#* **Properties of the Integral

All our old properties carry over to this new definition---and some
new ones, too.  We begin with (strong) extensionality.
*)

alias id "a" = "cic:/CoRN/ftc/MoreIntegrals/Properties_of_Integral/a.var".

alias id "b" = "cic:/CoRN/ftc/MoreIntegrals/Properties_of_Integral/b.var".

alias id "Hab" = "cic:/CoRN/ftc/MoreIntegrals/Properties_of_Integral/Hab.var".

alias id "F" = "cic:/CoRN/ftc/MoreIntegrals/Properties_of_Integral/F.var".

alias id "G" = "cic:/CoRN/ftc/MoreIntegrals/Properties_of_Integral/G.var".

alias id "contF" = "cic:/CoRN/ftc/MoreIntegrals/Properties_of_Integral/contF.var".

alias id "contG" = "cic:/CoRN/ftc/MoreIntegrals/Properties_of_Integral/contG.var".

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
End Properties_of_Integral
*)

(* UNEXPORTED
Section More_Properties
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

alias id "a" = "cic:/CoRN/ftc/MoreIntegrals/More_Properties/a.var".

alias id "b" = "cic:/CoRN/ftc/MoreIntegrals/More_Properties/b.var".

alias id "c" = "cic:/CoRN/ftc/MoreIntegrals/More_Properties/c.var".

(* begin show *)

alias id "Hab'" = "cic:/CoRN/ftc/MoreIntegrals/More_Properties/Hab'.var".

alias id "Hac'" = "cic:/CoRN/ftc/MoreIntegrals/More_Properties/Hac'.var".

alias id "Hcb'" = "cic:/CoRN/ftc/MoreIntegrals/More_Properties/Hcb'.var".

alias id "Habc'" = "cic:/CoRN/ftc/MoreIntegrals/More_Properties/Habc'.var".

(* end show *)

alias id "F" = "cic:/CoRN/ftc/MoreIntegrals/More_Properties/F.var".

(* begin show *)

alias id "Hab" = "cic:/CoRN/ftc/MoreIntegrals/More_Properties/Hab.var".

alias id "Hac" = "cic:/CoRN/ftc/MoreIntegrals/More_Properties/Hac.var".

alias id "Hcb" = "cic:/CoRN/ftc/MoreIntegrals/More_Properties/Hcb.var".

alias id "Habc" = "cic:/CoRN/ftc/MoreIntegrals/More_Properties/Habc.var".

(* end show *)

(* begin hide *)

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/le_abc_ab.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/le_abc_ac.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/le_abc_cb.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/le_abc_a.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/le_abc_b.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/le_abc_c.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/le_ab_a.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/le_cb_c.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/le_ac_a.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/le_ab_b.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/le_cb_b.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/le_ac_c.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/Habc_abc.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/Habc_ab.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/Habc_ac.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/Habc_cb.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/Habc_a.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/Habc_b.con" "More_Properties__".

inline "cic:/CoRN/ftc/MoreIntegrals/More_Properties/Habc_c.con" "More_Properties__".

(* end hide *)

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_plus_Integral.con".

(*#*
Notice that, unlike in the classical case, an extra hypothesis (the
continuity of [F] in the interval [[Min(a,b,c),Max(a,b,c)]]) must be assumed.
*)

(* UNEXPORTED
End More_Properties
*)

(* UNEXPORTED
Section Corollaries
*)

alias id "a" = "cic:/CoRN/ftc/MoreIntegrals/Corollaries/a.var".

alias id "b" = "cic:/CoRN/ftc/MoreIntegrals/Corollaries/b.var".

alias id "Hab" = "cic:/CoRN/ftc/MoreIntegrals/Corollaries/Hab.var".

alias id "F" = "cic:/CoRN/ftc/MoreIntegrals/Corollaries/F.var".

alias id "contF" = "cic:/CoRN/ftc/MoreIntegrals/Corollaries/contF.var".

(*#* As a corollary, we get the following rule: *)

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_op.con".

(*#* Finally, some miscellaneous results: *)

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_less_norm.con".

inline "cic:/CoRN/ftc/MoreIntegrals/ub_Integral.con".

(* UNEXPORTED
End Corollaries
*)

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_ap_zero.con".

inline "cic:/CoRN/ftc/MoreIntegrals/Integral_eq_zero.con".

