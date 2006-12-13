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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CGroups".

include "CoRN.ma".

(* $Id: CGroups.v,v 1.9 2004/04/23 10:00:52 lcf Exp $ *)

(*#* printing [-] %\ensuremath-% #&minus;# *)

(*#* printing [--] %\ensuremath-% #&minus;# *)

(*#* printing {-} %\ensuremath-% #&minus;# *)

(*#* printing {--} %\ensuremath-% #&minus;# *)

include "algebra/CMonoids.ma".

(* Begin_SpecReals *)

(*#*
* Groups
** Definition of the notion of Group
*)

inline "cic:/CoRN/algebra/CGroups/is_inverse.con".

(* UNEXPORTED
Implicit Arguments is_inverse [S].
*)

inline "cic:/CoRN/algebra/CGroups/is_CGroup.con".

inline "cic:/CoRN/algebra/CGroups/CGroup.ind".

coercion cic:/matita/CoRN-Decl/algebra/CGroups/cg_crr.con 0 (* compounds *).

(* End_SpecReals *)

(* Begin_SpecReals *)

(* UNEXPORTED
Implicit Arguments cg_inv [c].
*)

(* NOTATION
Notation "[--] x" := (cg_inv x) (at level 2, right associativity).
*)

inline "cic:/CoRN/algebra/CGroups/cg_minus.con".

(*#*
%\begin{nameconvention}%
In the names of lemmas, we will denote [[--] ] with [inv],
and [ [-] ] with [minus].
%\end{nameconvention}%
*)

(* UNEXPORTED
Implicit Arguments cg_minus [G].
*)

(* NOTATION
Infix "[-]" := cg_minus (at level 50, left associativity).
*)

(* End_SpecReals *)

(*#*
** Group axioms
%\begin{convention}% Let [G] be a group.
%\end{convention}%
*)

(* UNEXPORTED
Section CGroup_axioms
*)

alias id "G" = "cic:/CoRN/algebra/CGroups/CGroup_axioms/G.var".

inline "cic:/CoRN/algebra/CGroups/cg_inverse.con".

(* UNEXPORTED
End CGroup_axioms
*)

(*#*
** Group basics
General properties of groups.
%\begin{convention}% Let [G] be a group.
%\end{convention}%
*)

(* UNEXPORTED
Section CGroup_basics
*)

alias id "G" = "cic:/CoRN/algebra/CGroups/CGroup_basics/G.var".

inline "cic:/CoRN/algebra/CGroups/cg_rht_inv_unfolded.con".

inline "cic:/CoRN/algebra/CGroups/cg_lft_inv_unfolded.con".

inline "cic:/CoRN/algebra/CGroups/cg_minus_correct.con".

(* UNEXPORTED
Hint Resolve cg_rht_inv_unfolded cg_lft_inv_unfolded cg_minus_correct:
  algebra.
*)

inline "cic:/CoRN/algebra/CGroups/cg_inverse'.con".

(* Hints for Auto *)

inline "cic:/CoRN/algebra/CGroups/cg_minus_unfolded.con".

(* UNEXPORTED
Hint Resolve cg_minus_unfolded: algebra.
*)

inline "cic:/CoRN/algebra/CGroups/cg_minus_wd.con".

(* UNEXPORTED
Hint Resolve cg_minus_wd: algebra_c.
*)

inline "cic:/CoRN/algebra/CGroups/cg_minus_strext.con".

inline "cic:/CoRN/algebra/CGroups/cg_minus_is_csetoid_bin_op.con".

inline "cic:/CoRN/algebra/CGroups/grp_inv_assoc.con".

(* UNEXPORTED
Hint Resolve grp_inv_assoc: algebra.
*)

inline "cic:/CoRN/algebra/CGroups/cg_inv_unique.con".

inline "cic:/CoRN/algebra/CGroups/cg_inv_inv.con".

(* UNEXPORTED
Hint Resolve cg_inv_inv: algebra.
*)

inline "cic:/CoRN/algebra/CGroups/cg_cancel_lft.con".

inline "cic:/CoRN/algebra/CGroups/cg_cancel_rht.con".

inline "cic:/CoRN/algebra/CGroups/cg_inv_unique'.con".

inline "cic:/CoRN/algebra/CGroups/cg_inv_unique_2.con".

inline "cic:/CoRN/algebra/CGroups/cg_zero_inv.con".

(* UNEXPORTED
Hint Resolve cg_zero_inv: algebra.
*)

inline "cic:/CoRN/algebra/CGroups/cg_inv_zero.con".

inline "cic:/CoRN/algebra/CGroups/cg_inv_op.con".

(*#*
Useful for interactive proof development.
*)

inline "cic:/CoRN/algebra/CGroups/x_minus_x.con".

(*#*
** Sub-groups
%\begin{convention}% Let [P] be a predicate on [G] containing
[Zero] and closed under [[+]] and [[--] ].
%\end{convention}%
*)

(* UNEXPORTED
Section SubCGroups
*)

alias id "P" = "cic:/CoRN/algebra/CGroups/CGroup_basics/SubCGroups/P.var".

alias id "Punit" = "cic:/CoRN/algebra/CGroups/CGroup_basics/SubCGroups/Punit.var".

alias id "op_pres_P" = "cic:/CoRN/algebra/CGroups/CGroup_basics/SubCGroups/op_pres_P.var".

alias id "inv_pres_P" = "cic:/CoRN/algebra/CGroups/CGroup_basics/SubCGroups/inv_pres_P.var".

inline "cic:/CoRN/algebra/CGroups/CGroup_basics/SubCGroups/subcrr.con" "CGroup_basics__SubCGroups__".

inline "cic:/CoRN/algebra/CGroups/CGroup_basics/SubCGroups/subinv.con" "CGroup_basics__SubCGroups__".

inline "cic:/CoRN/algebra/CGroups/isgrp_scrr.con".

inline "cic:/CoRN/algebra/CGroups/Build_SubCGroup.con".

(* UNEXPORTED
End SubCGroups
*)

(* UNEXPORTED
End CGroup_basics
*)

(* UNEXPORTED
Hint Resolve cg_rht_inv_unfolded cg_lft_inv_unfolded: algebra.
*)

(* UNEXPORTED
Hint Resolve cg_inv_inv cg_minus_correct cg_zero_inv cg_inv_zero: algebra.
*)

(* UNEXPORTED
Hint Resolve cg_minus_unfolded grp_inv_assoc cg_inv_op: algebra.
*)

(* UNEXPORTED
Hint Resolve cg_minus_wd: algebra_c.
*)

(*#*
** Associative properties of groups
%\begin{convention}% Let [G] be a group.
%\end{convention}%
*)

(* UNEXPORTED
Section Assoc_properties
*)

alias id "G" = "cic:/CoRN/algebra/CGroups/Assoc_properties/G.var".

inline "cic:/CoRN/algebra/CGroups/assoc_2.con".

inline "cic:/CoRN/algebra/CGroups/zero_minus.con".

inline "cic:/CoRN/algebra/CGroups/cg_cancel_mixed.con".

inline "cic:/CoRN/algebra/CGroups/plus_resp_eq.con".

(* UNEXPORTED
End Assoc_properties
*)

(* UNEXPORTED
Hint Resolve assoc_2 minus_plus zero_minus cg_cancel_mixed plus_resp_eq:
  algebra.
*)

(*#*
** Apartness in Constructive Groups
Specific properties of apartness.
%\begin{convention}% Let [G] be a group.
%\end{convention}%
*)

(* UNEXPORTED
Section cgroups_apartness
*)

alias id "G" = "cic:/CoRN/algebra/CGroups/cgroups_apartness/G.var".

inline "cic:/CoRN/algebra/CGroups/cg_add_ap_zero.con".

inline "cic:/CoRN/algebra/CGroups/op_rht_resp_ap.con".

inline "cic:/CoRN/algebra/CGroups/cg_ap_cancel_rht.con".

inline "cic:/CoRN/algebra/CGroups/plus_cancel_ap_rht.con".

inline "cic:/CoRN/algebra/CGroups/minus_ap_zero.con".

inline "cic:/CoRN/algebra/CGroups/zero_minus_apart.con".

inline "cic:/CoRN/algebra/CGroups/inv_resp_ap_zero.con".

inline "cic:/CoRN/algebra/CGroups/inv_resp_ap.con".

inline "cic:/CoRN/algebra/CGroups/minus_resp_ap_rht.con".

inline "cic:/CoRN/algebra/CGroups/minus_resp_ap_lft.con".

inline "cic:/CoRN/algebra/CGroups/minus_cancel_ap_rht.con".

(* UNEXPORTED
End cgroups_apartness
*)

(* UNEXPORTED
Hint Resolve op_rht_resp_ap: algebra.
*)

(* UNEXPORTED
Hint Resolve minus_ap_zero zero_minus_apart inv_resp_ap_zero: algebra.
*)

(* UNEXPORTED
Section CGroup_Ops
*)

(*#*
** Functional operations

As before, we lift our group operations to the function space of the group.

%\begin{convention}%
Let [G] be a group and [F,F':(PartFunct G)] with domains given respectively
by [P] and [Q].
%\end{convention}%
*)

alias id "G" = "cic:/CoRN/algebra/CGroups/CGroup_Ops/G.var".

alias id "F" = "cic:/CoRN/algebra/CGroups/CGroup_Ops/F.var".

alias id "F'" = "cic:/CoRN/algebra/CGroups/CGroup_Ops/F'.var".

(* begin hide *)

inline "cic:/CoRN/algebra/CGroups/CGroup_Ops/P.con" "CGroup_Ops__".

inline "cic:/CoRN/algebra/CGroups/CGroup_Ops/Q.con" "CGroup_Ops__".

(* end hide *)

(* UNEXPORTED
Section Part_Function_Inv
*)

inline "cic:/CoRN/algebra/CGroups/part_function_inv_strext.con".

inline "cic:/CoRN/algebra/CGroups/Finv.con".

(* UNEXPORTED
End Part_Function_Inv
*)

(* UNEXPORTED
Section Part_Function_Minus
*)

inline "cic:/CoRN/algebra/CGroups/part_function_minus_strext.con".

inline "cic:/CoRN/algebra/CGroups/Fminus.con".

(* UNEXPORTED
End Part_Function_Minus
*)

(*#*
%\begin{convention}% Let [R:G->CProp].
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/CGroups/CGroup_Ops/R.var".

inline "cic:/CoRN/algebra/CGroups/included_FInv.con".

inline "cic:/CoRN/algebra/CGroups/included_FInv'.con".

inline "cic:/CoRN/algebra/CGroups/included_FMinus.con".

inline "cic:/CoRN/algebra/CGroups/included_FMinus'.con".

inline "cic:/CoRN/algebra/CGroups/included_FMinus''.con".

(* UNEXPORTED
End CGroup_Ops
*)

(* UNEXPORTED
Implicit Arguments Finv [G].
*)

(* NOTATION
Notation "{--} x" := (Finv x) (at level 2, right associativity).
*)

(* UNEXPORTED
Implicit Arguments Fminus [G].
*)

(* NOTATION
Infix "{-}" := Fminus (at level 50, left associativity).
*)

(* UNEXPORTED
Hint Resolve included_FInv included_FMinus : included.
*)

(* UNEXPORTED
Hint Immediate included_FInv' included_FMinus' included_FMinus'' : included.
*)

