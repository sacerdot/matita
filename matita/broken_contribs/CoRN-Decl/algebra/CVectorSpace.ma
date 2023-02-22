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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CVectorSpace".

include "CoRN.ma".

(* $Id: CVectorSpace.v,v 1.4 2004/04/23 10:00:54 lcf Exp $ *)

(*#* printing ['] %{'}% #'# *)

include "algebra/CFields.ma".

(*#*
* Vector Spaces

Obsolete but maintained.
*)

(* begin hide *)

(* UNEXPORTED
Set Implicit Arguments.
*)

(* UNEXPORTED
Unset Strict Implicit.
*)

(* end hide *)

inline "cic:/CoRN/algebra/CVectorSpace/VSpace.ind".

coercion cic:/matita/CoRN-Decl/algebra/CVectorSpace/vs_vs.con 0 (* compounds *).

(* begin hide *)

(* UNEXPORTED
Set Strict Implicit.
*)

(* UNEXPORTED
Unset Implicit Arguments.
*)

(* end hide *)

(* UNEXPORTED
Hint Resolve vs_assoc vs_unit vs_distl vs_distr: algebra.
*)

(* UNEXPORTED
Implicit Arguments vs_op [F v].
*)

(* NOTATION
Infix "[']" := vs_op (at level 30, no associativity).
*)

(*#*
%\begin{convention}%
Let [F] be a fiels and let [V] be a vector space over [F]
%\end{convention}%
*)

(* UNEXPORTED
Section VS_basics
*)

alias id "F" = "cic:/CoRN/algebra/CVectorSpace/VS_basics/F.var".

alias id "V" = "cic:/CoRN/algebra/CVectorSpace/VS_basics/V.var".

inline "cic:/CoRN/algebra/CVectorSpace/vs_op_zero.con".

inline "cic:/CoRN/algebra/CVectorSpace/zero_vs_op.con".

(* UNEXPORTED
Hint Resolve vs_op_zero zero_vs_op: algebra.
*)

inline "cic:/CoRN/algebra/CVectorSpace/vs_op_inv_V.con".

inline "cic:/CoRN/algebra/CVectorSpace/vs_op_inv_S.con".

(* UNEXPORTED
Hint Resolve vs_op_inv_V vs_op_inv_S: algebra.
*)

inline "cic:/CoRN/algebra/CVectorSpace/vs_inv_assoc.con".

(* UNEXPORTED
Hint Resolve vs_inv_assoc: algebra.
*)

inline "cic:/CoRN/algebra/CVectorSpace/ap_zero_vs_op_l.con".

inline "cic:/CoRN/algebra/CVectorSpace/ap_zero_vs_op_r.con".

(* note this is the same proof as mult_resp_ap_zero *)

inline "cic:/CoRN/algebra/CVectorSpace/vs_op_resp_ap_rht.con".

inline "cic:/CoRN/algebra/CVectorSpace/vs_op_resp_ap_zero.con".

inline "cic:/CoRN/algebra/CVectorSpace/vs_op_resp_ap_lft.con".

(* UNEXPORTED
End VS_basics
*)

(* UNEXPORTED
Hint Resolve vs_op_zero zero_vs_op: algebra.
*)

