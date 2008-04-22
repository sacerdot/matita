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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CMonoids".

include "CoRN.ma".

(* $Id: CMonoids.v,v 1.3 2004/04/07 15:07:57 lcf Exp $ *)

(*#* printing Zero %\ensuremath{\mathbf0}% #0# *)

include "algebra/CSemiGroups.ma".

(* Begin_SpecReals *)

(*#*
* Monoids %\label{section:monoids}%
** Definition of monoids
*)

inline "cic:/CoRN/algebra/CMonoids/is_rht_unit.con".

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CMonoids/is_lft_unit.con".

(* UNEXPORTED
Implicit Arguments is_lft_unit [S].
*)

(* Begin_SpecReals *)

(* UNEXPORTED
Implicit Arguments is_rht_unit [S].
*)

inline "cic:/CoRN/algebra/CMonoids/is_CMonoid.ind".

inline "cic:/CoRN/algebra/CMonoids/CMonoid.ind".

coercion cic:/matita/CoRN-Decl/algebra/CMonoids/cm_crr.con 0 (* compounds *).

(*#*
%\begin{nameconvention}%
In the names of lemmas, we will denote [Zero] with [zero].
We denote [ [#] Zero] in the names of lemmas by [ap_zero]
(and not, e.g.%\% [nonzero]).
%\end{nameconvention}%
*)

(* Begin_SpecReals *)

(*#*
The predicate "non-zero" is defined.
In lemmas we will continue to write [x [#] Zero], rather than
[(nonZeroP x)], but the predicate is useful for some high-level definitions,
e.g. for the setoid of non-zeros.
*)

(* NOTATION
Notation Zero := (cm_unit _).
*)

inline "cic:/CoRN/algebra/CMonoids/nonZeroP.con".

(* End_SpecReals *)

(* UNEXPORTED
Implicit Arguments nonZeroP [M].
*)

(*#*
** Monoid axioms
%\begin{convention}% Let [M] be a monoid.
%\end{convention}%
*)

(* UNEXPORTED
Section CMonoid_axioms
*)

alias id "M" = "cic:/CoRN/algebra/CMonoids/CMonoid_axioms/M.var".

inline "cic:/CoRN/algebra/CMonoids/CMonoid_is_CMonoid.con".

inline "cic:/CoRN/algebra/CMonoids/cm_rht_unit.con".

inline "cic:/CoRN/algebra/CMonoids/cm_lft_unit.con".

(* UNEXPORTED
End CMonoid_axioms
*)

(*#*
** Monoid basics
%\begin{convention}% Let [M] be a monoid.
%\end{convention}%
*)

(* UNEXPORTED
Section CMonoid_basics
*)

alias id "M" = "cic:/CoRN/algebra/CMonoids/CMonoid_basics/M.var".

inline "cic:/CoRN/algebra/CMonoids/cm_rht_unit_unfolded.con".

inline "cic:/CoRN/algebra/CMonoids/cm_lft_unit_unfolded.con".

(* UNEXPORTED
Hint Resolve cm_rht_unit_unfolded cm_lft_unit_unfolded: algebra.
*)

inline "cic:/CoRN/algebra/CMonoids/cm_unit_unique_lft.con".

inline "cic:/CoRN/algebra/CMonoids/cm_unit_unique_rht.con".

(* Begin_SpecReals *)

(*#*
The proof component of the monoid is irrelevant.
*)

inline "cic:/CoRN/algebra/CMonoids/is_CMonoid_proof_irr.con".

(* End_SpecReals *)

(*#*
** Submonoids
%\begin{convention}%
Let [P] a predicate on [M] containing [Zero] and closed under [[+]].
%\end{convention}%
*)

(* UNEXPORTED
Section SubCMonoids
*)

alias id "P" = "cic:/CoRN/algebra/CMonoids/CMonoid_basics/SubCMonoids/P.var".

alias id "Punit" = "cic:/CoRN/algebra/CMonoids/CMonoid_basics/SubCMonoids/Punit.var".

alias id "op_pres_P" = "cic:/CoRN/algebra/CMonoids/CMonoid_basics/SubCMonoids/op_pres_P.var".

inline "cic:/CoRN/algebra/CMonoids/CMonoid_basics/SubCMonoids/subcrr.con" "CMonoid_basics__SubCMonoids__".

inline "cic:/CoRN/algebra/CMonoids/ismon_scrr.con".

inline "cic:/CoRN/algebra/CMonoids/Build_SubCMonoid.con".

(* UNEXPORTED
End SubCMonoids
*)

(* UNEXPORTED
End CMonoid_basics
*)

(* UNEXPORTED
Hint Resolve cm_rht_unit_unfolded cm_lft_unit_unfolded: algebra.
*)

