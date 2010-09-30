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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CAbMonoids".

include "CoRN.ma".

include "algebra/CMonoids.ma".

(* UNEXPORTED
Section Abelian_Monoids
*)

(*#*
* Abelian Monoids
Now we introduce commutativity and add some results.
*)

inline "cic:/CoRN/algebra/CAbMonoids/is_CAbMonoid.con".

inline "cic:/CoRN/algebra/CAbMonoids/CAbMonoid.ind".

coercion cic:/matita/CoRN-Decl/algebra/CAbMonoids/cam_crr.con 0 (* compounds *).

(* UNEXPORTED
Section AbMonoid_Axioms
*)

alias id "M" = "cic:/CoRN/algebra/CAbMonoids/Abelian_Monoids/AbMonoid_Axioms/M.var".

(*#*
%\begin{convention}% Let [M] be an abelian monoid.
%\end{convention}%
*)

inline "cic:/CoRN/algebra/CAbMonoids/CAbMonoid_is_CAbMonoid.con".

inline "cic:/CoRN/algebra/CAbMonoids/cam_commutes.con".

inline "cic:/CoRN/algebra/CAbMonoids/cam_commutes_unfolded.con".

(* UNEXPORTED
End AbMonoid_Axioms
*)

(* UNEXPORTED
Section SubCAbMonoids
*)

(*#*
** Subgroups of an Abelian Monoid
*)

alias id "M" = "cic:/CoRN/algebra/CAbMonoids/Abelian_Monoids/SubCAbMonoids/M.var".

alias id "P" = "cic:/CoRN/algebra/CAbMonoids/Abelian_Monoids/SubCAbMonoids/P.var".

alias id "Punit" = "cic:/CoRN/algebra/CAbMonoids/Abelian_Monoids/SubCAbMonoids/Punit.var".

alias id "op_pres_P" = "cic:/CoRN/algebra/CAbMonoids/Abelian_Monoids/SubCAbMonoids/op_pres_P.var".

(*#*
%\begin{convention}%
Let [M] be an Abelian Monoid and [P] be a ([CProp]-valued) predicate on [M]
that contains [Zero] and is closed under [[+]] and [[--]].
%\end{convention}%
*)

inline "cic:/CoRN/algebra/CAbMonoids/Abelian_Monoids/SubCAbMonoids/subcrr.con" "Abelian_Monoids__SubCAbMonoids__".

inline "cic:/CoRN/algebra/CAbMonoids/isabgrp_scrr.con".

inline "cic:/CoRN/algebra/CAbMonoids/Build_SubCAbMonoid.con".

(* UNEXPORTED
End SubCAbMonoids
*)

(* UNEXPORTED
End Abelian_Monoids
*)

(* UNEXPORTED
Hint Resolve cam_commutes_unfolded: algebra.
*)

