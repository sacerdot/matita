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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CSemiGroups".

include "CoRN.ma".

(* $Id: CSemiGroups.v,v 1.8 2004/04/22 14:49:43 lcf Exp $ *)

(*#* printing [+] %\ensuremath+% #+# *)

(*#* printing {+} %\ensuremath+% #+# *)

include "algebra/CSetoidInc.ma".

(* Begin_SpecReals *)

(*#* *Semigroups

**Definition of the notion of semigroup
*)

inline "cic:/CoRN/algebra/CSemiGroups/is_CSemiGroup.con".

inline "cic:/CoRN/algebra/CSemiGroups/CSemiGroup.ind".

coercion cic:/matita/CoRN-Decl/algebra/CSemiGroups/csg_crr.con 0 (* compounds *).

(*#*
%\begin{nameconvention}%
In the %{\em %names%}% of lemmas, we will denote [[+]] with [plus].
%\end{nameconvention}%
*)

(* UNEXPORTED
Implicit Arguments csg_op [c].
*)

(* NOTATION
Infix "[+]" := csg_op (at level 50, left associativity).
*)

(* End_SpecReals *)

(*#* **Semigroup axioms
The axiomatic properties of a semi group.

%\begin{convention}% Let [G] be a semi-group.
%\end{convention}%
*)

(* UNEXPORTED
Section CSemiGroup_axioms
*)

alias id "G" = "cic:/CoRN/algebra/CSemiGroups/CSemiGroup_axioms/G.var".

inline "cic:/CoRN/algebra/CSemiGroups/CSemiGroup_is_CSemiGroup.con".

inline "cic:/CoRN/algebra/CSemiGroups/plus_assoc.con".

(* UNEXPORTED
End CSemiGroup_axioms
*)

(* Begin_SpecReals *)

(*#* **Semigroup basics

%\begin{convention}%
Let [G] be a semi-group.
%\end{convention}%
*)

(* UNEXPORTED
Section CSemiGroup_basics
*)

alias id "G" = "cic:/CoRN/algebra/CSemiGroups/CSemiGroup_basics/G.var".

(* End_SpecReals *)

inline "cic:/CoRN/algebra/CSemiGroups/plus_assoc_unfolded.con".

(* UNEXPORTED
End CSemiGroup_basics
*)

(* End_SpecReals *)

(* UNEXPORTED
Hint Resolve plus_assoc_unfolded: algebra.
*)

(*#* **Functional operations
We can also define a similar addition operator, which will be denoted by [{+}], on partial functions.

%\begin{convention}% Whenever possible, we will denote the functional construction corresponding to an algebraic operation by the same symbol enclosed in curly braces.
%\end{convention}%

At this stage, we will always consider automorphisms; we %{\em %could%}% treat this in a more general setting, but we feel that it wouldn't really be a useful effort.

%\begin{convention}% Let [G:CSemiGroup] and [F,F':(PartFunct G)] and denote by [P] and [Q], respectively, the predicates characterizing their domains.
%\end{convention}%
*)

(* UNEXPORTED
Section Part_Function_Plus
*)

alias id "G" = "cic:/CoRN/algebra/CSemiGroups/Part_Function_Plus/G.var".

alias id "F" = "cic:/CoRN/algebra/CSemiGroups/Part_Function_Plus/F.var".

alias id "F'" = "cic:/CoRN/algebra/CSemiGroups/Part_Function_Plus/F'.var".

(* begin hide *)

inline "cic:/CoRN/algebra/CSemiGroups/Part_Function_Plus/P.con" "Part_Function_Plus__".

inline "cic:/CoRN/algebra/CSemiGroups/Part_Function_Plus/Q.con" "Part_Function_Plus__".

(* end hide *)

inline "cic:/CoRN/algebra/CSemiGroups/part_function_plus_strext.con".

inline "cic:/CoRN/algebra/CSemiGroups/Fplus.con".

(*#*
%\begin{convention}% Let [R:G->CProp].
%\end{convention}%
*)

alias id "R" = "cic:/CoRN/algebra/CSemiGroups/Part_Function_Plus/R.var".

inline "cic:/CoRN/algebra/CSemiGroups/included_FPlus.con".

inline "cic:/CoRN/algebra/CSemiGroups/included_FPlus'.con".

inline "cic:/CoRN/algebra/CSemiGroups/included_FPlus''.con".

(* UNEXPORTED
End Part_Function_Plus
*)

(* UNEXPORTED
Implicit Arguments Fplus [G].
*)

(* NOTATION
Infix "{+}" := Fplus (at level 50, left associativity).
*)

(* UNEXPORTED
Hint Resolve included_FPlus : included.
*)

(* UNEXPORTED
Hint Immediate included_FPlus' included_FPlus'' : included.
*)

(*#* **Subsemigroups
%\begin{convention}%
Let [csg] a semi-group and [P] a non-empty
predicate on the semi-group which is preserved by [[+]].
%\end{convention}%
*)

(* UNEXPORTED
Section SubCSemiGroups
*)

alias id "csg" = "cic:/CoRN/algebra/CSemiGroups/SubCSemiGroups/csg.var".

alias id "P" = "cic:/CoRN/algebra/CSemiGroups/SubCSemiGroups/P.var".

alias id "op_pres_P" = "cic:/CoRN/algebra/CSemiGroups/SubCSemiGroups/op_pres_P.var".

inline "cic:/CoRN/algebra/CSemiGroups/SubCSemiGroups/subcrr.con" "SubCSemiGroups__".

inline "cic:/CoRN/algebra/CSemiGroups/Build_SubCSemiGroup.con".

(* UNEXPORTED
End SubCSemiGroups
*)

