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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/Differentiability".

include "CoRN.ma".

(* $Id: Differentiability.v,v 1.5 2004/04/20 22:38:49 hinderer Exp $ *)

include "ftc/PartInterval.ma".

include "ftc/DerivativeOps.ma".

(* UNEXPORTED
Section Definitions
*)

(*#* *Differentiability

We will now use our work on derivatives to define a notion of
differentiable function and prove its main properties.

%\begin{convention}% Throughout this section, [a,b] will be real
numbers with [a [<] b], [I] will denote the interval [[a,b]]
and [F,G,H] will be differentiable functions.
%\end{convention}%

Usually a function [F] is said to be differentiable in a proper
compact interval [[a,b]] if there exists another function [F']
such that [F'] is a derivative of [F] in that interval.  There is a
problem in formalizing this definition, as we pointed out earlier on,
which is that if we simply write it down as is we are not able to get
such a function [F'] from a hypothesis that [F] is differentiable.

However, it turns out that this is not altogether the best definition
for the following reason: if we say that [F] is differentiable in
[[a,b]], we mean that there is a partial function [F'] which is
defined in [[a,b]] and satisfies a certain condition in that
interval but nothing is required of the behaviour of the function
outside [[a,b]].  Thus we can argue that, from a mathematical
point of view, the [F'] that we get eliminating a hypothesis of
differentiability should be defined exactly on that interval.  If we
do this, we can quantify over the set of setoid functions in that
interval and eliminate the existencial quantifier without any
problems.
*)

inline "cic:/CoRN/ftc/Differentiability/Diffble_I.con".

(* UNEXPORTED
End Definitions
*)

(* UNEXPORTED
Implicit Arguments Diffble_I [a b].
*)

(* UNEXPORTED
Section Local_Properties
*)

(*#*
From this point on, we just prove results analogous to the ones for derivability.

A function differentiable in [[a,b]] is differentiable in every proper compact subinterval of [[a,b]].
*)

inline "cic:/CoRN/ftc/Differentiability/included_imp_diffble.con".

(*#*
A function differentiable in an interval is everywhere defined in that interval.
*)

alias id "a" = "cic:/CoRN/ftc/Differentiability/Local_Properties/a.var".

alias id "b" = "cic:/CoRN/ftc/Differentiability/Local_Properties/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/Differentiability/Local_Properties/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Differentiability/Local_Properties/Hab.con" "Local_Properties__".

inline "cic:/CoRN/ftc/Differentiability/Local_Properties/I.con" "Local_Properties__".

(* end hide *)

inline "cic:/CoRN/ftc/Differentiability/diffble_imp_inc.con".

(*#*
If a function has a derivative in an interval then it is differentiable in that interval.
*)

inline "cic:/CoRN/ftc/Differentiability/deriv_imp_Diffble_I.con".

(* UNEXPORTED
End Local_Properties
*)

(* UNEXPORTED
Hint Resolve diffble_imp_inc: included.
*)

(* UNEXPORTED
Section Operations
*)

(*#*
All the algebraic results carry on.
*)

alias id "a" = "cic:/CoRN/ftc/Differentiability/Operations/a.var".

alias id "b" = "cic:/CoRN/ftc/Differentiability/Operations/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/Differentiability/Operations/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Differentiability/Operations/Hab.con" "Operations__".

inline "cic:/CoRN/ftc/Differentiability/Operations/I.con" "Operations__".

(* end hide *)

(* UNEXPORTED
Section Constants
*)

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_const.con".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_id.con".

(* UNEXPORTED
End Constants
*)

(* UNEXPORTED
Section Well_Definedness
*)

alias id "F" = "cic:/CoRN/ftc/Differentiability/Operations/Well_Definedness/F.var".

alias id "H" = "cic:/CoRN/ftc/Differentiability/Operations/Well_Definedness/H.var".

alias id "diffF" = "cic:/CoRN/ftc/Differentiability/Operations/Well_Definedness/diffF.var".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_wd.con".

(* UNEXPORTED
End Well_Definedness
*)

alias id "F" = "cic:/CoRN/ftc/Differentiability/Operations/F.var".

alias id "G" = "cic:/CoRN/ftc/Differentiability/Operations/G.var".

alias id "diffF" = "cic:/CoRN/ftc/Differentiability/Operations/diffF.var".

alias id "diffG" = "cic:/CoRN/ftc/Differentiability/Operations/diffG.var".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_plus.con".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_inv.con".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_mult.con".

(* begin show *)

alias id "Gbnd" = "cic:/CoRN/ftc/Differentiability/Operations/Gbnd.var".

(* end show *)

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_recip.con".

(* UNEXPORTED
End Operations
*)

(* UNEXPORTED
Section Corollaries
*)

alias id "a" = "cic:/CoRN/ftc/Differentiability/Corollaries/a.var".

alias id "b" = "cic:/CoRN/ftc/Differentiability/Corollaries/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/Differentiability/Corollaries/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Differentiability/Corollaries/Hab.con" "Corollaries__".

inline "cic:/CoRN/ftc/Differentiability/Corollaries/I.con" "Corollaries__".

(* end hide *)

alias id "F" = "cic:/CoRN/ftc/Differentiability/Corollaries/F.var".

alias id "G" = "cic:/CoRN/ftc/Differentiability/Corollaries/G.var".

alias id "diffF" = "cic:/CoRN/ftc/Differentiability/Corollaries/diffF.var".

alias id "diffG" = "cic:/CoRN/ftc/Differentiability/Corollaries/diffG.var".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_minus.con".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_scal.con".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_nth.con".

alias id "Gbnd" = "cic:/CoRN/ftc/Differentiability/Corollaries/Gbnd.var".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_div.con".

(* UNEXPORTED
End Corollaries
*)

(* UNEXPORTED
Section Other_Properties
*)

(*#*
Differentiability of families of functions is proved by
induction using the constant and addition rules.
*)

alias id "a" = "cic:/CoRN/ftc/Differentiability/Other_Properties/a.var".

alias id "b" = "cic:/CoRN/ftc/Differentiability/Other_Properties/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/Differentiability/Other_Properties/Hab'.var".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_Sum0.con".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_Sumx.con".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_Sum.con".

(* UNEXPORTED
End Other_Properties
*)

(*#*
Finally, a differentiable function is continuous.

%\begin{convention}% Let [F] be a partial function with derivative [F'] on [I].
%\end{convention}%
*)

inline "cic:/CoRN/ftc/Differentiability/diffble_imp_contin_I.con".

(* UNEXPORTED
Hint Immediate included_imp_contin deriv_imp_contin_I deriv_imp_contin'_I
  diffble_imp_contin_I: continuous.
*)

(* UNEXPORTED
Hint Immediate included_imp_deriv: derivate.
*)

