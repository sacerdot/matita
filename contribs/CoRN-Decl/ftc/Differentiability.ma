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

include "CoRN_notation.ma".

(* $Id: Differentiability.v,v 1.5 2004/04/20 22:38:49 hinderer Exp $ *)

include "ftc/PartInterval.ma".

include "ftc/DerivativeOps.ma".

(* UNEXPORTED
Section Definitions.
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
End Definitions.
*)

(* UNEXPORTED
Implicit Arguments Diffble_I [a b].
*)

(* UNEXPORTED
Section Local_Properties.
*)

(*#*
From this point on, we just prove results analogous to the ones for derivability.

A function differentiable in [[a,b]] is differentiable in every proper compact subinterval of [[a,b]].
*)

inline "cic:/CoRN/ftc/Differentiability/included_imp_diffble.con".

(*#*
A function differentiable in an interval is everywhere defined in that interval.
*)

inline "cic:/CoRN/ftc/Differentiability/a.var".

inline "cic:/CoRN/ftc/Differentiability/b.var".

inline "cic:/CoRN/ftc/Differentiability/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Differentiability/Hab.con".

inline "cic:/CoRN/ftc/Differentiability/I.con".

(* end hide *)

inline "cic:/CoRN/ftc/Differentiability/diffble_imp_inc.con".

(*#*
If a function has a derivative in an interval then it is differentiable in that interval.
*)

inline "cic:/CoRN/ftc/Differentiability/deriv_imp_Diffble_I.con".

(* UNEXPORTED
End Local_Properties.
*)

(* UNEXPORTED
Hint Resolve diffble_imp_inc: included.
*)

(* UNEXPORTED
Section Operations.
*)

(*#*
All the algebraic results carry on.
*)

inline "cic:/CoRN/ftc/Differentiability/a.var".

inline "cic:/CoRN/ftc/Differentiability/b.var".

inline "cic:/CoRN/ftc/Differentiability/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Differentiability/Hab.con".

inline "cic:/CoRN/ftc/Differentiability/I.con".

(* end hide *)

(* UNEXPORTED
Section Constants.
*)

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_const.con".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_id.con".

(* UNEXPORTED
End Constants.
*)

(* UNEXPORTED
Section Well_Definedness.
*)

inline "cic:/CoRN/ftc/Differentiability/F.var".

inline "cic:/CoRN/ftc/Differentiability/H.var".

inline "cic:/CoRN/ftc/Differentiability/diffF.var".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_wd.con".

(* UNEXPORTED
End Well_Definedness.
*)

inline "cic:/CoRN/ftc/Differentiability/F.var".

inline "cic:/CoRN/ftc/Differentiability/G.var".

inline "cic:/CoRN/ftc/Differentiability/diffF.var".

inline "cic:/CoRN/ftc/Differentiability/diffG.var".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_plus.con".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_inv.con".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_mult.con".

(* begin show *)

inline "cic:/CoRN/ftc/Differentiability/Gbnd.var".

(* end show *)

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_recip.con".

(* UNEXPORTED
End Operations.
*)

(* UNEXPORTED
Section Corollaries.
*)

inline "cic:/CoRN/ftc/Differentiability/a.var".

inline "cic:/CoRN/ftc/Differentiability/b.var".

inline "cic:/CoRN/ftc/Differentiability/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Differentiability/Hab.con".

inline "cic:/CoRN/ftc/Differentiability/I.con".

(* end hide *)

inline "cic:/CoRN/ftc/Differentiability/F.var".

inline "cic:/CoRN/ftc/Differentiability/G.var".

inline "cic:/CoRN/ftc/Differentiability/diffF.var".

inline "cic:/CoRN/ftc/Differentiability/diffG.var".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_minus.con".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_scal.con".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_nth.con".

inline "cic:/CoRN/ftc/Differentiability/Gbnd.var".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_div.con".

(* UNEXPORTED
End Corollaries.
*)

(* UNEXPORTED
Section Other_Properties.
*)

(*#*
Differentiability of families of functions is proved by
induction using the constant and addition rules.
*)

inline "cic:/CoRN/ftc/Differentiability/a.var".

inline "cic:/CoRN/ftc/Differentiability/b.var".

inline "cic:/CoRN/ftc/Differentiability/Hab'.var".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_Sum0.con".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_Sumx.con".

inline "cic:/CoRN/ftc/Differentiability/Diffble_I_Sum.con".

(* UNEXPORTED
End Other_Properties.
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

