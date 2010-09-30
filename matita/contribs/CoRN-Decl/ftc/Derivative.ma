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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/Derivative".

include "CoRN.ma".

(* $Id: Derivative.v,v 1.7 2004/04/23 10:00:58 lcf Exp $ *)

include "ftc/Continuity.ma".

(* UNEXPORTED
Section Definitions
*)

(*#* *Derivatives

We will now proceed toward the development of differential calculus.
To begin with, the main notion is that of derivative.

At this stage we will not define a notion of differentiable function,
mainly because the natural definition (that of being a function which
has some derivative) poses some technical problems; thus, we will
postpone that part of our work to a subsequent stage.

Derivative is a binary relation in the type of partial functions,
dependent (once again) on a compact interval with distinct
endpoints#. #%\footnote{%As before, we do not define pointwise
differentiability, mainly for coherence reasons.  See Bishop [1967]
for a discussion on the relative little interest of that concept.%}.%
The reason for requiring the endpoints to be apart is mainly to be
able to derive the usual properties of the derivative
relation---namely, that any two derivatives of the same function must
coincide.

%\begin{convention}% Let [a,b:IR] with [a [<] b] and denote by [I] the
interval [[a,b]].  Throughout this chapter, [F, F', G, G'] and [H]
will be partial functions with domains respectively [P, P', Q, Q'] and
[R].
%\end{convention}%
*)

alias id "a" = "cic:/CoRN/ftc/Derivative/Definitions/a.var".

alias id "b" = "cic:/CoRN/ftc/Derivative/Definitions/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/Derivative/Definitions/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Derivative/Definitions/Hab.con" "Definitions__".

inline "cic:/CoRN/ftc/Derivative/Definitions/I.con" "Definitions__".

(* end hide *)

alias id "F" = "cic:/CoRN/ftc/Derivative/Definitions/F.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Derivative/Definitions/P.con" "Definitions__".

(* end hide *)

inline "cic:/CoRN/ftc/Derivative/Derivative_I.con".

(* UNEXPORTED
End Definitions
*)

(* UNEXPORTED
Implicit Arguments Derivative_I [a b].
*)

(* UNEXPORTED
Section Basic_Properties
*)

(*#* **Basic Properties
*)

alias id "a" = "cic:/CoRN/ftc/Derivative/Basic_Properties/a.var".

alias id "b" = "cic:/CoRN/ftc/Derivative/Basic_Properties/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/Derivative/Basic_Properties/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Derivative/Basic_Properties/Hab.con" "Basic_Properties__".

inline "cic:/CoRN/ftc/Derivative/Basic_Properties/I.con" "Basic_Properties__".

(* end hide *)

(*#*
Like we did for equality, we begin by stating a lemma that makes proofs of derivation easier in practice.
*)

inline "cic:/CoRN/ftc/Derivative/Derivative_I_char.con".

(* end hide *)

(*#*
Derivative is a well defined relation; we will make this explicit for both arguments:
*)

alias id "F" = "cic:/CoRN/ftc/Derivative/Basic_Properties/F.var".

alias id "G" = "cic:/CoRN/ftc/Derivative/Basic_Properties/G.var".

alias id "H" = "cic:/CoRN/ftc/Derivative/Basic_Properties/H.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Derivative/Basic_Properties/P.con" "Basic_Properties__".

inline "cic:/CoRN/ftc/Derivative/Basic_Properties/Q.con" "Basic_Properties__".

inline "cic:/CoRN/ftc/Derivative/Basic_Properties/R.con" "Basic_Properties__".

(* end hide *)

inline "cic:/CoRN/ftc/Derivative/Derivative_I_wdl.con".

inline "cic:/CoRN/ftc/Derivative/Derivative_I_wdr.con".

(* begin hide *)

inline "cic:/CoRN/ftc/Derivative/Basic_Properties/Derivative_I_unique_lemma.con" "Basic_Properties__".

(* end hide *)

(*#*
Derivative is unique.
*)

inline "cic:/CoRN/ftc/Derivative/Derivative_I_unique.con".

(*#*
Finally, the set where we are considering the relation is included in the domain of both functions.
*)

inline "cic:/CoRN/ftc/Derivative/derivative_imp_inc.con".

inline "cic:/CoRN/ftc/Derivative/derivative_imp_inc'.con".

(*#*
Any function that is or has a derivative is continuous.
*)

alias id "Hab''" = "cic:/CoRN/ftc/Derivative/Basic_Properties/Hab''.var".

inline "cic:/CoRN/ftc/Derivative/deriv_imp_contin'_I.con".

inline "cic:/CoRN/ftc/Derivative/deriv_imp_contin_I.con".

(* UNEXPORTED
End Basic_Properties
*)

(*#*
If [G] is the derivative of [F] in a given interval, then [G] is also the derivative of [F] in any smaller interval.
*)

inline "cic:/CoRN/ftc/Derivative/included_imp_deriv.con".

