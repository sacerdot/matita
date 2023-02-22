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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/FTC".

include "CoRN.ma".

(* $Id: FTC.v,v 1.5 2004/04/23 10:00:58 lcf Exp $ *)

(*#* printing [-S-] %\ensuremath{\int}% #&int;# *)

include "ftc/MoreIntegrals.ma".

include "ftc/CalculusTheorems.ma".

(* UNEXPORTED
Opaque Min.
*)

(* UNEXPORTED
Section Indefinite_Integral
*)

(*#* *The Fundamental Theorem of Calculus

Finally we can prove the fundamental theorem of calculus and its most
important corollaries, which are the main tools to formalize most of
real analysis.

**Indefinite Integrals

We define the indefinite integral of a function in a proper interval
in the obvious way; we just need to state a first lemma so that the
continuity proofs become unnecessary.

%\begin{convention}% Let [I : interval], [F : PartIR] be continuous in [I]
and [a] be a point in [I].
%\end{convention}%
*)

alias id "I" = "cic:/CoRN/ftc/FTC/Indefinite_Integral/I.var".

alias id "F" = "cic:/CoRN/ftc/FTC/Indefinite_Integral/F.var".

alias id "contF" = "cic:/CoRN/ftc/FTC/Indefinite_Integral/contF.var".

alias id "a" = "cic:/CoRN/ftc/FTC/Indefinite_Integral/a.var".

alias id "Ha" = "cic:/CoRN/ftc/FTC/Indefinite_Integral/Ha.var".

inline "cic:/CoRN/ftc/FTC/prim_lemma.con".

inline "cic:/CoRN/ftc/FTC/Fprim_strext.con".

inline "cic:/CoRN/ftc/FTC/Fprim.con".

(* UNEXPORTED
End Indefinite_Integral
*)

(* UNEXPORTED
Implicit Arguments Fprim [I F].
*)

(* NOTATION
Notation "[-S-] F" := (Fprim F) (at level 20).
*)

(* UNEXPORTED
Section FTC
*)

(*#* **The FTC

We can now prove our main theorem.  We begin by remarking that the
primitive function is always continuous.

%\begin{convention}% Assume that [J : interval], [F : PartIR] is
continuous in [J] and [x0] is a point in [J].  Denote by [G] the
indefinite integral of [F] from [x0].
%\end{convention}%
*)

alias id "J" = "cic:/CoRN/ftc/FTC/FTC/J.var".

alias id "F" = "cic:/CoRN/ftc/FTC/FTC/F.var".

alias id "contF" = "cic:/CoRN/ftc/FTC/FTC/contF.var".

alias id "x0" = "cic:/CoRN/ftc/FTC/FTC/x0.var".

alias id "Hx0" = "cic:/CoRN/ftc/FTC/FTC/Hx0.var".

(* begin hide *)

inline "cic:/CoRN/ftc/FTC/FTC/G.con" "FTC__".

(* end hide *)

inline "cic:/CoRN/ftc/FTC/Continuous_prim.con".

(*#*
The derivative of [G] is simply [F].
*)

alias id "pJ" = "cic:/CoRN/ftc/FTC/FTC/pJ.var".

inline "cic:/CoRN/ftc/FTC/FTC1.con".

(*#*
Any other function [G0] with derivative [F] must differ from [G] by a constant.
*)

alias id "G0" = "cic:/CoRN/ftc/FTC/FTC/G0.var".

alias id "derG0" = "cic:/CoRN/ftc/FTC/FTC/derG0.var".

inline "cic:/CoRN/ftc/FTC/FTC2.con".

(*#*
The following is another statement of the Fundamental Theorem of Calculus, also known as Barrow's rule.
*)

(* begin hide *)

inline "cic:/CoRN/ftc/FTC/FTC/G0_inc.con" "FTC__".

(* end hide *)

(* UNEXPORTED
Opaque G.
*)

inline "cic:/CoRN/ftc/FTC/Barrow.con".

(* end hide *)

(* UNEXPORTED
End FTC
*)

(* UNEXPORTED
Hint Resolve Continuous_prim: continuous.
*)

(* UNEXPORTED
Hint Resolve FTC1: derivate.
*)

(* UNEXPORTED
Section Limit_of_Integral_Seq
*)

(*#* **Corollaries

With these tools in our hand, we can prove several useful results.

%\begin{convention}% From this point onwards:
 - [J : interval];
 - [f : nat->PartIR] is a sequence of continuous functions (in [J]);
 - [F : PartIR] is continuous in [J].

%\end{convention}%

In the first place, if a sequence of continuous functions converges
then the sequence of their primitives also converges, and the limit
commutes with the indefinite integral.
*)

alias id "J" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/J.var".

alias id "f" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/f.var".

alias id "F" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/F.var".

alias id "contf" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/contf.var".

alias id "contF" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/contF.var".

(* UNEXPORTED
Section Compact
*)

(*#*
We need to prove this result first for compact intervals.

%\begin{convention}% Assume that [a, b, x0 : IR] with [(f n)] and [F]
continuous in [[a,b]], $x0\in[a,b]$#x0&isin;[a,b]#; denote by
[(g n)] and [G] the indefinite integrals respectively of [(f n)] and
[F] with origin [x0].
%\end{convention}%
*)

alias id "a" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/Compact/a.var".

alias id "b" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/Compact/b.var".

alias id "Hab" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/Compact/Hab.var".

alias id "contIf" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/Compact/contIf.var".

alias id "contIF" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/Compact/contIF.var".

(* begin show *)

alias id "convF" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/Compact/convF.var".

(* end show *)

alias id "x0" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/Compact/x0.var".

alias id "Hx0" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/Compact/Hx0.var".

alias id "Hx0'" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/Compact/Hx0'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/Compact/g.con" "Limit_of_Integral_Seq__Compact__".

inline "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/Compact/G.con" "Limit_of_Integral_Seq__Compact__".

(* end hide *)

(* begin show *)

alias id "contg" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/Compact/contg.var".

alias id "contG" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/Compact/contG.var".

(* end show *)

inline "cic:/CoRN/ftc/FTC/fun_lim_seq_integral.con".

(* UNEXPORTED
End Compact
*)

(*#*
And now we can generalize it step by step.
*)

inline "cic:/CoRN/ftc/FTC/limit_of_integral.con".

inline "cic:/CoRN/ftc/FTC/limit_of_Integral.con".

(* UNEXPORTED
Section General
*)

(*#*
Finally, with [x0, g, G] as before,
*)

(* begin show *)

alias id "convF" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/General/convF.var".

(* end show *)

alias id "x0" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/General/x0.var".

alias id "Hx0" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/General/Hx0.var".

(* begin hide *)

inline "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/General/g.con" "Limit_of_Integral_Seq__General__".

inline "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/General/G.con" "Limit_of_Integral_Seq__General__".

(* end hide *)

alias id "contg" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/General/contg.var".

alias id "contG" = "cic:/CoRN/ftc/FTC/Limit_of_Integral_Seq/General/contG.var".

inline "cic:/CoRN/ftc/FTC/fun_lim_seq_integral_IR.con".

(* UNEXPORTED
End General
*)

(* UNEXPORTED
End Limit_of_Integral_Seq
*)

(* UNEXPORTED
Section Limit_of_Derivative_Seq
*)

(*#*
Similar results hold for the sequence of derivatives of a converging sequence; this time the proof is easier, as we can do it directly for any kind of interval.

%\begin{convention}% Let [g] be the sequence of derivatives of [f] and [G] be the derivative of [F].
%\end{convention}%
*)

alias id "J" = "cic:/CoRN/ftc/FTC/Limit_of_Derivative_Seq/J.var".

alias id "pJ" = "cic:/CoRN/ftc/FTC/Limit_of_Derivative_Seq/pJ.var".

alias id "f" = "cic:/CoRN/ftc/FTC/Limit_of_Derivative_Seq/f.var".

alias id "g" = "cic:/CoRN/ftc/FTC/Limit_of_Derivative_Seq/g.var".

alias id "F" = "cic:/CoRN/ftc/FTC/Limit_of_Derivative_Seq/F.var".

alias id "G" = "cic:/CoRN/ftc/FTC/Limit_of_Derivative_Seq/G.var".

alias id "contf" = "cic:/CoRN/ftc/FTC/Limit_of_Derivative_Seq/contf.var".

alias id "contF" = "cic:/CoRN/ftc/FTC/Limit_of_Derivative_Seq/contF.var".

alias id "convF" = "cic:/CoRN/ftc/FTC/Limit_of_Derivative_Seq/convF.var".

alias id "contg" = "cic:/CoRN/ftc/FTC/Limit_of_Derivative_Seq/contg.var".

alias id "contG" = "cic:/CoRN/ftc/FTC/Limit_of_Derivative_Seq/contG.var".

alias id "convG" = "cic:/CoRN/ftc/FTC/Limit_of_Derivative_Seq/convG.var".

alias id "derf" = "cic:/CoRN/ftc/FTC/Limit_of_Derivative_Seq/derf.var".

inline "cic:/CoRN/ftc/FTC/fun_lim_seq_derivative.con".

(* UNEXPORTED
End Limit_of_Derivative_Seq
*)

(* UNEXPORTED
Section Derivative_Series
*)

(*#*
As a very important case of this result, we get a rule for deriving series.
*)

alias id "J" = "cic:/CoRN/ftc/FTC/Derivative_Series/J.var".

alias id "pJ" = "cic:/CoRN/ftc/FTC/Derivative_Series/pJ.var".

alias id "f" = "cic:/CoRN/ftc/FTC/Derivative_Series/f.var".

alias id "g" = "cic:/CoRN/ftc/FTC/Derivative_Series/g.var".

(* begin show *)

alias id "convF" = "cic:/CoRN/ftc/FTC/Derivative_Series/convF.var".

alias id "convG" = "cic:/CoRN/ftc/FTC/Derivative_Series/convG.var".

(* end show *)

alias id "derF" = "cic:/CoRN/ftc/FTC/Derivative_Series/derF.var".

inline "cic:/CoRN/ftc/FTC/Derivative_FSeries.con".

(* UNEXPORTED
End Derivative_Series
*)

