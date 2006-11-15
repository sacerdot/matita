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

(* $Id: FTC.v,v 1.5 2004/04/23 10:00:58 lcf Exp $ *)

(*#* printing [-S-] %\ensuremath{\int}% #&int;# *)

(* INCLUDE
MoreIntegrals
*)

(* INCLUDE
CalculusTheorems
*)

(* UNEXPORTED
Opaque Min.
*)

(* UNEXPORTED
Section Indefinite_Integral.
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

inline cic:/CoRN/ftc/FTC/I.var.

inline cic:/CoRN/ftc/FTC/F.var.

inline cic:/CoRN/ftc/FTC/contF.var.

inline cic:/CoRN/ftc/FTC/a.var.

inline cic:/CoRN/ftc/FTC/Ha.var.

inline cic:/CoRN/ftc/FTC/prim_lemma.con.

inline cic:/CoRN/ftc/FTC/Fprim_strext.con.

inline cic:/CoRN/ftc/FTC/Fprim.con.

(* UNEXPORTED
End Indefinite_Integral.
*)

(* UNEXPORTED
Implicit Arguments Fprim [I F].
*)

(* UNEXPORTED
Section FTC.
*)

(*#* **The FTC

We can now prove our main theorem.  We begin by remarking that the
primitive function is always continuous.

%\begin{convention}% Assume that [J : interval], [F : PartIR] is
continuous in [J] and [x0] is a point in [J].  Denote by [G] the
indefinite integral of [F] from [x0].
%\end{convention}%
*)

inline cic:/CoRN/ftc/FTC/J.var.

inline cic:/CoRN/ftc/FTC/F.var.

inline cic:/CoRN/ftc/FTC/contF.var.

inline cic:/CoRN/ftc/FTC/x0.var.

inline cic:/CoRN/ftc/FTC/Hx0.var.

(* begin hide *)

inline cic:/CoRN/ftc/FTC/G.con.

(* end hide *)

inline cic:/CoRN/ftc/FTC/Continuous_prim.con.

(*#*
The derivative of [G] is simply [F].
*)

inline cic:/CoRN/ftc/FTC/pJ.var.

inline cic:/CoRN/ftc/FTC/FTC1.con.

(*#*
Any other function [G0] with derivative [F] must differ from [G] by a constant.
*)

inline cic:/CoRN/ftc/FTC/G0.var.

inline cic:/CoRN/ftc/FTC/derG0.var.

inline cic:/CoRN/ftc/FTC/FTC2.con.

(*#*
The following is another statement of the Fundamental Theorem of Calculus, also known as Barrow's rule.
*)

(* begin hide *)

inline cic:/CoRN/ftc/FTC/G0_inc.con.

(* end hide *)

(* UNEXPORTED
Opaque G.
*)

inline cic:/CoRN/ftc/FTC/Barrow.con.

(* end hide *)

(* UNEXPORTED
End FTC.
*)

(* UNEXPORTED
Hint Resolve Continuous_prim: continuous.
*)

(* UNEXPORTED
Hint Resolve FTC1: derivate.
*)

(* UNEXPORTED
Section Limit_of_Integral_Seq.
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

inline cic:/CoRN/ftc/FTC/J.var.

inline cic:/CoRN/ftc/FTC/f.var.

inline cic:/CoRN/ftc/FTC/F.var.

inline cic:/CoRN/ftc/FTC/contf.var.

inline cic:/CoRN/ftc/FTC/contF.var.

(* UNEXPORTED
Section Compact.
*)

(*#*
We need to prove this result first for compact intervals.

%\begin{convention}% Assume that [a, b, x0 : IR] with [(f n)] and [F]
continuous in [[a,b]], $x0\in[a,b]$#x0&isin;[a,b]#; denote by
[(g n)] and [G] the indefinite integrals respectively of [(f n)] and
[F] with origin [x0].
%\end{convention}%
*)

inline cic:/CoRN/ftc/FTC/a.var.

inline cic:/CoRN/ftc/FTC/b.var.

inline cic:/CoRN/ftc/FTC/Hab.var.

inline cic:/CoRN/ftc/FTC/contIf.var.

inline cic:/CoRN/ftc/FTC/contIF.var.

(* begin show *)

inline cic:/CoRN/ftc/FTC/convF.var.

(* end show *)

inline cic:/CoRN/ftc/FTC/x0.var.

inline cic:/CoRN/ftc/FTC/Hx0.var.

inline cic:/CoRN/ftc/FTC/Hx0'.var.

(* begin hide *)

inline cic:/CoRN/ftc/FTC/g.con.

inline cic:/CoRN/ftc/FTC/G.con.

(* end hide *)

(* begin show *)

inline cic:/CoRN/ftc/FTC/contg.var.

inline cic:/CoRN/ftc/FTC/contG.var.

(* end show *)

inline cic:/CoRN/ftc/FTC/fun_lim_seq_integral.con.

(* UNEXPORTED
End Compact.
*)

(*#*
And now we can generalize it step by step.
*)

inline cic:/CoRN/ftc/FTC/limit_of_integral.con.

inline cic:/CoRN/ftc/FTC/limit_of_Integral.con.

(* UNEXPORTED
Section General.
*)

(*#*
Finally, with [x0, g, G] as before,
*)

(* begin show *)

inline cic:/CoRN/ftc/FTC/convF.var.

(* end show *)

inline cic:/CoRN/ftc/FTC/x0.var.

inline cic:/CoRN/ftc/FTC/Hx0.var.

(* begin hide *)

inline cic:/CoRN/ftc/FTC/g.con.

inline cic:/CoRN/ftc/FTC/G.con.

(* end hide *)

inline cic:/CoRN/ftc/FTC/contg.var.

inline cic:/CoRN/ftc/FTC/contG.var.

inline cic:/CoRN/ftc/FTC/fun_lim_seq_integral_IR.con.

(* UNEXPORTED
End General.
*)

(* UNEXPORTED
End Limit_of_Integral_Seq.
*)

(* UNEXPORTED
Section Limit_of_Derivative_Seq.
*)

(*#*
Similar results hold for the sequence of derivatives of a converging sequence; this time the proof is easier, as we can do it directly for any kind of interval.

%\begin{convention}% Let [g] be the sequence of derivatives of [f] and [G] be the derivative of [F].
%\end{convention}%
*)

inline cic:/CoRN/ftc/FTC/J.var.

inline cic:/CoRN/ftc/FTC/pJ.var.

inline cic:/CoRN/ftc/FTC/f.var.

inline cic:/CoRN/ftc/FTC/g.var.

inline cic:/CoRN/ftc/FTC/F.var.

inline cic:/CoRN/ftc/FTC/G.var.

inline cic:/CoRN/ftc/FTC/contf.var.

inline cic:/CoRN/ftc/FTC/contF.var.

inline cic:/CoRN/ftc/FTC/convF.var.

inline cic:/CoRN/ftc/FTC/contg.var.

inline cic:/CoRN/ftc/FTC/contG.var.

inline cic:/CoRN/ftc/FTC/convG.var.

inline cic:/CoRN/ftc/FTC/derf.var.

inline cic:/CoRN/ftc/FTC/fun_lim_seq_derivative.con.

(* UNEXPORTED
End Limit_of_Derivative_Seq.
*)

(* UNEXPORTED
Section Derivative_Series.
*)

(*#*
As a very important case of this result, we get a rule for deriving series.
*)

inline cic:/CoRN/ftc/FTC/J.var.

inline cic:/CoRN/ftc/FTC/pJ.var.

inline cic:/CoRN/ftc/FTC/f.var.

inline cic:/CoRN/ftc/FTC/g.var.

(* begin show *)

inline cic:/CoRN/ftc/FTC/convF.var.

inline cic:/CoRN/ftc/FTC/convG.var.

(* end show *)

inline cic:/CoRN/ftc/FTC/derF.var.

inline cic:/CoRN/ftc/FTC/Derivative_FSeries.con.

(* UNEXPORTED
End Derivative_Series.
*)

