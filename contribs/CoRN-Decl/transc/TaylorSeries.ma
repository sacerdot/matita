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

set "baseuri" "cic:/matita/CoRN-Decl/transc/TaylorSeries".

include "CoRN.ma".

(* $Id: TaylorSeries.v,v 1.7 2004/04/23 10:01:08 lcf Exp $ *)

include "transc/PowerSeries.ma".

include "ftc/Taylor.ma".

(*#* *Taylor Series

We now generalize our work on Taylor's theorem to define the Taylor
series of an infinitely many times differentiable function as a power
series.  We prove convergence (always) of the Taylor series and give
criteria for when the sum of this series is the original function.

**Definitions

%\begin{convention}% Let [J] be a proper interval and [F] an
infinitely many times differentiable function in [J].  Let [a] be a
point of [J].
%\end{convention}%
*)

(* UNEXPORTED
Section Definitions
*)

alias id "J" = "cic:/CoRN/transc/TaylorSeries/Definitions/J.var".

alias id "pJ" = "cic:/CoRN/transc/TaylorSeries/Definitions/pJ.var".

alias id "F" = "cic:/CoRN/transc/TaylorSeries/Definitions/F.var".

alias id "diffF" = "cic:/CoRN/transc/TaylorSeries/Definitions/diffF.var".

alias id "a" = "cic:/CoRN/transc/TaylorSeries/Definitions/a.var".

alias id "Ha" = "cic:/CoRN/transc/TaylorSeries/Definitions/Ha.var".

inline "cic:/CoRN/transc/TaylorSeries/Taylor_Series'.con".

(*#*
%\begin{convention}% Assume also that [f] is the sequence of
derivatives of [F].
%\end{convention}%
*)

alias id "f" = "cic:/CoRN/transc/TaylorSeries/Definitions/f.var".

alias id "derF" = "cic:/CoRN/transc/TaylorSeries/Definitions/derF.var".

inline "cic:/CoRN/transc/TaylorSeries/Taylor_Series.con".

(* UNEXPORTED
Opaque N_Deriv.
*)

(*#* Characterizations of the Taylor remainder. *)

inline "cic:/CoRN/transc/TaylorSeries/Taylor_Rem_char.con".

inline "cic:/CoRN/transc/TaylorSeries/abs_Taylor_Rem_char.con".

(* UNEXPORTED
End Definitions
*)

(* UNEXPORTED
Section Convergence_in_IR
*)

(*#* **Convergence

Our interval is now the real line.  We begin by proving some helpful
continuity properties, then define a boundedness condition for the
derivatives of [F] that guarantees convergence of its Taylor series to
[F].
*)

alias id "H" = "cic:/CoRN/transc/TaylorSeries/Convergence_in_IR/H.var".

alias id "F" = "cic:/CoRN/transc/TaylorSeries/Convergence_in_IR/F.var".

alias id "a" = "cic:/CoRN/transc/TaylorSeries/Convergence_in_IR/a.var".

alias id "Ha" = "cic:/CoRN/transc/TaylorSeries/Convergence_in_IR/Ha.var".

alias id "f" = "cic:/CoRN/transc/TaylorSeries/Convergence_in_IR/f.var".

alias id "derF" = "cic:/CoRN/transc/TaylorSeries/Convergence_in_IR/derF.var".

inline "cic:/CoRN/transc/TaylorSeries/Taylor_Series_imp_cont.con".

inline "cic:/CoRN/transc/TaylorSeries/Taylor_Series_lemma_cont.con".

inline "cic:/CoRN/transc/TaylorSeries/Taylor_bnd.con".

(* begin show *)

alias id "bndf" = "cic:/CoRN/transc/TaylorSeries/Convergence_in_IR/bndf.var".

(* end show *)

(* UNEXPORTED
Opaque nexp_op fac.
*)

(* begin hide *)

inline "cic:/CoRN/transc/TaylorSeries/Convergence_in_IR/H1.con" "Convergence_in_IR__".

(* UNEXPORTED
Transparent nexp_op.
*)

inline "cic:/CoRN/transc/TaylorSeries/Taylor_Series_conv_lemma1.con".

inline "cic:/CoRN/transc/TaylorSeries/Taylor_Series_conv_lemma2.con".

(* end hide *)

(*#* The Taylor series always converges on the realline. *)

(* UNEXPORTED
Transparent nexp_op.
*)

(* UNEXPORTED
Opaque nexp_op.
*)

inline "cic:/CoRN/transc/TaylorSeries/Taylor_Series_conv_IR.con".

(* begin hide *)

(* UNEXPORTED
Transparent nexp_op.
*)

inline "cic:/CoRN/transc/TaylorSeries/Taylor_majoration_lemma.con".

(* UNEXPORTED
Opaque N_Deriv fac.
*)

inline "cic:/CoRN/transc/TaylorSeries/Taylor_Series_conv_lemma3.con".

(* end hide *)

(*#*
We now prove that, under our assumptions, it actually converges to the
original function.  For generality and also usability, however, we
will separately assume convergence.
*)

(* begin show *)

alias id "Hf" = "cic:/CoRN/transc/TaylorSeries/Convergence_in_IR/Hf.var".

(* end show *)

(* UNEXPORTED
Transparent fac.
*)

(* UNEXPORTED
Opaque mult.
*)

inline "cic:/CoRN/transc/TaylorSeries/Taylor_Series_conv_to_fun.con".

(* UNEXPORTED
End Convergence_in_IR
*)

(* UNEXPORTED
Section Other_Results
*)

(*#*
The condition for the previous lemma is not very easy to prove.  We
give some helpful lemmas.
*)

inline "cic:/CoRN/transc/TaylorSeries/Taylor_bnd_trans.con".

(* begin hide *)

(* UNEXPORTED
Opaque nexp_op.
*)

inline "cic:/CoRN/transc/TaylorSeries/convergence_lemma.con".

(* end hide *)

inline "cic:/CoRN/transc/TaylorSeries/bnd_imp_Taylor_bnd.con".

(*#*
Finally, a uniqueness criterium: two functions [F] and [G] are equal,
provided that their derivatives coincide at a given point and their
Taylor series converge to themselves.
*)

alias id "F" = "cic:/CoRN/transc/TaylorSeries/Other_Results/F.var".

alias id "G" = "cic:/CoRN/transc/TaylorSeries/Other_Results/G.var".

alias id "a" = "cic:/CoRN/transc/TaylorSeries/Other_Results/a.var".

alias id "f" = "cic:/CoRN/transc/TaylorSeries/Other_Results/f.var".

alias id "g" = "cic:/CoRN/transc/TaylorSeries/Other_Results/g.var".

alias id "derF" = "cic:/CoRN/transc/TaylorSeries/Other_Results/derF.var".

alias id "derG" = "cic:/CoRN/transc/TaylorSeries/Other_Results/derG.var".

alias id "bndf" = "cic:/CoRN/transc/TaylorSeries/Other_Results/bndf.var".

alias id "bndg" = "cic:/CoRN/transc/TaylorSeries/Other_Results/bndg.var".

(* begin show *)

alias id "Heq" = "cic:/CoRN/transc/TaylorSeries/Other_Results/Heq.var".

(* end show *)

(* begin hide *)

inline "cic:/CoRN/transc/TaylorSeries/Other_Results/Hf.con" "Other_Results__".

(* end hide *)

inline "cic:/CoRN/transc/TaylorSeries/Taylor_unique_crit.con".

(* UNEXPORTED
End Other_Results
*)

