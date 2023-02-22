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

include "CoRN.ma".

(* $Id: FunctSeries.v,v 1.6 2004/04/23 10:00:58 lcf Exp $ *)

include "ftc/FunctSequence.ma".

include "reals/Series.ma".

(*#* printing fun_seq_part_sum %\ensuremath{\sum^n}% #&sum;<sup>n</sup># *)

(*#* printing Fun_Series_Sum %\ensuremath{\sum_0^{\infty}}% #&sum;<sub>0</sub><sup>&infin;</sup># *)

(* UNEXPORTED
Section Definitions
*)

(*#* *Series of Functions

We now turn our attention to series of functions.  Like it was already
the case for sequences, we will mainly rewrite the results we proved
for series of real numbers in a different way.

%\begin{convention}% Throughout this section:
 - [a] and [b] will be real numbers and the interval [[a,b]] will be denoted
by [I];
 - [f, g] and [h] will denote sequences of continuous functions;
 - [F, G] and [H] will denote continuous functions.

%\end{convention}%

** Definitions

As before, we will consider only sequences of continuous functions
defined in a compact interval.  For this, partial sums are defined and
convergence is simply the convergence of the sequence of partial sums.
*)

alias id "a" = "cic:/CoRN/ftc/FunctSeries/Definitions/a.var".

alias id "b" = "cic:/CoRN/ftc/FunctSeries/Definitions/b.var".

alias id "Hab" = "cic:/CoRN/ftc/FunctSeries/Definitions/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/FunctSeries/Definitions/I.con" "Definitions__".

(* end hide *)

alias id "f" = "cic:/CoRN/ftc/FunctSeries/Definitions/f.var".

inline "cic:/CoRN/ftc/FunctSeries/fun_seq_part_sum.con".

inline "cic:/CoRN/ftc/FunctSeries/fun_seq_part_sum_cont.con".

inline "cic:/CoRN/ftc/FunctSeries/fun_series_convergent.con".

(*#*
For what comes up next we need to know that the convergence of a
series of functions implies pointwise convergence of the corresponding
real number series.
*)

inline "cic:/CoRN/ftc/FunctSeries/fun_series_conv_imp_conv.con".

(*#* We then define the sum of the series as being the pointwise sum of
the corresponding series.
*)

(* begin show *)

alias id "H" = "cic:/CoRN/ftc/FunctSeries/Definitions/H.var".

(* end show *)

(* begin hide *)

inline "cic:/CoRN/ftc/FunctSeries/Definitions/contf.con" "Definitions__".

inline "cic:/CoRN/ftc/FunctSeries/Definitions/incf.con" "Definitions__".

(* end hide *)

inline "cic:/CoRN/ftc/FunctSeries/Fun_Series_Sum_strext.con".

inline "cic:/CoRN/ftc/FunctSeries/Fun_Series_Sum.con".

(* UNEXPORTED
End Definitions
*)

(* UNEXPORTED
Implicit Arguments Fun_Series_Sum [a b Hab f].
*)

(* UNEXPORTED
Hint Resolve fun_seq_part_sum_cont: continuous.
*)

(* UNEXPORTED
Section More_Definitions
*)

alias id "a" = "cic:/CoRN/ftc/FunctSeries/More_Definitions/a.var".

alias id "b" = "cic:/CoRN/ftc/FunctSeries/More_Definitions/b.var".

alias id "Hab" = "cic:/CoRN/ftc/FunctSeries/More_Definitions/Hab.var".

alias id "f" = "cic:/CoRN/ftc/FunctSeries/More_Definitions/f.var".

(*#* A series can also be absolutely convergent. *)

inline "cic:/CoRN/ftc/FunctSeries/fun_series_abs_convergent.con".

(* UNEXPORTED
End More_Definitions
*)

(* UNEXPORTED
Section Operations
*)

(* **Algebraic Properties

All of these are analogous to the properties for series of real numbers, so we won't comment much about them.
*)

alias id "a" = "cic:/CoRN/ftc/FunctSeries/Operations/a.var".

alias id "b" = "cic:/CoRN/ftc/FunctSeries/Operations/b.var".

alias id "Hab" = "cic:/CoRN/ftc/FunctSeries/Operations/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/FunctSeries/Operations/I.con" "Operations__".

(* end hide *)

inline "cic:/CoRN/ftc/FunctSeries/fun_seq_part_sum_n.con".

inline "cic:/CoRN/ftc/FunctSeries/conv_fun_const_series.con".

inline "cic:/CoRN/ftc/FunctSeries/fun_const_series_sum.con".

inline "cic:/CoRN/ftc/FunctSeries/conv_zero_fun_series.con".

inline "cic:/CoRN/ftc/FunctSeries/Fun_Series_Sum_zero.con".

(* begin show *)

alias id "f" = "cic:/CoRN/ftc/FunctSeries/Operations/f.var".

alias id "g" = "cic:/CoRN/ftc/FunctSeries/Operations/g.var".

(* end show *)

inline "cic:/CoRN/ftc/FunctSeries/fun_series_convergent_wd.con".

(* begin show *)

alias id "convF" = "cic:/CoRN/ftc/FunctSeries/Operations/convF.var".

alias id "convG" = "cic:/CoRN/ftc/FunctSeries/Operations/convG.var".

(* end show *)

inline "cic:/CoRN/ftc/FunctSeries/Fun_Series_Sum_wd'.con".

inline "cic:/CoRN/ftc/FunctSeries/conv_fun_series_plus.con".

inline "cic:/CoRN/ftc/FunctSeries/Fun_Series_Sum_plus.con".

inline "cic:/CoRN/ftc/FunctSeries/conv_fun_series_minus.con".

inline "cic:/CoRN/ftc/FunctSeries/Fun_Series_Sum_min.con".

(*#*
%\begin{convention}% Let [c:IR].
%\end{convention}%
*)

alias id "c" = "cic:/CoRN/ftc/FunctSeries/Operations/c.var".

alias id "H" = "cic:/CoRN/ftc/FunctSeries/Operations/H.var".

alias id "contH" = "cic:/CoRN/ftc/FunctSeries/Operations/contH.var".

inline "cic:/CoRN/ftc/FunctSeries/conv_fun_series_scal.con".

inline "cic:/CoRN/ftc/FunctSeries/Fun_Series_Sum_scal.con".

(* UNEXPORTED
End Operations
*)

(* UNEXPORTED
Section More_Operations
*)

alias id "a" = "cic:/CoRN/ftc/FunctSeries/More_Operations/a.var".

alias id "b" = "cic:/CoRN/ftc/FunctSeries/More_Operations/b.var".

alias id "Hab" = "cic:/CoRN/ftc/FunctSeries/More_Operations/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/FunctSeries/More_Operations/I.con" "More_Operations__".

(* end hide *)

alias id "f" = "cic:/CoRN/ftc/FunctSeries/More_Operations/f.var".

alias id "convF" = "cic:/CoRN/ftc/FunctSeries/More_Operations/convF.var".

inline "cic:/CoRN/ftc/FunctSeries/conv_fun_series_inv.con".

inline "cic:/CoRN/ftc/FunctSeries/Fun_Series_Sum_inv.con".

(* UNEXPORTED
End More_Operations
*)

(* UNEXPORTED
Section Other_Results
*)

alias id "a" = "cic:/CoRN/ftc/FunctSeries/Other_Results/a.var".

alias id "b" = "cic:/CoRN/ftc/FunctSeries/Other_Results/b.var".

alias id "Hab" = "cic:/CoRN/ftc/FunctSeries/Other_Results/Hab.var".

alias id "f" = "cic:/CoRN/ftc/FunctSeries/Other_Results/f.var".

alias id "convF" = "cic:/CoRN/ftc/FunctSeries/Other_Results/convF.var".

(*#*
The following relate the sum series with the limit of the sequence of
partial sums; as a corollary we get the continuity of the sum of the
series.
*)

inline "cic:/CoRN/ftc/FunctSeries/Fun_Series_Sum_char'.con".

inline "cic:/CoRN/ftc/FunctSeries/fun_series_conv.con".

inline "cic:/CoRN/ftc/FunctSeries/Fun_Series_Sum_cont.con".

inline "cic:/CoRN/ftc/FunctSeries/Fun_Series_Sum_char.con".

inline "cic:/CoRN/ftc/FunctSeries/Fun_Series_Sum_as_Lim.con".

(* UNEXPORTED
End Other_Results
*)

(* UNEXPORTED
Hint Resolve Fun_Series_Sum_cont: continuous.
*)

(* UNEXPORTED
Section Convergence_Criteria
*)

(*#* **Convergence Criteria

Most of the convergence criteria for series of real numbers carry over to series of real-valued functions, so again we just present them without comments.
*)

alias id "a" = "cic:/CoRN/ftc/FunctSeries/Convergence_Criteria/a.var".

alias id "b" = "cic:/CoRN/ftc/FunctSeries/Convergence_Criteria/b.var".

alias id "Hab" = "cic:/CoRN/ftc/FunctSeries/Convergence_Criteria/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/FunctSeries/Convergence_Criteria/I.con" "Convergence_Criteria__".

(* end hide *)

alias id "f" = "cic:/CoRN/ftc/FunctSeries/Convergence_Criteria/f.var".

alias id "contF" = "cic:/CoRN/ftc/FunctSeries/Convergence_Criteria/contF.var".

(* UNEXPORTED
Opaque Frestr.
*)

(* UNEXPORTED
Transparent Frestr.
*)

(* UNEXPORTED
Opaque FAbs.
*)

(* UNEXPORTED
Transparent FAbs.
*)

(* UNEXPORTED
Opaque fun_seq_part_sum.
*)

(* UNEXPORTED
Opaque FAbs.
*)

(* UNEXPORTED
Transparent FAbs.
*)

(* UNEXPORTED
Opaque FAbs.
*)

(* UNEXPORTED
Transparent fun_seq_part_sum.
*)

(* UNEXPORTED
Opaque fun_seq_part_sum.
*)

inline "cic:/CoRN/ftc/FunctSeries/fun_str_comparison.con".

(* UNEXPORTED
Transparent FAbs.
*)

inline "cic:/CoRN/ftc/FunctSeries/fun_comparison.con".

inline "cic:/CoRN/ftc/FunctSeries/abs_imp_conv.con".

(* UNEXPORTED
Opaque FAbs.
*)

inline "cic:/CoRN/ftc/FunctSeries/fun_ratio_test_conv.con".

(* UNEXPORTED
End Convergence_Criteria
*)

