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

set "baseuri" "cic:/matita/CoRN-Decl/reals/Series".

(* $Id: Series.v,v 1.6 2004/04/23 10:01:05 lcf Exp $ *)

(*#* printing seq_part_sum %\ensuremath{\sum^n}% #&sum;<sup>n</sup># *)

(*#* printing series_sum %\ensuremath{\sum_0^{\infty}}% #&sum;<sub>0</sub><sup>&infin;</sup># *)

(*#* printing pi %\ensuremath{\pi}% #&pi; *)

(* INCLUDE
CSumsReals
*)

(* INCLUDE
NRootIR
*)

(* UNEXPORTED
Section Definitions.
*)

(*#* *Series of Real Numbers
In this file we develop a theory of series of real numbers.
** Definitions

A series is simply a sequence from the natural numbers into the reals.  
To each such sequence we can assign a sequence of partial sums.

%\begin{convention}% Let [x:nat->IR].
%\end{convention}%
*)

inline cic:/CoRN/reals/Series/x.var.

inline cic:/CoRN/reals/Series/seq_part_sum.con.

(*#* 
For subsequent purposes it will be very useful to be able to write the
difference between two arbitrary elements of the sequence of partial
sums as a sum of elements of the original sequence.
*)

inline cic:/CoRN/reals/Series/seq_part_sum_n.con.

(*#* A series is convergent iff its sequence of partial Sums is a
Cauchy sequence.  To each convergent series we can assign a Sum.
*)

inline cic:/CoRN/reals/Series/convergent.con.

inline cic:/CoRN/reals/Series/series_sum.con.

(*#* Divergence can be characterized in a positive way, which will sometimes 
be useful.  We thus define divergence of sequences and series and prove the 
obvious fact that no sequence can be both convergent and divergent, whether
 considered either as a sequence or as a series.
*)

inline cic:/CoRN/reals/Series/divergent_seq.con.

inline cic:/CoRN/reals/Series/divergent.con.

inline cic:/CoRN/reals/Series/conv_imp_not_div.con.

inline cic:/CoRN/reals/Series/div_imp_not_conv.con.

inline cic:/CoRN/reals/Series/convergent_imp_not_divergent.con.

inline cic:/CoRN/reals/Series/divergent_imp_not_convergent.con.

(*#* Finally we have the well known fact that every convergent series converges 
to zero as a sequence.
*)

inline cic:/CoRN/reals/Series/series_seq_Lim.con.

inline cic:/CoRN/reals/Series/series_seq_Lim'.con.

(* UNEXPORTED
End Definitions.
*)

(* UNEXPORTED
Section More_Definitions.
*)

inline cic:/CoRN/reals/Series/x.var.

(*#* We also define absolute convergence. *)

inline cic:/CoRN/reals/Series/abs_convergent.con.

(* UNEXPORTED
End More_Definitions.
*)

(* UNEXPORTED
Section Power_Series.
*)

(*#* **Power Series

Power series are an important special case.
*)

inline cic:/CoRN/reals/Series/power_series.con.

(*#*
Specially important is the case when [c] is a positive real number
less than 1; in this case not only the power series is convergent, but
we can also compute its sum.

%\begin{convention}% Let [c] be a real number between 0 and 1.
%\end{convention}%
*)

inline cic:/CoRN/reals/Series/c.var.

inline cic:/CoRN/reals/Series/H0c.var.

inline cic:/CoRN/reals/Series/Hc1.var.

inline cic:/CoRN/reals/Series/c_exp_Lim.con.

inline cic:/CoRN/reals/Series/power_series_Lim1.con.

inline cic:/CoRN/reals/Series/power_series_conv.con.

inline cic:/CoRN/reals/Series/power_series_sum.con.

(* UNEXPORTED
End Power_Series.
*)

(* UNEXPORTED
Section Operations.
*)

(*#* **Operations

Some operations with series preserve convergence.  We start by defining 
the series that is zero everywhere.
*)

inline cic:/CoRN/reals/Series/conv_zero_series.con.

inline cic:/CoRN/reals/Series/series_sum_zero.con.

(*#* Next we consider extensionality, as well as the sum and difference 
of two convergent series.

%\begin{convention}% Let [x,y:nat->IR] be convergent series.
%\end{convention}%
*)

inline cic:/CoRN/reals/Series/x.var.

inline cic:/CoRN/reals/Series/y.var.

inline cic:/CoRN/reals/Series/convX.var.

inline cic:/CoRN/reals/Series/convY.var.

inline cic:/CoRN/reals/Series/convergent_wd.con.

inline cic:/CoRN/reals/Series/series_sum_wd.con.

inline cic:/CoRN/reals/Series/conv_series_plus.con.

inline cic:/CoRN/reals/Series/series_sum_plus.con.

inline cic:/CoRN/reals/Series/conv_series_minus.con.

inline cic:/CoRN/reals/Series/series_sum_minus.con.

(*#* Multiplication by a scalar [c] is also permitted. *)

inline cic:/CoRN/reals/Series/c.var.

inline cic:/CoRN/reals/Series/conv_series_mult_scal.con.

inline cic:/CoRN/reals/Series/series_sum_mult_scal.con.

(* UNEXPORTED
End Operations.
*)

(* UNEXPORTED
Section More_Operations.
*)

inline cic:/CoRN/reals/Series/x.var.

inline cic:/CoRN/reals/Series/convX.var.

(*#* As a corollary, we get the series of the inverses. *)

inline cic:/CoRN/reals/Series/conv_series_inv.con.

inline cic:/CoRN/reals/Series/series_sum_inv.con.

(* UNEXPORTED
End More_Operations.
*)

(* UNEXPORTED
Section Almost_Everywhere.
*)

(*#* ** Almost Everywhere

In this section we strengthen some of the convergence results for sequences 
and derive an important corollary for series.

Let [x,y : nat->IR] be equal after some natural number.
*)

inline cic:/CoRN/reals/Series/x.var.

inline cic:/CoRN/reals/Series/y.var.

inline cic:/CoRN/reals/Series/aew_eq.con.

inline cic:/CoRN/reals/Series/aew_equal.var.

inline cic:/CoRN/reals/Series/aew_Cauchy.con.

inline cic:/CoRN/reals/Series/aew_Cauchy2.con.

inline cic:/CoRN/reals/Series/aew_series_conv.con.

(* UNEXPORTED
End Almost_Everywhere.
*)

(* UNEXPORTED
Section Cauchy_Almost_Everywhere.
*)

(*#* Suppose furthermore that [x,y] are Cauchy sequences. *)

inline cic:/CoRN/reals/Series/x.var.

inline cic:/CoRN/reals/Series/y.var.

inline cic:/CoRN/reals/Series/aew_equal.var.

inline cic:/CoRN/reals/Series/aew_Lim.con.

(* UNEXPORTED
End Cauchy_Almost_Everywhere.
*)

(* UNEXPORTED
Section Convergence_Criteria.
*)

(*#* **Convergence Criteria

%\begin{convention}% Let [x:nat->IR].
%\end{convention}%
*)

inline cic:/CoRN/reals/Series/x.var.

(*#* We include the comparison test for series, both in a strong and in a less 
general (but simpler) form.
*)

inline cic:/CoRN/reals/Series/str_comparison.con.

inline cic:/CoRN/reals/Series/comparison.con.

(*#* As a corollary, we get that every absolutely convergent series converges. *)

inline cic:/CoRN/reals/Series/abs_imp_conv.con.

(*#* Next we have the ratio test, both as a positive and negative result. *)

inline cic:/CoRN/reals/Series/divergent_crit.con.

inline cic:/CoRN/reals/Series/tail_series.con.

inline cic:/CoRN/reals/Series/join_series.con.

(* UNEXPORTED
End Convergence_Criteria.
*)

(* UNEXPORTED
Section More_CC.
*)

inline cic:/CoRN/reals/Series/x.var.

inline cic:/CoRN/reals/Series/ratio_test_conv.con.

inline cic:/CoRN/reals/Series/ratio_test_div.con.

(* UNEXPORTED
End More_CC.
*)

(* UNEXPORTED
Section Alternate_Series.
*)

(*#* **Alternate Series

Alternate series are a special case.  Suppose that [x] is nonnegative and 
decreasing convergent to 0.
*)

inline cic:/CoRN/reals/Series/x.var.

inline cic:/CoRN/reals/Series/pos_x.var.

inline cic:/CoRN/reals/Series/Lim_x.var.

inline cic:/CoRN/reals/Series/mon_x.var.

(* begin hide *)

inline cic:/CoRN/reals/Series/y.con.

inline cic:/CoRN/reals/Series/alternate_lemma1.con.

inline cic:/CoRN/reals/Series/alternate_lemma2.con.

inline cic:/CoRN/reals/Series/alternate_lemma3.con.

inline cic:/CoRN/reals/Series/alternate_lemma4.con.

(* end hide *)

inline cic:/CoRN/reals/Series/alternate_series_conv.con.

(* UNEXPORTED
End Alternate_Series.
*)

(* UNEXPORTED
Section Important_Numbers.
*)

(*#* **Important Numbers

We end this chapter by defining two important numbers in mathematics: [pi]
and $e$#e#, both as sums of convergent series.
*)

inline cic:/CoRN/reals/Series/e_series.con.

inline cic:/CoRN/reals/Series/e_series_conv.con.

inline cic:/CoRN/reals/Series/E.con.

inline cic:/CoRN/reals/Series/pi_series.con.

inline cic:/CoRN/reals/Series/pi_series_conv.con.

inline cic:/CoRN/reals/Series/pi.con.

(* UNEXPORTED
End Important_Numbers.
*)

