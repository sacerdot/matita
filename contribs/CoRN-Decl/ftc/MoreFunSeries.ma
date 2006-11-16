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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/MoreFunSeries".

include "CoRN.ma".

(* $Id: MoreFunSeries.v,v 1.4 2004/04/23 10:00:59 lcf Exp $ *)

include "ftc/FunctSeries.ma".

include "ftc/MoreFunctions.ma".

(*#* printing FSeries_Sum %\ensuremath{\sum_{\infty}}% #&sum;'<sub>&infin;</sub># *)

(* UNEXPORTED
Section Definitions.
*)

(*#* *More on Sequences and Series

We will now extend our convergence definitions and results for
sequences and series of functions defined in compact intervals to
arbitrary intervals.

%\begin{convention}% Throughout this file, [J] will be an interval,
[f, g] will be sequences of continuous (in [J]) functions and [F,G]
will be continuous (in [J]) functions.
%\end{convention}%

**Sequences

First we will consider the case of sequences.

***Definitions

Some of the definitions do not make sense in this more general setting
(for instance, because the norm of a function is no longer defined),
but the ones which do we simply adapt in the usual way.
*)

inline "cic:/CoRN/ftc/MoreFunSeries/J.var".

inline "cic:/CoRN/ftc/MoreFunSeries/f.var".

inline "cic:/CoRN/ftc/MoreFunSeries/F.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contf.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contF.var".

inline "cic:/CoRN/ftc/MoreFunSeries/Cauchy_fun_seq_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/conv_fun_seq_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/conv_fun_seq'_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/Cauchy_fun_seq2_IR.con".

(*#*
The equivalences between these definitions still hold.
*)

inline "cic:/CoRN/ftc/MoreFunSeries/conv_Cauchy_fun_seq'_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/Cauchy_fun_seq_seq2_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/Cauchy_fun_seq2_seq_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/Cauchy_fun_real_IR.con".

(* UNEXPORTED
End Definitions.
*)

(* UNEXPORTED
Section More_Definitions.
*)

(*#*
Limit is defined and works in the same way as before.
*)

inline "cic:/CoRN/ftc/MoreFunSeries/J.var".

inline "cic:/CoRN/ftc/MoreFunSeries/f.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contf.var".

(* begin show *)

inline "cic:/CoRN/ftc/MoreFunSeries/conv.var".

(* end show *)

inline "cic:/CoRN/ftc/MoreFunSeries/Cauchy_fun_seq_Lim_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/Cauchy_fun_seq_Lim_char.con".

(* UNEXPORTED
End More_Definitions.
*)

(* UNEXPORTED
Section Irrelevance_of_Proofs.
*)

(*#* ***Basic Properties

Proofs are irrelevant as before---they just have to be present.
*)

inline "cic:/CoRN/ftc/MoreFunSeries/J.var".

inline "cic:/CoRN/ftc/MoreFunSeries/f.var".

(* begin show *)

inline "cic:/CoRN/ftc/MoreFunSeries/contf.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contf0.var".

(* end show *)

inline "cic:/CoRN/ftc/MoreFunSeries/F.var".

(* begin show *)

inline "cic:/CoRN/ftc/MoreFunSeries/contF.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contF0.var".

(* end show *)

inline "cic:/CoRN/ftc/MoreFunSeries/conv_fun_seq'_wd_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/Cauchy_fun_seq2_wd_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/conv_fun_seq_wd_IR.con".

(* UNEXPORTED
End Irrelevance_of_Proofs.
*)

(* UNEXPORTED
Opaque Cauchy_fun_seq_Lim_IR.
*)

(* UNEXPORTED
Section More_Properties.
*)

inline "cic:/CoRN/ftc/MoreFunSeries/J.var".

inline "cic:/CoRN/ftc/MoreFunSeries/f.var".

inline "cic:/CoRN/ftc/MoreFunSeries/g.var".

(* begin show *)

inline "cic:/CoRN/ftc/MoreFunSeries/contf.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contf0.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contg.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contg0.var".

(* end show *)

inline "cic:/CoRN/ftc/MoreFunSeries/Cauchy_conv_fun_seq'_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/F.var".

inline "cic:/CoRN/ftc/MoreFunSeries/G.var".

(* begin show *)

inline "cic:/CoRN/ftc/MoreFunSeries/contF.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contF0.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contG.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contG0.var".

(* end show *)

inline "cic:/CoRN/ftc/MoreFunSeries/conv_fun_seq'_wdl_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/conv_fun_seq'_wdr_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/conv_fun_seq'_wdl'_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/conv_fun_seq'_wdr'_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/Cauchy_cont_Lim_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/Cauchy_conv_fun_seq_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/conv_Cauchy_fun_seq_IR.con".

(* UNEXPORTED
End More_Properties.
*)

(* UNEXPORTED
Hint Resolve Cauchy_cont_Lim_IR: continuous.
*)

(* UNEXPORTED
Section Algebraic_Properties.
*)

(*#* ***Algebraic Properties

Algebraic operations still work well.
*)

inline "cic:/CoRN/ftc/MoreFunSeries/J.var".

inline "cic:/CoRN/ftc/MoreFunSeries/f.var".

inline "cic:/CoRN/ftc/MoreFunSeries/g.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contf.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contg.var".

inline "cic:/CoRN/ftc/MoreFunSeries/FLim_unique_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/Cauchy_fun_seq_wd_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_Lim_seq_const_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_Cauchy_prop_const_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/F.var".

inline "cic:/CoRN/ftc/MoreFunSeries/G.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contF.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contG.var".

(* begin show *)

inline "cic:/CoRN/ftc/MoreFunSeries/convF.var".

inline "cic:/CoRN/ftc/MoreFunSeries/convG.var".

(* end show *)

inline "cic:/CoRN/ftc/MoreFunSeries/fun_Lim_seq_plus'_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_Lim_seq_minus'_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_Lim_seq_mult'_IR.con".

(* UNEXPORTED
End Algebraic_Properties.
*)

(* UNEXPORTED
Section More_Algebraic_Properties.
*)

(*#*
If we work with the limit function things fit in just as well.
*)

inline "cic:/CoRN/ftc/MoreFunSeries/J.var".

inline "cic:/CoRN/ftc/MoreFunSeries/f.var".

inline "cic:/CoRN/ftc/MoreFunSeries/g.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contf.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contg.var".

(* begin show *)

inline "cic:/CoRN/ftc/MoreFunSeries/Hf.var".

inline "cic:/CoRN/ftc/MoreFunSeries/Hg.var".

(* end show *)

inline "cic:/CoRN/ftc/MoreFunSeries/fun_Lim_seq_plus_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_Cauchy_prop_plus.con".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_Lim_seq_inv_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_Cauchy_prop_inv.con".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_Lim_seq_minus_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_Cauchy_prop_minus.con".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_Lim_seq_mult_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_Cauchy_prop_mult.con".

(* UNEXPORTED
End More_Algebraic_Properties.
*)

(* UNEXPORTED
Section Other.
*)

(*#* ***Miscellaneous

Finally, we define a mapping between sequences of real numbers and sequences of (constant) functions and prove that convergence is preserved.
*)

inline "cic:/CoRN/ftc/MoreFunSeries/seq_to_funseq.con".

inline "cic:/CoRN/ftc/MoreFunSeries/funseq_conv.con".

(*#*
Another interesting fact: if a sequence of constant functions converges then it must converge to a constant function.
*)

inline "cic:/CoRN/ftc/MoreFunSeries/fun_const_Lim.con".

(* UNEXPORTED
End Other.
*)

(* UNEXPORTED
Section Series_Definitions.
*)

(*#* **Series

We now consider series of functions defined in arbitrary intervals.

Convergence is defined as expected---through convergence in every compact interval.
*)

inline "cic:/CoRN/ftc/MoreFunSeries/J.var".

inline "cic:/CoRN/ftc/MoreFunSeries/f.var".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_series_convergent_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_series_conv_imp_conv_IR.con".

(* begin show *)

inline "cic:/CoRN/ftc/MoreFunSeries/H.var".

(* end show *)

inline "cic:/CoRN/ftc/MoreFunSeries/fun_series_inc_IR.con".

(*#* Assume [h(x)] is the pointwise series of [f(x)] *)

(* begin hide *)

inline "cic:/CoRN/ftc/MoreFunSeries/h.con".

(* end hide *)

inline "cic:/CoRN/ftc/MoreFunSeries/FSeries_Sum_strext_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/FSeries_Sum.con".

inline "cic:/CoRN/ftc/MoreFunSeries/FSeries_Sum_char.con".

(* UNEXPORTED
End Series_Definitions.
*)

(* UNEXPORTED
Implicit Arguments FSeries_Sum [J f].
*)

(* UNEXPORTED
Section More_Series_Definitions.
*)

inline "cic:/CoRN/ftc/MoreFunSeries/J.var".

inline "cic:/CoRN/ftc/MoreFunSeries/f.var".

(*#*
Absolute convergence still exists.
*)

inline "cic:/CoRN/ftc/MoreFunSeries/fun_series_abs_convergent_IR.con".

(* UNEXPORTED
End More_Series_Definitions.
*)

(* UNEXPORTED
Section Convergence_Results.
*)

(*#*
As before, any series converges to its sum.
*)

inline "cic:/CoRN/ftc/MoreFunSeries/J.var".

inline "cic:/CoRN/ftc/MoreFunSeries/f.var".

inline "cic:/CoRN/ftc/MoreFunSeries/FSeries_conv.con".

inline "cic:/CoRN/ftc/MoreFunSeries/convergent_imp_inc.con".

inline "cic:/CoRN/ftc/MoreFunSeries/convergent_imp_Continuous.con".

inline "cic:/CoRN/ftc/MoreFunSeries/Continuous_FSeries_Sum.con".

(* UNEXPORTED
End Convergence_Results.
*)

(* UNEXPORTED
Hint Resolve convergent_imp_inc: included.
*)

(* UNEXPORTED
Hint Resolve convergent_imp_Continuous Continuous_FSeries_Sum: continuous.
*)

(* UNEXPORTED
Section Operations.
*)

(*#* **Algebraic Operations

Convergence is well defined and preserved by operations.
*)

inline "cic:/CoRN/ftc/MoreFunSeries/J.var".

inline "cic:/CoRN/ftc/MoreFunSeries/conv_fun_const_series_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_const_series_Sum_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/conv_zero_fun_series_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/FSeries_Sum_zero_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/f.var".

inline "cic:/CoRN/ftc/MoreFunSeries/g.var".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_series_convergent_wd_IR.con".

(* begin show *)

inline "cic:/CoRN/ftc/MoreFunSeries/convF.var".

inline "cic:/CoRN/ftc/MoreFunSeries/convG.var".

(* end show *)

inline "cic:/CoRN/ftc/MoreFunSeries/FSeries_Sum_wd'.con".

inline "cic:/CoRN/ftc/MoreFunSeries/FSeries_Sum_plus_conv.con".

inline "cic:/CoRN/ftc/MoreFunSeries/FSeries_Sum_plus.con".

inline "cic:/CoRN/ftc/MoreFunSeries/FSeries_Sum_inv_conv.con".

inline "cic:/CoRN/ftc/MoreFunSeries/FSeries_Sum_inv.con".

inline "cic:/CoRN/ftc/MoreFunSeries/FSeries_Sum_minus_conv.con".

inline "cic:/CoRN/ftc/MoreFunSeries/FSeries_Sum_minus.con".

(*#*
%\begin{convention}% Let [c:IR] and [H:PartIR] be continuous in [J].
%\end{convention}%
*)

inline "cic:/CoRN/ftc/MoreFunSeries/c.var".

inline "cic:/CoRN/ftc/MoreFunSeries/H.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contH.var".

inline "cic:/CoRN/ftc/MoreFunSeries/FSeries_Sum_scal_conv.con".

inline "cic:/CoRN/ftc/MoreFunSeries/FSeries_Sum_scal.con".

(* UNEXPORTED
End Operations.
*)

(* UNEXPORTED
Section Convergence_Criteria.
*)

(*#* ***Convergence Criteria

The most important tests for convergence of series still apply: the
comparison test (in both versions) and the ratio test.
*)

inline "cic:/CoRN/ftc/MoreFunSeries/J.var".

inline "cic:/CoRN/ftc/MoreFunSeries/f.var".

inline "cic:/CoRN/ftc/MoreFunSeries/contF.var".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_str_comparison_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_comparison_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/abs_imp_conv_IR.con".

inline "cic:/CoRN/ftc/MoreFunSeries/fun_ratio_test_conv_IR.con".

(* UNEXPORTED
End Convergence_Criteria.
*)

(* UNEXPORTED
Section Insert_Series.
*)

(*#* ***Translation

When working in particular with power series and Taylor series, it is 
sometimes useful to ``shift'' all the terms in the series one position 
forward, that is, replacing each $f_{i+1}$#f<sub>i+1</sub># with
$f_i$#f<sub>i</sub># and inserting the null function in the first 
position.  This does not affect convergence or the sum of the series.
*)

inline "cic:/CoRN/ftc/MoreFunSeries/J.var".

inline "cic:/CoRN/ftc/MoreFunSeries/f.var".

inline "cic:/CoRN/ftc/MoreFunSeries/convF.var".

inline "cic:/CoRN/ftc/MoreFunSeries/insert_series.con".

inline "cic:/CoRN/ftc/MoreFunSeries/insert_series_cont.con".

inline "cic:/CoRN/ftc/MoreFunSeries/insert_series_sum_char.con".

inline "cic:/CoRN/ftc/MoreFunSeries/insert_series_conv.con".

inline "cic:/CoRN/ftc/MoreFunSeries/insert_series_sum.con".

(* UNEXPORTED
End Insert_Series.
*)

