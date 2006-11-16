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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/FunctSequence".

include "CoRN_notation.ma".

(* $Id: FunctSequence.v,v 1.5 2004/04/23 10:00:58 lcf Exp $ *)

include "ftc/Continuity.ma".

include "ftc/PartInterval.ma".

(* UNEXPORTED
Section Definitions.
*)

(*#* *Sequences of Functions

In this file we define some more operators on functions, namely
sequences and limits.  These concepts are defined only for continuous
functions.

%\begin{convention}% Throughout this section:
 - [a] and [b] will be real numbers and the interval [[a,b]]
will be denoted by [I];
 - [f, g] and [h] will denote sequences of continuous functions;
 - [F, G] and [H] will denote continuous functions.

%\end{convention}%

**Definitions

A sequence of functions is simply an object of type [nat->PartIR].
However, we will be interested mostly in convergent and Cauchy
sequences.  Several definitions of these concepts will be formalized;
they mirror the several different ways in which a Cauchy sequence can
be defined.  For a discussion on the different notions of convergent
see Bishop 1967.
*)

inline "cic:/CoRN/ftc/FunctSequence/a.var".

inline "cic:/CoRN/ftc/FunctSequence/b.var".

inline "cic:/CoRN/ftc/FunctSequence/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/FunctSequence/I.con".

(* end hide *)

inline "cic:/CoRN/ftc/FunctSequence/f.var".

inline "cic:/CoRN/ftc/FunctSequence/F.var".

inline "cic:/CoRN/ftc/FunctSequence/contf.var".

inline "cic:/CoRN/ftc/FunctSequence/contF.var".

(* begin hide *)

inline "cic:/CoRN/ftc/FunctSequence/incf.con".

inline "cic:/CoRN/ftc/FunctSequence/incF.con".

(* end hide *)

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq.con".

inline "cic:/CoRN/ftc/FunctSequence/conv_fun_seq'.con".

inline "cic:/CoRN/ftc/FunctSequence/conv_norm_fun_seq.con".

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq1.con".

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq'.con".

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq2.con".

(*#*
These definitions are all shown to be equivalent.
*)

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq_seq'.con".

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq'_seq.con".

inline "cic:/CoRN/ftc/FunctSequence/conv_Cauchy_fun_seq'.con".

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq_seq2.con".

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq2_seq.con".

inline "cic:/CoRN/ftc/FunctSequence/conv_fun_seq'_norm.con".

inline "cic:/CoRN/ftc/FunctSequence/conv_fun_norm_seq.con".

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq1_seq'.con".

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq'_seq1.con".

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq_seq1.con".

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq1_seq.con".

(*#*
A Cauchy sequence of functions is pointwise a Cauchy sequence.
*)

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_real.con".

(* UNEXPORTED
End Definitions.
*)

(* UNEXPORTED
Section More_Definitions.
*)

inline "cic:/CoRN/ftc/FunctSequence/a.var".

inline "cic:/CoRN/ftc/FunctSequence/b.var".

inline "cic:/CoRN/ftc/FunctSequence/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/FunctSequence/I.con".

(* end hide *)

inline "cic:/CoRN/ftc/FunctSequence/f.var".

inline "cic:/CoRN/ftc/FunctSequence/contf.var".

(*#*
We can also say that [f] is simply convergent if it converges to some
continuous function.  Notice that we do not quantify directly over
partial functions, for reasons which were already explained.
*)

inline "cic:/CoRN/ftc/FunctSequence/conv_fun_seq.con".

(*#*
It is useful to extract the limit as a partial function:
*)

(* begin show *)

inline "cic:/CoRN/ftc/FunctSequence/H.var".

(* end show *)

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq_Lim.con".

(* UNEXPORTED
End More_Definitions.
*)

(* UNEXPORTED
Section Irrelevance_of_Proofs.
*)

(*#* **Irrelevance of Proofs

This section contains a number of technical results stating mainly that being a Cauchy sequence or converging to some limit is a property of the sequence itself and independent of the proofs we supply of its continuity or the continuity of its limit.
*)

inline "cic:/CoRN/ftc/FunctSequence/a.var".

inline "cic:/CoRN/ftc/FunctSequence/b.var".

inline "cic:/CoRN/ftc/FunctSequence/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/FunctSequence/I.con".

(* end hide *)

inline "cic:/CoRN/ftc/FunctSequence/f.var".

(* begin show *)

inline "cic:/CoRN/ftc/FunctSequence/contf.var".

inline "cic:/CoRN/ftc/FunctSequence/contf0.var".

(* end show *)

inline "cic:/CoRN/ftc/FunctSequence/F.var".

(* begin show *)

inline "cic:/CoRN/ftc/FunctSequence/contF.var".

inline "cic:/CoRN/ftc/FunctSequence/contF0.var".

(* end show *)

inline "cic:/CoRN/ftc/FunctSequence/conv_fun_seq'_wd.con".

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq'_wd.con".

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq2_wd.con".

inline "cic:/CoRN/ftc/FunctSequence/conv_norm_fun_seq_wd.con".

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq1_wd.con".

(* UNEXPORTED
End Irrelevance_of_Proofs.
*)

(* UNEXPORTED
Section More_Proof_Irrelevance.
*)

inline "cic:/CoRN/ftc/FunctSequence/conv_fun_seq_wd.con".

(* UNEXPORTED
End More_Proof_Irrelevance.
*)

(* UNEXPORTED
Section More_Properties.
*)

(*#* **Other Properties

Still more technical details---a convergent sequence converges to its
limit; the limit is a continuous function; and convergence is well
defined with respect to functional equality in the interval [[a,b]].
*)

inline "cic:/CoRN/ftc/FunctSequence/a.var".

inline "cic:/CoRN/ftc/FunctSequence/b.var".

inline "cic:/CoRN/ftc/FunctSequence/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/FunctSequence/I.con".

(* end hide *)

inline "cic:/CoRN/ftc/FunctSequence/f.var".

inline "cic:/CoRN/ftc/FunctSequence/g.var".

(* begin show *)

inline "cic:/CoRN/ftc/FunctSequence/contf.var".

inline "cic:/CoRN/ftc/FunctSequence/contf0.var".

inline "cic:/CoRN/ftc/FunctSequence/contg.var".

inline "cic:/CoRN/ftc/FunctSequence/contg0.var".

(* end show *)

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_conv_fun_seq'.con".

inline "cic:/CoRN/ftc/FunctSequence/F.var".

inline "cic:/CoRN/ftc/FunctSequence/G.var".

(* begin show *)

inline "cic:/CoRN/ftc/FunctSequence/contF.var".

inline "cic:/CoRN/ftc/FunctSequence/contF0.var".

inline "cic:/CoRN/ftc/FunctSequence/contG.var".

inline "cic:/CoRN/ftc/FunctSequence/contG0.var".

(* end show *)

inline "cic:/CoRN/ftc/FunctSequence/conv_fun_seq'_wdl.con".

inline "cic:/CoRN/ftc/FunctSequence/conv_fun_seq'_wdr.con".

inline "cic:/CoRN/ftc/FunctSequence/conv_fun_seq'_wdl'.con".

inline "cic:/CoRN/ftc/FunctSequence/conv_fun_seq'_wdr'.con".

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_fun_seq_wd.con".

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_cont_Lim.con".

inline "cic:/CoRN/ftc/FunctSequence/Cauchy_conv_fun_seq.con".

inline "cic:/CoRN/ftc/FunctSequence/conv_Cauchy_fun_seq.con".

(*#*
More interesting is the fact that a convergent sequence of functions converges pointwise as a sequence of real numbers.
*)

inline "cic:/CoRN/ftc/FunctSequence/fun_conv_imp_seq_conv.con".

(*#*
And a sequence of real numbers converges iff the corresponding sequence of constant functions converges to the corresponding constant function.
*)

inline "cic:/CoRN/ftc/FunctSequence/seq_conv_imp_fun_conv.con".

(* UNEXPORTED
End More_Properties.
*)

(* UNEXPORTED
Hint Resolve Cauchy_cont_Lim: continuous.
*)

(* UNEXPORTED
Section Algebraic_Properties.
*)

(*#* **Algebraic Properties

We now study how convergence is affected by algebraic operations, and some algebraic properties of the limit function.
*)

inline "cic:/CoRN/ftc/FunctSequence/a.var".

inline "cic:/CoRN/ftc/FunctSequence/b.var".

inline "cic:/CoRN/ftc/FunctSequence/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/FunctSequence/I.con".

(* end hide *)

inline "cic:/CoRN/ftc/FunctSequence/f.var".

inline "cic:/CoRN/ftc/FunctSequence/g.var".

inline "cic:/CoRN/ftc/FunctSequence/contf.var".

inline "cic:/CoRN/ftc/FunctSequence/contg.var".

(*#*
First, the limit function is unique.
*)

inline "cic:/CoRN/ftc/FunctSequence/FLim_unique.con".

(*#* Constant sequences (not sequences of constant functions!) always converge.
*)

inline "cic:/CoRN/ftc/FunctSequence/fun_Lim_seq_const.con".

inline "cic:/CoRN/ftc/FunctSequence/fun_Cauchy_prop_const.con".

(*#*
We now prove that if two sequences converge than their sum (difference, product) also converge to the sum (difference, product) of their limits.
*)

inline "cic:/CoRN/ftc/FunctSequence/F.var".

inline "cic:/CoRN/ftc/FunctSequence/G.var".

inline "cic:/CoRN/ftc/FunctSequence/contF.var".

inline "cic:/CoRN/ftc/FunctSequence/contG.var".

(* begin show *)

inline "cic:/CoRN/ftc/FunctSequence/convF.var".

inline "cic:/CoRN/ftc/FunctSequence/convG.var".

(* end show *)

(* begin hide *)

inline "cic:/CoRN/ftc/FunctSequence/incf.con".

inline "cic:/CoRN/ftc/FunctSequence/incg.con".

inline "cic:/CoRN/ftc/FunctSequence/incF.con".

inline "cic:/CoRN/ftc/FunctSequence/incG.con".

(* end hide *)

inline "cic:/CoRN/ftc/FunctSequence/fun_Lim_seq_plus'.con".

inline "cic:/CoRN/ftc/FunctSequence/fun_Lim_seq_minus'.con".

inline "cic:/CoRN/ftc/FunctSequence/fun_Lim_seq_mult'.con".

(* UNEXPORTED
End Algebraic_Properties.
*)

(* UNEXPORTED
Section More_Algebraic_Properties.
*)

inline "cic:/CoRN/ftc/FunctSequence/a.var".

inline "cic:/CoRN/ftc/FunctSequence/b.var".

inline "cic:/CoRN/ftc/FunctSequence/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/FunctSequence/I.con".

(* end hide *)

inline "cic:/CoRN/ftc/FunctSequence/f.var".

inline "cic:/CoRN/ftc/FunctSequence/g.var".

inline "cic:/CoRN/ftc/FunctSequence/contf.var".

inline "cic:/CoRN/ftc/FunctSequence/contg.var".

(*#*
The same is true if we don't make the limits explicit.
*)

(* begin hide *)

inline "cic:/CoRN/ftc/FunctSequence/Hf.var".

inline "cic:/CoRN/ftc/FunctSequence/Hg.var".

(* end hide *)

inline "cic:/CoRN/ftc/FunctSequence/fun_Lim_seq_plus.con".

inline "cic:/CoRN/ftc/FunctSequence/fun_Cauchy_prop_plus.con".

inline "cic:/CoRN/ftc/FunctSequence/fun_Lim_seq_minus.con".

inline "cic:/CoRN/ftc/FunctSequence/fun_Cauchy_prop_minus.con".

inline "cic:/CoRN/ftc/FunctSequence/fun_Lim_seq_mult.con".

inline "cic:/CoRN/ftc/FunctSequence/fun_Cauchy_prop_mult.con".

(* UNEXPORTED
End More_Algebraic_Properties.
*)

(* UNEXPORTED
Section Still_More_Algebraic_Properties.
*)

inline "cic:/CoRN/ftc/FunctSequence/a.var".

inline "cic:/CoRN/ftc/FunctSequence/b.var".

inline "cic:/CoRN/ftc/FunctSequence/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/FunctSequence/I.con".

(* end hide *)

inline "cic:/CoRN/ftc/FunctSequence/f.var".

inline "cic:/CoRN/ftc/FunctSequence/contf.var".

inline "cic:/CoRN/ftc/FunctSequence/Hf.var".

(*#*
As a corollary, we get the analogous property for the sequence of algebraic inverse functions.
*)

inline "cic:/CoRN/ftc/FunctSequence/fun_Lim_seq_inv.con".

inline "cic:/CoRN/ftc/FunctSequence/fun_Cauchy_prop_inv.con".

(* UNEXPORTED
End Still_More_Algebraic_Properties.
*)

(* UNEXPORTED
Hint Resolve Continuous_I_Sum Continuous_I_Sumx Continuous_I_Sum0: continuous.
*)

