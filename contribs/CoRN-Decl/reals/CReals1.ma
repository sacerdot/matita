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

set "baseuri" "cic:/matita/CoRN-Decl/reals/CReals1".

include "CoRN.ma".

(* $Id: CReals1.v,v 1.4 2004/04/23 10:01:04 lcf Exp $ *)

include "reals/Max_AbsIR.ma".

include "algebra/Expon.ma".

include "algebra/CPoly_ApZero.ma".

(* UNEXPORTED
Section More_Cauchy_Props
*)

(*#* **Miscellaneous
*** More properties of Cauchy sequences
We will now define some special Cauchy sequences and prove some 
more useful properties about them.

The sequence defined by $x_n=\frac2{n+1}$#x(n)=2/(n+1)#.
*)

inline "cic:/CoRN/reals/CReals1/twice_inv_seq_Lim.con".

inline "cic:/CoRN/reals/CReals1/twice_inv_seq.con".

(*#* 
Next, we prove that the sequence of absolute values of a Cauchy 
sequence is also Cauchy.
*)

inline "cic:/CoRN/reals/CReals1/Cauchy_Lim_abs.con".

inline "cic:/CoRN/reals/CReals1/Cauchy_abs.con".

inline "cic:/CoRN/reals/CReals1/Lim_abs.con".

(* UNEXPORTED
End More_Cauchy_Props
*)

(* UNEXPORTED
Section Subsequences
*)

(*#* *** Subsequences
We will now examine (although without formalizing it) the concept 
of subsequence and some of its properties.

%\begin{convention}% Let [seq1,seq2:nat->IR].
%\end{convention}%

In order for [seq1] to be a subsequence of [seq2], there must be an
increasing function [f] growing to infinity such that
[forall (n :nat), (seq1 n) [=] (seq2 (f n))].  We assume [f] to be such a
function.

Finally, for some of our results it is important to assume that 
[seq2] is monotonous.
*)

alias id "seq1" = "cic:/CoRN/reals/CReals1/Subsequences/seq1.var".

alias id "seq2" = "cic:/CoRN/reals/CReals1/Subsequences/seq2.var".

alias id "f" = "cic:/CoRN/reals/CReals1/Subsequences/f.var".

alias id "monF" = "cic:/CoRN/reals/CReals1/Subsequences/monF.var".

alias id "crescF" = "cic:/CoRN/reals/CReals1/Subsequences/crescF.var".

alias id "subseq" = "cic:/CoRN/reals/CReals1/Subsequences/subseq.var".

alias id "mon_seq2" = "cic:/CoRN/reals/CReals1/Subsequences/mon_seq2.var".

inline "cic:/CoRN/reals/CReals1/unbnd_f.con".

(* begin hide *)

inline "cic:/CoRN/reals/CReals1/Subsequences/mon_F'.con" "Subsequences__".

(* end hide *)

inline "cic:/CoRN/reals/CReals1/conv_subseq_imp_conv_seq.con".

inline "cic:/CoRN/reals/CReals1/Cprop2_seq_imp_Cprop2_subseq.con".

inline "cic:/CoRN/reals/CReals1/conv_seq_imp_conv_subseq.con".

inline "cic:/CoRN/reals/CReals1/Cprop2_subseq_imp_Cprop2_seq.con".

(* UNEXPORTED
End Subsequences
*)

(* UNEXPORTED
Section Cauchy_Subsequences
*)

alias id "seq1" = "cic:/CoRN/reals/CReals1/Cauchy_Subsequences/seq1.var".

alias id "seq2" = "cic:/CoRN/reals/CReals1/Cauchy_Subsequences/seq2.var".

alias id "f" = "cic:/CoRN/reals/CReals1/Cauchy_Subsequences/f.var".

alias id "monF" = "cic:/CoRN/reals/CReals1/Cauchy_Subsequences/monF.var".

alias id "crescF" = "cic:/CoRN/reals/CReals1/Cauchy_Subsequences/crescF.var".

alias id "subseq" = "cic:/CoRN/reals/CReals1/Cauchy_Subsequences/subseq.var".

alias id "mon_seq2" = "cic:/CoRN/reals/CReals1/Cauchy_Subsequences/mon_seq2.var".

inline "cic:/CoRN/reals/CReals1/Lim_seq_eq_Lim_subseq.con".

inline "cic:/CoRN/reals/CReals1/Lim_subseq_eq_Lim_seq.con".

(* UNEXPORTED
End Cauchy_Subsequences
*)

(* UNEXPORTED
Section Properties_of_Exponentiation
*)

(*#* *** More properties of Exponentiation

Finally, we prove that [x[^]n] grows to infinity if [x [>] One].
*)

inline "cic:/CoRN/reals/CReals1/power_big'.con".

inline "cic:/CoRN/reals/CReals1/power_big.con".

inline "cic:/CoRN/reals/CReals1/qi_yields_zero.con".

inline "cic:/CoRN/reals/CReals1/qi_lim_zero.con".

(* UNEXPORTED
End Properties_of_Exponentiation
*)

(*#* *** [IR] has characteristic zero *)

inline "cic:/CoRN/reals/CReals1/char0_IR.con".

inline "cic:/CoRN/reals/CReals1/poly_apzero_IR.con".

inline "cic:/CoRN/reals/CReals1/poly_IR_extensional.con".

