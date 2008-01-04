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

set "baseuri" "cic:/matita/CoRN-Decl/algebra/CSums".

include "CoRN.ma".

(* $Id: CSums.v,v 1.8 2004/04/23 10:00:54 lcf Exp $ *)

(*#* printing Sum0 %\ensuremath{\sum_0}% #&sum;<sub>0</sub># *)

(*#* printing Sum1 %\ensuremath{\sum_1}% #&sum;<sub>1</sub># *)

(*#* printing Sum2 %\ensuremath{\sum_2}% #&sum;<sub>2</sub># *)

(*#* printing Sum %\ensuremath{\sum}% #&sum;# *)

(*#* printing Sumx %\ensuremath{\sum'}% #&sum;'&*)

include "algebra/CAbGroups.ma".

(*#* * Sums

%\begin{convention}% Let [G] be an abelian group.
%\end{convention}%
*)

(* UNEXPORTED
Section Sums
*)

alias id "G" = "cic:/CoRN/algebra/CSums/Sums/G.var".

(* Sum1 and Sum use subtraction *)

inline "cic:/CoRN/algebra/CSums/Sumlist.con".

inline "cic:/CoRN/algebra/CSums/Sumx.con".

(*#*
It is sometimes useful to view a function defined on $\{0,\ldots,i-1\}$
#{0, ... i-1}# as a function on the natural numbers which evaluates to
[Zero] when the input is greater than or equal to [i].
*)

inline "cic:/CoRN/algebra/CSums/part_tot_nat_fun.con".

inline "cic:/CoRN/algebra/CSums/part_tot_nat_fun_ch1.con".

inline "cic:/CoRN/algebra/CSums/part_tot_nat_fun_ch2.con".

(*#* [Sum0] defines the sum for [i=0..(n-1)] *)

inline "cic:/CoRN/algebra/CSums/Sum0.con".

(*#* [Sum1] defines the sum for [i=m..(n-1)] *)

inline "cic:/CoRN/algebra/CSums/Sum1.con".

inline "cic:/CoRN/algebra/CSums/Sum.con".

(* Sum i=m..n *)

(*#* [Sum2] is similar to [Sum1], but does not require the summand to be
defined outside where it is being added. *)

inline "cic:/CoRN/algebra/CSums/Sum2.con".

inline "cic:/CoRN/algebra/CSums/Sum_one.con".

(* UNEXPORTED
Hint Resolve Sum_one: algebra.
*)

inline "cic:/CoRN/algebra/CSums/Sum_empty.con".

(* UNEXPORTED
Hint Resolve Sum_empty: algebra.
*)

inline "cic:/CoRN/algebra/CSums/Sum_Sum.con".

(* UNEXPORTED
Hint Resolve Sum_Sum: algebra.
*)

inline "cic:/CoRN/algebra/CSums/Sum_first.con".

inline "cic:/CoRN/algebra/CSums/Sum_last.con".

(* UNEXPORTED
Hint Resolve Sum_last: algebra.
*)

inline "cic:/CoRN/algebra/CSums/Sum_last'.con".

(*#*
We add some extensionality results which will be quite useful
when working with integration.
*)

inline "cic:/CoRN/algebra/CSums/Sum0_strext.con".

inline "cic:/CoRN/algebra/CSums/Sum_strext.con".

inline "cic:/CoRN/algebra/CSums/Sumx_strext.con".

inline "cic:/CoRN/algebra/CSums/Sum0_strext'.con".

inline "cic:/CoRN/algebra/CSums/Sum_strext'.con".

inline "cic:/CoRN/algebra/CSums/Sum0_wd.con".

inline "cic:/CoRN/algebra/CSums/Sum_wd.con".

inline "cic:/CoRN/algebra/CSums/Sumx_wd.con".

inline "cic:/CoRN/algebra/CSums/Sum_wd'.con".

inline "cic:/CoRN/algebra/CSums/Sum2_wd.con".

inline "cic:/CoRN/algebra/CSums/Sum0_plus_Sum0.con".

(* UNEXPORTED
Hint Resolve Sum0_plus_Sum0: algebra.
*)

inline "cic:/CoRN/algebra/CSums/Sum_plus_Sum.con".

inline "cic:/CoRN/algebra/CSums/Sumx_plus_Sumx.con".

inline "cic:/CoRN/algebra/CSums/Sum2_plus_Sum2.con".

inline "cic:/CoRN/algebra/CSums/inv_Sum0.con".

(* UNEXPORTED
Hint Resolve inv_Sum0: algebra.
*)

inline "cic:/CoRN/algebra/CSums/inv_Sum.con".

(* UNEXPORTED
Hint Resolve inv_Sum: algebra.
*)

inline "cic:/CoRN/algebra/CSums/inv_Sumx.con".

inline "cic:/CoRN/algebra/CSums/inv_Sum2.con".

inline "cic:/CoRN/algebra/CSums/Sum_minus_Sum.con".

(* UNEXPORTED
Hint Resolve Sum_minus_Sum: algebra.
*)

inline "cic:/CoRN/algebra/CSums/Sumx_minus_Sumx.con".

inline "cic:/CoRN/algebra/CSums/Sum2_minus_Sum2.con".

inline "cic:/CoRN/algebra/CSums/Sum_apzero.con".

inline "cic:/CoRN/algebra/CSums/Sum_zero.con".

inline "cic:/CoRN/algebra/CSums/Sum_term.con".

inline "cic:/CoRN/algebra/CSums/Sum0_shift.con".

(* UNEXPORTED
Hint Resolve Sum0_shift: algebra.
*)

inline "cic:/CoRN/algebra/CSums/Sum_shift.con".

inline "cic:/CoRN/algebra/CSums/Sum_big_shift.con".

inline "cic:/CoRN/algebra/CSums/Sumx_Sum0.con".

(* UNEXPORTED
End Sums
*)

(* UNEXPORTED
Implicit Arguments Sum [G].
*)

(* UNEXPORTED
Implicit Arguments Sum0 [G].
*)

(* UNEXPORTED
Implicit Arguments Sumx [G n].
*)

(* UNEXPORTED
Implicit Arguments Sum2 [G m n].
*)

(*#*
The next results are useful for calculating some special sums,
often referred to as ``Mengolli Sums''.
%\begin{convention}% Let [G] be an abelian group.
%\end{convention}%
*)

(* UNEXPORTED
Section More_Sums
*)

alias id "G" = "cic:/CoRN/algebra/CSums/More_Sums/G.var".

inline "cic:/CoRN/algebra/CSums/Mengolli_Sum.con".

inline "cic:/CoRN/algebra/CSums/Mengolli_Sum_gen.con".

inline "cic:/CoRN/algebra/CSums/str_Mengolli_Sum_gen.con".

inline "cic:/CoRN/algebra/CSums/Sumx_to_Sum.con".

(* UNEXPORTED
End More_Sums
*)

(* UNEXPORTED
Hint Resolve Sum_one Sum_Sum Sum_first Sum_last Sum_last' Sum_wd
  Sum_plus_Sum: algebra.
*)

(* UNEXPORTED
Hint Resolve Sum_minus_Sum inv_Sum inv_Sum0: algebra.
*)

