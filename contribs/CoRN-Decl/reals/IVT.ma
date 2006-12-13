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

set "baseuri" "cic:/matita/CoRN-Decl/reals/IVT".

include "CoRN.ma".

(* $Id: IVT.v,v 1.5 2004/04/23 10:01:04 lcf Exp $ *)

include "reals/CPoly_Contin.ma".

(* UNEXPORTED
Section Nested_Intervals
*)

(*#* * Intermediate Value Theorem

** Nested intervals

%\begin{convention}% Let [a,b:nat->IR] be sequences such that:
- [a] is increasing;
- [b] is decreasing;
- [forall (i:nat), (a i) [<] (b i)];
- for every positive real number [eps], there is an [i] such that [(b i) [<] (a i) [+]eps].

%\end{convention}%
*)

alias id "a" = "cic:/CoRN/reals/IVT/Nested_Intervals/a.var".

alias id "b" = "cic:/CoRN/reals/IVT/Nested_Intervals/b.var".

alias id "a_mon" = "cic:/CoRN/reals/IVT/Nested_Intervals/a_mon.var".

alias id "b_mon" = "cic:/CoRN/reals/IVT/Nested_Intervals/b_mon.var".

alias id "a_b" = "cic:/CoRN/reals/IVT/Nested_Intervals/a_b.var".

alias id "b_a" = "cic:/CoRN/reals/IVT/Nested_Intervals/b_a.var".

inline "cic:/CoRN/reals/IVT/a_mon'.con".

inline "cic:/CoRN/reals/IVT/b_mon'.con".

inline "cic:/CoRN/reals/IVT/a_b'.con".

inline "cic:/CoRN/reals/IVT/intervals_cauchy.con".

(* begin hide *)

inline "cic:/CoRN/reals/IVT/Nested_Intervals/a'.con" "Nested_Intervals__".

(* end hide *)

inline "cic:/CoRN/reals/IVT/Cnested_intervals_limit.con".

(*#* %\begin{convention}% Let [f] be a continuous real function.
%\end{convention}%
*)

alias id "f" = "cic:/CoRN/reals/IVT/Nested_Intervals/f.var".

alias id "f_contin" = "cic:/CoRN/reals/IVT/Nested_Intervals/f_contin.var".

inline "cic:/CoRN/reals/IVT/f_contin_pos.con".

inline "cic:/CoRN/reals/IVT/f_contin_neg.con".

(*#* Assume also that [forall i, f (a i) [<=] Zero [<=] f (b i)]. *)

alias id "f_a" = "cic:/CoRN/reals/IVT/Nested_Intervals/f_a.var".

alias id "f_b" = "cic:/CoRN/reals/IVT/Nested_Intervals/f_b.var".

inline "cic:/CoRN/reals/IVT/Cnested_intervals_zero.con".

(* UNEXPORTED
End Nested_Intervals
*)

(* UNEXPORTED
Section Bisection
*)

(*#* ** Bissections *)

alias id "f" = "cic:/CoRN/reals/IVT/Bisection/f.var".

alias id "f_apzero_interval" = "cic:/CoRN/reals/IVT/Bisection/f_apzero_interval.var".

alias id "a" = "cic:/CoRN/reals/IVT/Bisection/a.var".

alias id "b" = "cic:/CoRN/reals/IVT/Bisection/b.var".

alias id "a_b" = "cic:/CoRN/reals/IVT/Bisection/a_b.var".

alias id "f_a" = "cic:/CoRN/reals/IVT/Bisection/f_a.var".

alias id "f_b" = "cic:/CoRN/reals/IVT/Bisection/f_b.var".

(*#*
%\begin{convention}% Let [Small] denote [Two[/]ThreeNZ], [lft] be [(Two[*]a[+]b) [/]ThreeNZ] and [rht] be [(a[+]Two[*]b) [/]ThreeNZ].
%\end{convention}%
*)

(* begin hide *)

inline "cic:/CoRN/reals/IVT/Bisection/Small.con" "Bisection__".

inline "cic:/CoRN/reals/IVT/Bisection/lft.con" "Bisection__".

inline "cic:/CoRN/reals/IVT/Bisection/rht.con" "Bisection__".

(* end hide *)

inline "cic:/CoRN/reals/IVT/a_lft.con".

inline "cic:/CoRN/reals/IVT/rht_b.con".

inline "cic:/CoRN/reals/IVT/lft_rht.con".

inline "cic:/CoRN/reals/IVT/smaller_lft.con".

inline "cic:/CoRN/reals/IVT/smaller_rht.con".

(* UNEXPORTED
Hint Resolve smaller_lft smaller_rht: algebra.
*)

inline "cic:/CoRN/reals/IVT/Cbisect'.con".

(* UNEXPORTED
End Bisection
*)

(* UNEXPORTED
Section Bisect_Interval
*)

alias id "f" = "cic:/CoRN/reals/IVT/Bisect_Interval/f.var".

alias id "C_f_apzero_interval" = "cic:/CoRN/reals/IVT/Bisect_Interval/C_f_apzero_interval.var".

(* begin hide *)

inline "cic:/CoRN/reals/IVT/Bisect_Interval/Small.con" "Bisect_Interval__".

(* end hide *)

inline "cic:/CoRN/reals/IVT/bisect_interval.ind".

inline "cic:/CoRN/reals/IVT/Cbisect_exists.con".

inline "cic:/CoRN/reals/IVT/bisect.con".

inline "cic:/CoRN/reals/IVT/bisect_prop.con".

(* UNEXPORTED
End Bisect_Interval
*)

(* UNEXPORTED
Section IVT_Op
*)

(*#* ** IVT for operations
Same conventions as before.
*)

alias id "f" = "cic:/CoRN/reals/IVT/IVT_Op/f.var".

alias id "f_contin" = "cic:/CoRN/reals/IVT/IVT_Op/f_contin.var".

alias id "f_apzero_interval" = "cic:/CoRN/reals/IVT/IVT_Op/f_apzero_interval.var".

alias id "a" = "cic:/CoRN/reals/IVT/IVT_Op/a.var".

alias id "b" = "cic:/CoRN/reals/IVT/IVT_Op/b.var".

alias id "a_b" = "cic:/CoRN/reals/IVT/IVT_Op/a_b.var".

alias id "f_a" = "cic:/CoRN/reals/IVT/IVT_Op/f_a.var".

alias id "f_b" = "cic:/CoRN/reals/IVT/IVT_Op/f_b.var".

(* begin hide *)

inline "cic:/CoRN/reals/IVT/IVT_Op/Small.con" "IVT_Op__".

(* end hide *)

inline "cic:/CoRN/reals/IVT/interval_sequence.con".

inline "cic:/CoRN/reals/IVT/IVT_Op/a_.con" "IVT_Op__".

inline "cic:/CoRN/reals/IVT/IVT_Op/b_.con" "IVT_Op__".

inline "cic:/CoRN/reals/IVT/intervals_smaller.con".

inline "cic:/CoRN/reals/IVT/intervals_small''.con".

inline "cic:/CoRN/reals/IVT/intervals_small'.con".

inline "cic:/CoRN/reals/IVT/intervals_small.con".

inline "cic:/CoRN/reals/IVT/Civt_op.con".

(* UNEXPORTED
End IVT_Op
*)

(* UNEXPORTED
Section IVT_Poly
*)

(*#* ** IVT for polynomials *)

inline "cic:/CoRN/reals/IVT/Civt_poly.con".

(* UNEXPORTED
End IVT_Poly
*)

