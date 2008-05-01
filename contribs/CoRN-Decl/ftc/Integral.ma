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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/Integral".

include "CoRN.ma".

(* $Id: Integral.v,v 1.10 2004/04/23 10:00:59 lcf Exp $ *)

include "ftc/RefLemma.ma".

(*#* printing integral %\ensuremath{\int_I}% #&int;<sub>I</sub># *)

(*#* printing Integral %\ensuremath{\int_I}% #&int;<sub>I</sub># *)

(* begin hide *)

(* UNEXPORTED
Section Lemmas
*)

inline "cic:/CoRN/ftc/Integral/Lemmas/Sumx_wd_weird.con" "Lemmas__".

inline "cic:/CoRN/ftc/Integral/Sumx_weird_lemma.con".

(* UNEXPORTED
End Lemmas
*)

(* end hide *)

(* UNEXPORTED
Section Integral
*)

(*#* *Integral

Having proved the main properties of partitions and refinements, we
will define the integral of a continuous function [F] in the interval
[[a,b]] as the limit of the sequence of Sums of $F$ for even
partitions of increasing number of points.

%\begin{convention}% All throughout, [a,b] will be real numbers, the
interval [[a,b]] will be denoted by [I] and [F,G] will be
continuous functions in [I].
%\end{convention}%
*)

alias id "a" = "cic:/CoRN/ftc/Integral/Integral/a.var".

alias id "b" = "cic:/CoRN/ftc/Integral/Integral/b.var".

alias id "Hab" = "cic:/CoRN/ftc/Integral/Integral/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Integral/Integral/I.con" "Integral__".

alias id "F" = "cic:/CoRN/ftc/Integral/Integral/F.var".

alias id "contF" = "cic:/CoRN/ftc/Integral/Integral/contF.var".

inline "cic:/CoRN/ftc/Integral/Integral/contF'.con" "Integral__".

(* end hide *)

(* UNEXPORTED
Section Darboux_Sum
*)

inline "cic:/CoRN/ftc/Integral/integral_seq.con".

inline "cic:/CoRN/ftc/Integral/Cauchy_Darboux_Seq.con".

inline "cic:/CoRN/ftc/Integral/integral.con".

(* UNEXPORTED
End Darboux_Sum
*)

(* UNEXPORTED
Section Integral_Thm
*)

(*#*
The following shows that in fact the integral of [F] is the limit of
any sequence of partitions of mesh converging to 0.

%\begin{convention}% Let [e] be a positive real number and [P] be a
partition of [I] with [n] points and mesh smaller than the
modulus of continuity of [F] for [e].  Let [fP] be a choice of points
respecting [P].
%\end{convention}%
*)

alias id "n" = "cic:/CoRN/ftc/Integral/Integral/Integral_Thm/n.var".

alias id "P" = "cic:/CoRN/ftc/Integral/Integral/Integral_Thm/P.var".

alias id "e" = "cic:/CoRN/ftc/Integral/Integral/Integral_Thm/e.var".

alias id "He" = "cic:/CoRN/ftc/Integral/Integral/Integral_Thm/He.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Integral/Integral/Integral_Thm/d.con" "Integral__Integral_Thm__".

(* end hide *)

alias id "HmeshP" = "cic:/CoRN/ftc/Integral/Integral/Integral_Thm/HmeshP.var".

alias id "fP" = "cic:/CoRN/ftc/Integral/Integral/Integral_Thm/fP.var".

alias id "HfP" = "cic:/CoRN/ftc/Integral/Integral/Integral_Thm/HfP.var".

alias id "HfP'" = "cic:/CoRN/ftc/Integral/Integral/Integral_Thm/HfP'.var".

alias id "incF" = "cic:/CoRN/ftc/Integral/Integral/Integral_Thm/incF.var".

inline "cic:/CoRN/ftc/Integral/partition_Sum_conv_integral.con".

(* UNEXPORTED
End Integral_Thm
*)

(* UNEXPORTED
End Integral
*)

(* UNEXPORTED
Section Basic_Properties
*)

(*#*
The usual extensionality and strong extensionality results hold.
*)

alias id "a" = "cic:/CoRN/ftc/Integral/Basic_Properties/a.var".

alias id "b" = "cic:/CoRN/ftc/Integral/Basic_Properties/b.var".

alias id "Hab" = "cic:/CoRN/ftc/Integral/Basic_Properties/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Integral/Basic_Properties/I.con" "Basic_Properties__".

(* end hide *)

(* NOTATION
Notation Integral := (integral _ _ Hab).
*)

(* UNEXPORTED
Section Well_Definedness
*)

alias id "F" = "cic:/CoRN/ftc/Integral/Basic_Properties/Well_Definedness/F.var".

alias id "G" = "cic:/CoRN/ftc/Integral/Basic_Properties/Well_Definedness/G.var".

alias id "contF" = "cic:/CoRN/ftc/Integral/Basic_Properties/Well_Definedness/contF.var".

alias id "contG" = "cic:/CoRN/ftc/Integral/Basic_Properties/Well_Definedness/contG.var".

inline "cic:/CoRN/ftc/Integral/integral_strext.con".

inline "cic:/CoRN/ftc/Integral/integral_strext'.con".

inline "cic:/CoRN/ftc/Integral/integral_wd.con".

inline "cic:/CoRN/ftc/Integral/integral_wd'.con".

(* UNEXPORTED
End Well_Definedness
*)

(* UNEXPORTED
Section Linearity_and_Monotonicity
*)

(* UNEXPORTED
Opaque Even_Partition.
*)

(*#*
The integral is a linear and monotonous function; in order to prove these facts we also need the important equalities $\int_a^bdx=b-a$#&int;<sub>a</sub><sup>b</sup>dx=b-a# and $\int_a^af(x)dx=0$#&int;<sub>a</sub><sup>a</sup>=0#.
*)

inline "cic:/CoRN/ftc/Integral/integral_one.con".

alias id "F" = "cic:/CoRN/ftc/Integral/Basic_Properties/Linearity_and_Monotonicity/F.var".

alias id "G" = "cic:/CoRN/ftc/Integral/Basic_Properties/Linearity_and_Monotonicity/G.var".

alias id "contF" = "cic:/CoRN/ftc/Integral/Basic_Properties/Linearity_and_Monotonicity/contF.var".

alias id "contG" = "cic:/CoRN/ftc/Integral/Basic_Properties/Linearity_and_Monotonicity/contG.var".

inline "cic:/CoRN/ftc/Integral/integral_comm_scal.con".

inline "cic:/CoRN/ftc/Integral/integral_plus.con".

(* UNEXPORTED
Transparent Even_Partition.
*)

inline "cic:/CoRN/ftc/Integral/integral_empty.con".

(* UNEXPORTED
End Linearity_and_Monotonicity
*)

(* UNEXPORTED
Section Linearity_and_Monotonicity'
*)

alias id "F" = "cic:/CoRN/ftc/Integral/Basic_Properties/Linearity_and_Monotonicity'/F.var".

alias id "G" = "cic:/CoRN/ftc/Integral/Basic_Properties/Linearity_and_Monotonicity'/G.var".

alias id "contF" = "cic:/CoRN/ftc/Integral/Basic_Properties/Linearity_and_Monotonicity'/contF.var".

alias id "contG" = "cic:/CoRN/ftc/Integral/Basic_Properties/Linearity_and_Monotonicity'/contG.var".

(*#*
%\begin{convention}% Let [alpha, beta : IR] and assume that
[h := alpha{**}F{+}beta{**}G] is continuous.
%\end{convention}%
*)

alias id "alpha" = "cic:/CoRN/ftc/Integral/Basic_Properties/Linearity_and_Monotonicity'/alpha.var".

alias id "beta" = "cic:/CoRN/ftc/Integral/Basic_Properties/Linearity_and_Monotonicity'/beta.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Integral/Basic_Properties/Linearity_and_Monotonicity'/h.con" "Basic_Properties__Linearity_and_Monotonicity'__".

(* end hide *)

alias id "contH" = "cic:/CoRN/ftc/Integral/Basic_Properties/Linearity_and_Monotonicity'/contH.var".

inline "cic:/CoRN/ftc/Integral/linear_integral.con".

(* UNEXPORTED
Opaque nring.
*)

inline "cic:/CoRN/ftc/Integral/monotonous_integral.con".

(* UNEXPORTED
Transparent nring.
*)

(* UNEXPORTED
End Linearity_and_Monotonicity'
*)

(* UNEXPORTED
Section Corollaries
*)

alias id "F" = "cic:/CoRN/ftc/Integral/Basic_Properties/Corollaries/F.var".

alias id "G" = "cic:/CoRN/ftc/Integral/Basic_Properties/Corollaries/G.var".

alias id "contF" = "cic:/CoRN/ftc/Integral/Basic_Properties/Corollaries/contF.var".

alias id "contG" = "cic:/CoRN/ftc/Integral/Basic_Properties/Corollaries/contG.var".

(*#*
As corollaries we can calculate integrals of group operations applied to functions.
*)

inline "cic:/CoRN/ftc/Integral/integral_const.con".

inline "cic:/CoRN/ftc/Integral/integral_minus.con".

inline "cic:/CoRN/ftc/Integral/integral_inv.con".

(*#*
We can also bound integrals by bounding the integrated functions.
*)

inline "cic:/CoRN/ftc/Integral/lb_integral.con".

inline "cic:/CoRN/ftc/Integral/ub_integral.con".

inline "cic:/CoRN/ftc/Integral/integral_leEq_norm.con".

(* UNEXPORTED
End Corollaries
*)

(* UNEXPORTED
Section Integral_Sum
*)

(*#*
We now relate the sum of integrals in adjoining intervals to the
integral over the union of those intervals.

%\begin{convention}% Let [c] be a real number such that
$c\in[a,b]$#c&isin;[a,b]#.
%\end{convention}%
*)

alias id "F" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/F.var".

alias id "c" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/c.var".

alias id "Hac" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/Hac.var".

alias id "Hcb" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/Hcb.var".

alias id "Hab'" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/Hab'.var".

alias id "Hac'" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/Hac'.var".

alias id "Hcb'" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/Hcb'.var".

(* UNEXPORTED
Section Partition_Join
*)

(*#*
We first prove that every pair of partitions, one of [[a,c]]
and another of [[c,b]] defines a partition of [[a,b]] the mesh
of which is less or equal to the maximum of the mesh of the original
partitions (actually it is equal, but we don't need the other
inequality).

%\begin{convention}% Let [P,Q] be partitions respectively of
[[a,c]] and [[c,b]] with [n] and [m] points.
%\end{convention}%
*)

alias id "n" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/Partition_Join/n.var".

alias id "m" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/Partition_Join/m.var".

alias id "P" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/Partition_Join/P.var".

alias id "Q" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/Partition_Join/Q.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Integral/partition_join_aux.con".

(* end hide *)

inline "cic:/CoRN/ftc/Integral/partition_join_fun.con".

(* begin hide *)

inline "cic:/CoRN/ftc/Integral/pjf_1.con".

inline "cic:/CoRN/ftc/Integral/pjf_2.con".

inline "cic:/CoRN/ftc/Integral/pjf_2'.con".

inline "cic:/CoRN/ftc/Integral/pjf_3.con".

inline "cic:/CoRN/ftc/Integral/partition_join_prf1.con".

inline "cic:/CoRN/ftc/Integral/partition_join_prf2.con".

inline "cic:/CoRN/ftc/Integral/partition_join_start.con".

inline "cic:/CoRN/ftc/Integral/partition_join_finish.con".

inline "cic:/CoRN/ftc/Integral/partition_join.con".

(* end hide *)

(*#*
%\begin{convention}% [fP, fQ] are choices of points respecting [P] and [Q].
%\end{convention}%
*)

alias id "fP" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/Partition_Join/fP.var".

alias id "HfP" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/Partition_Join/HfP.var".

alias id "HfP'" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/Partition_Join/HfP'.var".

alias id "fQ" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/Partition_Join/fQ.var".

alias id "HfQ" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/Partition_Join/HfQ.var".

alias id "HfQ'" = "cic:/CoRN/ftc/Integral/Basic_Properties/Integral_Sum/Partition_Join/HfQ'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Integral/partition_join_aux'.con".

(* end hide *)

inline "cic:/CoRN/ftc/Integral/partition_join_pts.con".

(* begin hide *)

inline "cic:/CoRN/ftc/Integral/pjp_1.con".

inline "cic:/CoRN/ftc/Integral/pjp_2.con".

inline "cic:/CoRN/ftc/Integral/pjp_3.con".

(* end hide *)

inline "cic:/CoRN/ftc/Integral/partition_join_Pts_in_partition.con".

inline "cic:/CoRN/ftc/Integral/partition_join_Pts_wd.con".

(* UNEXPORTED
Opaque partition_join.
*)

(* UNEXPORTED
Transparent partition_join.
*)

(* UNEXPORTED
Opaque minus.
*)

(* UNEXPORTED
Transparent minus.
*)

(* UNEXPORTED
Opaque minus.
*)

(* UNEXPORTED
Transparent minus.
*)

inline "cic:/CoRN/ftc/Integral/partition_join_Sum_lemma.con".

inline "cic:/CoRN/ftc/Integral/partition_join_mesh.con".

(* UNEXPORTED
End Partition_Join
*)

(*#*
With these results in mind, the following is a trivial consequence:
*)

(* UNEXPORTED
Opaque Even_Partition.
*)

inline "cic:/CoRN/ftc/Integral/integral_plus_integral.con".

(* UNEXPORTED
End Integral_Sum
*)

(* UNEXPORTED
Transparent Even_Partition.
*)

(* UNEXPORTED
End Basic_Properties
*)

(*#*
The following are simple consequences of this result and of previous ones.
*)

inline "cic:/CoRN/ftc/Integral/integral_less_norm.con".

(* end hide *)

inline "cic:/CoRN/ftc/Integral/integral_gt_zero.con".

(* end hide *)

(*#* remove printing Integral *)

