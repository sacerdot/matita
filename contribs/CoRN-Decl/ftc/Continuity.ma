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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/Continuity".

include "CoRN.ma".

(* $Id: Continuity.v,v 1.6 2004/04/23 10:00:58 lcf Exp $ *)

(*#* printing Norm_Funct %\ensuremath{\|\cdot\|}% *)

include "reals/NRootIR.ma".

include "ftc/FunctSums.ma".

(* UNEXPORTED
Section Definitions_and_Basic_Results
*)

(*#* *Continuity

Constructively, continuity is the most fundamental property of any
function---so strongly that no example is known of a constructive
function that is not continuous.  However, the classical definition of
continuity is not good for our purposes, as it is not true, for
example, that a function which is continuous in a compact interval is
uniformly continuous in that same interval (for a discussion of this
see Bishop 1967).  Thus, our notion of continuity will be the uniform
one#. #%\footnote{%Similar remarks apply to convergence of sequences
of functions, which we will define ahead, and elsewhere; we will
refrain from discussing this issue at those places.%}.%

%\begin{convention}% Throughout this section, [a] and [b] will be real
numbers, [I] will denote the compact interval [[a,b]] and
[F, G, H] will denote arbitrary partial functions with domains
respectively [P, Q] and [R].
%\end{convention}%

** Definitions and Basic Results

Here we define continuity and prove some basic properties of continuous functions.
*)

alias id "a" = "cic:/CoRN/ftc/Continuity/Definitions_and_Basic_Results/a.var".

alias id "b" = "cic:/CoRN/ftc/Continuity/Definitions_and_Basic_Results/b.var".

alias id "Hab" = "cic:/CoRN/ftc/Continuity/Definitions_and_Basic_Results/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Continuity/Definitions_and_Basic_Results/I.con" "Definitions_and_Basic_Results__".

(* end hide *)

alias id "F" = "cic:/CoRN/ftc/Continuity/Definitions_and_Basic_Results/F.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Continuity/Definitions_and_Basic_Results/P.con" "Definitions_and_Basic_Results__".

(* end hide *)

inline "cic:/CoRN/ftc/Continuity/Continuous_I.con".

(*#*
For convenience, we distinguish the two properties of continuous functions.
*)

inline "cic:/CoRN/ftc/Continuity/contin_imp_inc.con".

inline "cic:/CoRN/ftc/Continuity/contin_prop.con".

(*#*
Assume [F] to be continuous in [I].  Then it has a least upper bound and a greater lower bound on [I].
*)

alias id "contF" = "cic:/CoRN/ftc/Continuity/Definitions_and_Basic_Results/contF.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Continuity/Definitions_and_Basic_Results/Hinc'.con" "Definitions_and_Basic_Results__".

(* end hide *)

inline "cic:/CoRN/ftc/Continuity/Continuous_I_imp_tb_image.con".

inline "cic:/CoRN/ftc/Continuity/Continuous_I_imp_lub.con".

inline "cic:/CoRN/ftc/Continuity/Continuous_I_imp_glb.con".

(*#*
We now make this glb and lub into operators.
*)

inline "cic:/CoRN/ftc/Continuity/lub_funct.con".

inline "cic:/CoRN/ftc/Continuity/glb_funct.con".

(*#*
These operators have the expected properties.
*)

inline "cic:/CoRN/ftc/Continuity/lub_is_lub.con".

inline "cic:/CoRN/ftc/Continuity/glb_is_glb.con".

inline "cic:/CoRN/ftc/Continuity/glb_prop.con".

inline "cic:/CoRN/ftc/Continuity/lub_prop.con".

(*#*
The norm of a function is defined as being the supremum of its absolute value; that is equivalent to the following definition (which is often more convenient to use).
*)

inline "cic:/CoRN/ftc/Continuity/Norm_Funct.con".

(*#*
The norm effectively bounds the absolute value of a function.
*)

inline "cic:/CoRN/ftc/Continuity/norm_bnd_AbsIR.con".

(*#*
The following is another way of characterizing the norm:
*)

inline "cic:/CoRN/ftc/Continuity/Continuous_I_imp_abs_lub.con".

(*#*
We now prove some basic properties of the norm---namely that it is positive, and that it provides a least upper bound for the absolute value of its argument.
*)

inline "cic:/CoRN/ftc/Continuity/positive_norm.con".

inline "cic:/CoRN/ftc/Continuity/norm_fun_lub.con".

inline "cic:/CoRN/ftc/Continuity/leEq_Norm_Funct.con".

inline "cic:/CoRN/ftc/Continuity/less_Norm_Funct.con".

(* UNEXPORTED
End Definitions_and_Basic_Results
*)

(* UNEXPORTED
Implicit Arguments Continuous_I [a b].
*)

(* UNEXPORTED
Implicit Arguments Norm_Funct [a b Hab F].
*)

(* UNEXPORTED
Section Local_Results
*)

(*#* **Algebraic Properties

We now state and prove some results about continuous functions.  Assume that [I] is included in the domain of both [F] and [G].
*)

alias id "a" = "cic:/CoRN/ftc/Continuity/Local_Results/a.var".

alias id "b" = "cic:/CoRN/ftc/Continuity/Local_Results/b.var".

alias id "Hab" = "cic:/CoRN/ftc/Continuity/Local_Results/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Continuity/Local_Results/I.con" "Local_Results__".

(* end hide *)

alias id "F" = "cic:/CoRN/ftc/Continuity/Local_Results/F.var".

alias id "G" = "cic:/CoRN/ftc/Continuity/Local_Results/G.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Continuity/Local_Results/P.con" "Local_Results__".

inline "cic:/CoRN/ftc/Continuity/Local_Results/Q.con" "Local_Results__".

(* end hide *)

alias id "incF" = "cic:/CoRN/ftc/Continuity/Local_Results/incF.var".

alias id "incG" = "cic:/CoRN/ftc/Continuity/Local_Results/incG.var".

(*#*
The first result does not require the function to be continuous; however, its preconditions are easily verified by continuous functions, which justifies its inclusion in this section.
*)

inline "cic:/CoRN/ftc/Continuity/cont_no_sign_change.con".

inline "cic:/CoRN/ftc/Continuity/cont_no_sign_change_pos.con".

inline "cic:/CoRN/ftc/Continuity/cont_no_sign_change_neg.con".

(*#*
Being continuous is an extensional property.
*)

inline "cic:/CoRN/ftc/Continuity/Continuous_I_wd.con".

(*#*
A continuous function remains continuous if you restrict its domain.
*)

inline "cic:/CoRN/ftc/Continuity/included_imp_contin.con".

(*#*
Constant functions and identity are continuous.
*)

inline "cic:/CoRN/ftc/Continuity/Continuous_I_const.con".

inline "cic:/CoRN/ftc/Continuity/Continuous_I_id.con".

(*#*
Assume [F] and [G] are continuous in [I].  Then functions derived from these through algebraic operations are also continuous, provided (in the case of reciprocal and division) some extra conditions are met.
*)

alias id "contF" = "cic:/CoRN/ftc/Continuity/Local_Results/contF.var".

alias id "contG" = "cic:/CoRN/ftc/Continuity/Local_Results/contG.var".

inline "cic:/CoRN/ftc/Continuity/Continuous_I_plus.con".

inline "cic:/CoRN/ftc/Continuity/Continuous_I_inv.con".

inline "cic:/CoRN/ftc/Continuity/Continuous_I_mult.con".

(* UNEXPORTED
Opaque AbsIR Max.
*)

(* UNEXPORTED
Transparent AbsIR Max.
*)

inline "cic:/CoRN/ftc/Continuity/Continuous_I_max.con".

(* begin show *)

alias id "Hg'" = "cic:/CoRN/ftc/Continuity/Local_Results/Hg'.var".

alias id "Hg''" = "cic:/CoRN/ftc/Continuity/Local_Results/Hg''.var".

(* end show *)

inline "cic:/CoRN/ftc/Continuity/Continuous_I_recip.con".

(* UNEXPORTED
End Local_Results
*)

(* UNEXPORTED
Hint Resolve contin_imp_inc: included.
*)

(* UNEXPORTED
Section Corolaries
*)

alias id "a" = "cic:/CoRN/ftc/Continuity/Corolaries/a.var".

alias id "b" = "cic:/CoRN/ftc/Continuity/Corolaries/b.var".

alias id "Hab" = "cic:/CoRN/ftc/Continuity/Corolaries/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Continuity/Corolaries/I.con" "Corolaries__".

(* end hide *)

alias id "F" = "cic:/CoRN/ftc/Continuity/Corolaries/F.var".

alias id "G" = "cic:/CoRN/ftc/Continuity/Corolaries/G.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Continuity/Corolaries/P.con" "Corolaries__".

inline "cic:/CoRN/ftc/Continuity/Corolaries/Q.con" "Corolaries__".

(* end hide *)

alias id "contF" = "cic:/CoRN/ftc/Continuity/Corolaries/contF.var".

alias id "contG" = "cic:/CoRN/ftc/Continuity/Corolaries/contG.var".

(*#*
The corresponding properties for subtraction, division and
multiplication by a scalar are easily proved as corollaries;
exponentiation is proved by induction, appealing to the results on
product and constant functions.
*)

inline "cic:/CoRN/ftc/Continuity/Continuous_I_minus.con".

inline "cic:/CoRN/ftc/Continuity/Continuous_I_scal.con".

inline "cic:/CoRN/ftc/Continuity/Continuous_I_nth.con".

inline "cic:/CoRN/ftc/Continuity/Continuous_I_min.con".

inline "cic:/CoRN/ftc/Continuity/Continuous_I_abs.con".

alias id "Hg'" = "cic:/CoRN/ftc/Continuity/Corolaries/Hg'.var".

alias id "Hg''" = "cic:/CoRN/ftc/Continuity/Corolaries/Hg''.var".

inline "cic:/CoRN/ftc/Continuity/Continuous_I_div.con".

(* UNEXPORTED
End Corolaries
*)

(* UNEXPORTED
Section Other
*)

(* UNEXPORTED
Section Sums
*)

(*#*
We finally prove that the sum of an arbitrary family of continuous functions is still a continuous function.
*)

alias id "a" = "cic:/CoRN/ftc/Continuity/Other/Sums/a.var".

alias id "b" = "cic:/CoRN/ftc/Continuity/Other/Sums/b.var".

alias id "Hab" = "cic:/CoRN/ftc/Continuity/Other/Sums/Hab.var".

alias id "Hab'" = "cic:/CoRN/ftc/Continuity/Other/Sums/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Continuity/Other/Sums/I.con" "Other__Sums__".

(* end hide *)

inline "cic:/CoRN/ftc/Continuity/Continuous_I_Sum0.con".

inline "cic:/CoRN/ftc/Continuity/Continuous_I_Sumx.con".

inline "cic:/CoRN/ftc/Continuity/Continuous_I_Sum.con".

(* UNEXPORTED
End Sums
*)

(*#*
For practical purposes, these characterization results are useful:
*)

inline "cic:/CoRN/ftc/Continuity/lub_charact.con".

inline "cic:/CoRN/ftc/Continuity/glb_charact.con".

(*#*
The following result is also extremely useful, as it allows us to set a lower bound on the glb of a function.
*)

inline "cic:/CoRN/ftc/Continuity/leEq_glb.con".

(*#*
The norm is also an extensional property.
*)

inline "cic:/CoRN/ftc/Continuity/Norm_Funct_wd.con".

(*#*
The value of the norm is covariant with the length of the interval.
*)

inline "cic:/CoRN/ftc/Continuity/included_imp_norm_leEq.con".

(* UNEXPORTED
End Other
*)

(* UNEXPORTED
Hint Resolve Continuous_I_const Continuous_I_id Continuous_I_plus
  Continuous_I_inv Continuous_I_minus Continuous_I_mult Continuous_I_scal
  Continuous_I_recip Continuous_I_max Continuous_I_min Continuous_I_div
  Continuous_I_nth Continuous_I_abs: continuous.
*)

