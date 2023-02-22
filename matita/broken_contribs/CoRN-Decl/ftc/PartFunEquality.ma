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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/PartFunEquality".

include "CoRN.ma".

(* $Id: PartFunEquality.v,v 1.8 2004/04/23 10:00:59 lcf Exp $ *)

(*#* printing Feq %\ensuremath{\approx}% #&asymp;# *)

include "reals/Intervals.ma".

include "tactics/DiffTactics1.ma".

(* UNEXPORTED
Section Definitions
*)

(*#* *Equality of Partial Functions

** Definitions

In some contexts (namely when quantifying over partial functions) we
need to refer explicitly to the subsetoid of elements satisfying a
given predicate rather than to the predicate itself.  The following
definition makes this possible.
*)

inline "cic:/CoRN/ftc/PartFunEquality/subset.con".

(*#*
The core of our work will revolve around the following fundamental
notion: two functions are equal in a given domain (predicate) iff they
coincide on every point of that domain#. #%\footnote{%Notice that,
according to our definition of partial function, it is equivalent to
prove the equality for every proof or for a specific proof.  Typically
it is easier to consider a generic case%.}%.  This file is concerned
with proving the main properties of this equality relation.
*)

inline "cic:/CoRN/ftc/PartFunEquality/Feq.con".

(*#*
Notice that, because the quantification over the proofs is universal,
we must require explicitly that the predicate be included in the
domain of each function; otherwise the basic properties of equality
(like, for example, transitivity) would fail to hold#. #%\footnote{%To
see this it is enough to realize that the empty function would be
equal to every other function in every domain.%}.% The way to
circumvent this would be to quantify existentially over the proofs;
this, however, would have two major disadvantages: first, proofs of
equality would become very cumbersome and clumsy; secondly (and most
important), we often need to prove the inclusions from an equality
hypothesis, and this definition allows us to do it in a very easy way.
Also, the pointwise equality is much nicer to use from this definition
than in an existentially quantified one.
*)

(* UNEXPORTED
End Definitions
*)

(* UNEXPORTED
Section Equality_Results
*)

(*#* **Properties of Inclusion

We will now prove the main properties of the equality relation.

%\begin{convention}% Let [I,R:IR->CProp] and [F,G:PartIR], and denote
by [P] and [Q], respectively, the domains of [F] and [G].
%\end{convention}%
*)

alias id "I" = "cic:/CoRN/ftc/PartFunEquality/Equality_Results/I.var".

alias id "F" = "cic:/CoRN/ftc/PartFunEquality/Equality_Results/F.var".

alias id "G" = "cic:/CoRN/ftc/PartFunEquality/Equality_Results/G.var".

(* begin hide *)

inline "cic:/CoRN/ftc/PartFunEquality/Equality_Results/P.con" "Equality_Results__".

inline "cic:/CoRN/ftc/PartFunEquality/Equality_Results/Q.con" "Equality_Results__".

(* end hide *)

alias id "R" = "cic:/CoRN/ftc/PartFunEquality/Equality_Results/R.var".

(*#*
We start with two lemmas which make it much easier to prove and use
this definition:
*)

inline "cic:/CoRN/ftc/PartFunEquality/eq_imp_Feq.con".

inline "cic:/CoRN/ftc/PartFunEquality/Feq_imp_eq.con".

inline "cic:/CoRN/ftc/PartFunEquality/included_IR.con".

(* UNEXPORTED
End Equality_Results
*)

(* UNEXPORTED
Hint Resolve included_IR : included.
*)

(* UNEXPORTED
Section Some_More
*)

(*#*
If two function coincide on a given subset then they coincide in any smaller subset.
*)

inline "cic:/CoRN/ftc/PartFunEquality/included_Feq.con".

(* UNEXPORTED
End Some_More
*)

(* UNEXPORTED
Section Away_from_Zero
*)

(* UNEXPORTED
Section Definitions
*)

(*#* **Away from Zero

Before we prove our main results about the equality we have to do some
work on division.  A function is said to be bounded away from zero in
a set if there exists a positive lower bound for the set of absolute
values of its image of that set.

%\begin{convention}% Let [I : IR->CProp], [F : PartIR] and denote by [P]
the domain of [F].
%\end{convention}%
*)

alias id "I" = "cic:/CoRN/ftc/PartFunEquality/Away_from_Zero/Definitions/I.var".

alias id "F" = "cic:/CoRN/ftc/PartFunEquality/Away_from_Zero/Definitions/F.var".

(* begin hide *)

inline "cic:/CoRN/ftc/PartFunEquality/Away_from_Zero/Definitions/P.con" "Away_from_Zero__Definitions__".

(* end hide *)

inline "cic:/CoRN/ftc/PartFunEquality/bnd_away_zero.con".

(*#*
If [F] is bounded away from zero in [I] then [F] is necessarily apart from zero in [I]; also this means that [I] is included in the domain of [{1/}F].
*)

(* begin show *)

alias id "Hf" = "cic:/CoRN/ftc/PartFunEquality/Away_from_Zero/Definitions/Hf.var".

(* end show *)

inline "cic:/CoRN/ftc/PartFunEquality/bnd_imp_ap_zero.con".

inline "cic:/CoRN/ftc/PartFunEquality/bnd_imp_inc_recip.con".

inline "cic:/CoRN/ftc/PartFunEquality/bnd_imp_inc_div.con".

(* UNEXPORTED
End Definitions
*)

(*#*
Boundedness away from zero is preserved through restriction of the set.

%\begin{convention}% Let [F] be a partial function and [P, Q] be predicates.
%\end{convention}%
*)

alias id "F" = "cic:/CoRN/ftc/PartFunEquality/Away_from_Zero/F.var".

alias id "P" = "cic:/CoRN/ftc/PartFunEquality/Away_from_Zero/P.var".

alias id "Q" = "cic:/CoRN/ftc/PartFunEquality/Away_from_Zero/Q.var".

inline "cic:/CoRN/ftc/PartFunEquality/included_imp_bnd.con".

inline "cic:/CoRN/ftc/PartFunEquality/FRestr_bnd.con".

(*#*
A function is said to be bounded away from zero everywhere if it is bounded away from zero in every compact subinterval of its domain; a similar definition is made for arbitrary sets, which will be necessary for future work.
*)

inline "cic:/CoRN/ftc/PartFunEquality/bnd_away_zero_everywhere.con".

inline "cic:/CoRN/ftc/PartFunEquality/bnd_away_zero_in_P.con".

(*#*
An immediate consequence:
*)

inline "cic:/CoRN/ftc/PartFunEquality/bnd_in_P_imp_ap_zero.con".

inline "cic:/CoRN/ftc/PartFunEquality/FRestr_bnd'.con".

(* UNEXPORTED
End Away_from_Zero
*)

(* UNEXPORTED
Hint Resolve bnd_imp_inc_recip bnd_imp_inc_div: included.
*)

(* UNEXPORTED
Hint Immediate bnd_in_P_imp_ap_zero: included.
*)

(*#* ** The [FEQ] tactic
This tactic splits a goal of the form [Feq I F G] into the three subgoals
[included I (Dom F)], [included I (Dom G)] and [forall x, F x [=] G x]
and applies [Included] to the first two and [rational] to the third.
*)

(* begin hide *)

(* UNEXPORTED
Ltac FEQ := apply eq_imp_Feq;
   [ Included | Included | intros; try (simpl in |- *; rational) ].
*)

(* end hide *)

(* UNEXPORTED
Section More_on_Equality
*)

(*#* **Properties of Equality

We are now finally able to prove the main properties of the equality relation.  We begin by showing it to be an equivalence relation.

%\begin{convention}% Let [I] be a predicate and [F, F', G, G', H] be
partial functions.
%\end{convention}%
*)

alias id "I" = "cic:/CoRN/ftc/PartFunEquality/More_on_Equality/I.var".

(* UNEXPORTED
Section Feq_Equivalence
*)

alias id "F" = "cic:/CoRN/ftc/PartFunEquality/More_on_Equality/Feq_Equivalence/F.var".

alias id "G" = "cic:/CoRN/ftc/PartFunEquality/More_on_Equality/Feq_Equivalence/G.var".

alias id "H" = "cic:/CoRN/ftc/PartFunEquality/More_on_Equality/Feq_Equivalence/H.var".

inline "cic:/CoRN/ftc/PartFunEquality/Feq_reflexive.con".

inline "cic:/CoRN/ftc/PartFunEquality/Feq_symmetric.con".

inline "cic:/CoRN/ftc/PartFunEquality/Feq_transitive.con".

(* UNEXPORTED
End Feq_Equivalence
*)

(* UNEXPORTED
Section Operations
*)

(*#*
Also it is preserved through application of functional constructors and restriction.
*)

alias id "F" = "cic:/CoRN/ftc/PartFunEquality/More_on_Equality/Operations/F.var".

alias id "F'" = "cic:/CoRN/ftc/PartFunEquality/More_on_Equality/Operations/F'.var".

alias id "G" = "cic:/CoRN/ftc/PartFunEquality/More_on_Equality/Operations/G.var".

alias id "G'" = "cic:/CoRN/ftc/PartFunEquality/More_on_Equality/Operations/G'.var".

inline "cic:/CoRN/ftc/PartFunEquality/Feq_plus.con".

inline "cic:/CoRN/ftc/PartFunEquality/Feq_inv.con".

inline "cic:/CoRN/ftc/PartFunEquality/Feq_minus.con".

inline "cic:/CoRN/ftc/PartFunEquality/Feq_mult.con".

inline "cic:/CoRN/ftc/PartFunEquality/Feq_nth.con".

inline "cic:/CoRN/ftc/PartFunEquality/Feq_recip.con".

inline "cic:/CoRN/ftc/PartFunEquality/Feq_recip'.con".

inline "cic:/CoRN/ftc/PartFunEquality/Feq_div.con".

inline "cic:/CoRN/ftc/PartFunEquality/Feq_div'.con".

(*#*
Notice that in the case of division we only need to require boundedness away from zero for one of the functions (as they are equal); thus the two last lemmas are stated in two different ways, as according to the context one or the other condition may be easier to prove.

The restriction of a function is well defined.
*)

inline "cic:/CoRN/ftc/PartFunEquality/FRestr_wd.con".

(*#*
The image of a set is extensional.
*)

inline "cic:/CoRN/ftc/PartFunEquality/fun_image_wd.con".

(* UNEXPORTED
End Operations
*)

(* UNEXPORTED
End More_on_Equality
*)

(* UNEXPORTED
Section Nth_Power
*)

(*#* **Nth Power

We finish this group of lemmas with characterization results for the
power function (similar to those already proved for arbitrary rings).
The characterization is done at first pointwise and later using the
equality relation.

%\begin{convention}% Let [F] be a partial function with domain [P] and
[Q] be a predicate on the real numbers assumed to be included in [P].
%\end{convention}%
*)

alias id "F" = "cic:/CoRN/ftc/PartFunEquality/Nth_Power/F.var".

(* begin hide *)

inline "cic:/CoRN/ftc/PartFunEquality/Nth_Power/P.con" "Nth_Power__".

(* end hide *)

alias id "Q" = "cic:/CoRN/ftc/PartFunEquality/Nth_Power/Q.var".

alias id "H" = "cic:/CoRN/ftc/PartFunEquality/Nth_Power/H.var".

alias id "Hf" = "cic:/CoRN/ftc/PartFunEquality/Nth_Power/Hf.var".

inline "cic:/CoRN/ftc/PartFunEquality/FNth_zero.con".

alias id "n" = "cic:/CoRN/ftc/PartFunEquality/Nth_Power/n.var".

alias id "H'" = "cic:/CoRN/ftc/PartFunEquality/Nth_Power/H'.var".

inline "cic:/CoRN/ftc/PartFunEquality/FNth_mult.con".

(* UNEXPORTED
End Nth_Power
*)

(* UNEXPORTED
Section Strong_Nth_Power
*)

(*#*
%\begin{convention}% Let [a,b] be real numbers such that [I := [a,b]]
is included in the domain of [F].
%\end{convention}%
*)

alias id "a" = "cic:/CoRN/ftc/PartFunEquality/Strong_Nth_Power/a.var".

alias id "b" = "cic:/CoRN/ftc/PartFunEquality/Strong_Nth_Power/b.var".

alias id "Hab" = "cic:/CoRN/ftc/PartFunEquality/Strong_Nth_Power/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/PartFunEquality/Strong_Nth_Power/I.con" "Strong_Nth_Power__".

(* end hide *)

alias id "F" = "cic:/CoRN/ftc/PartFunEquality/Strong_Nth_Power/F.var".

alias id "incF" = "cic:/CoRN/ftc/PartFunEquality/Strong_Nth_Power/incF.var".

inline "cic:/CoRN/ftc/PartFunEquality/FNth_zero'.con".

inline "cic:/CoRN/ftc/PartFunEquality/FNth_mult'.con".

(* UNEXPORTED
End Strong_Nth_Power
*)

