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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/MoreIntervals".

include "CoRN.ma".

(* $Id: MoreIntervals.v,v 1.6 2004/04/23 10:00:59 lcf Exp $ *)

include "ftc/NthDerivative.ma".

(* UNEXPORTED
Opaque Min Max.
*)

(* UNEXPORTED
Section Intervals
*)

(*#* printing realline %\ensuremath{\RR}% #(-&infin;,+&infin;)# *)

(*#* printing openl %\ensuremath{(\cdot,+\infty)}% #(&sdot;,+&infin;)# *)

(*#* printing openr %\ensuremath{(-\infty,\cdot)}% #(-&infin;,&sdot;)# *)

(*#* printing closel %\ensuremath{[\cdot,+\infty)}% #[&sdot;,+&infin;)# *)

(*#* printing closer %\ensuremath{(-\infty,\cdot]}% #(-&infin;,&sdot;]# *)

(*#* printing olor %\ensuremath{(\cdot,\cdot)}% #(&sdot;,&sdot;)# *)

(*#* printing clor %\ensuremath{[\cdot,\cdot)}% #[&sdot;,&sdot;)# *)

(*#* printing olcr %\ensuremath{(\cdot,\cdot]}% #(&sdot;,&sdot;]# *)

(*#* printing clcr %\ensuremath{[\cdot,\cdot]}% #[&sdot;,&sdot;]# *)

(*#* *Generalized Intervals

At this stage we have enough material to begin generalizing our
concepts in preparation for the fundamental theorem of calculus and
the definition of the main (non-polynomial) functions of analysis.

In order to define functions via power series (or any other kind of
series) we need to formalize a notion of convergence more general than
the one we already have on compact intervals.  This is necessary for
practical reasons: we want to define a single exponential function
with domain [IR], not several exponential functions defined on compact
intervals which we prove to be the same wherever their domains
overlap.  In a similar way, we want to define indefinite integrals on
infinite domains and not only on compact intervals.

Unfortunately, proceeding in a way analogous to how we defined the
concept of global continuity will lead us nowhere; the concept turns
out to be to general, and the behaviour on too small domains
(typically intervals [[a,a']] where [a [=] a'] is neither
provably true nor provably false) will be unsatisfactory.

There is a special family of sets, however, where this problems can be
avoided: intervals.  Intervals have some nice properties that allow us
to prove good results, namely the facts that if [a] and [b] are
elements of an interval [I] then so are [Min(a,b)] and
[Max(a,b)] (which is in general not true) and also the
compact interval [[a,b]] is included in [I].  Furthermore, all
intervals are characterized by simple, well defined predicates, and
the nonempty and proper concepts become very easy to define.

**Definitions and Basic Results

We define an inductive type of intervals with nine constructors,
corresponding to the nine basic types of intervals.  The reason why so
many constructors are needed is that we do not have a notion of real
line, for many reasons which we will not discuss here.  Also it seems
simple to directly define finite intervals than to define then later
as intersections of infinite intervals, as it would only mess things
up.

The compact interval which we will define here is obviously the same
that we have been working with all the way through; why, then, the
different formulation?  The reason is simple: if we had worked with
intervals from the beginning we would have had case definitions at
every spot, and our lemmas and proofs would have been very awkward.
Also, it seems more natural to characterize a compact interval by two
real numbers (and a proof) than as a particular case of a more general
concept which doesn't have an intuitive interpretation.  Finally, the
definitions we will make here will have the elegant consequence that
from this point on we can work with any kind of intervals in exactly
the same way.
*)

inline "cic:/CoRN/ftc/MoreIntervals/interval.ind".

(*#*
To each interval a predicate (set) is assigned by the following map:
*)

inline "cic:/CoRN/ftc/MoreIntervals/iprop.con".

(* begin hide *)

coercion cic:/matita/CoRN-Decl/ftc/MoreIntervals/iprop.con 0 (* compounds *).

(* end hide *)

(*#*
This map is made into a coercion, so that intervals
%\emph{%#<i>#are%}%#</i># really subsets of reals.

We now define what it means for an interval to be nonvoid, proper,
finite and compact in the obvious way.
*)

inline "cic:/CoRN/ftc/MoreIntervals/nonvoid.con".

inline "cic:/CoRN/ftc/MoreIntervals/proper.con".

inline "cic:/CoRN/ftc/MoreIntervals/finite.con".

inline "cic:/CoRN/ftc/MoreIntervals/compact_.con".

(*#* Finite intervals have a left end and a right end. *)

inline "cic:/CoRN/ftc/MoreIntervals/left_end.con".

inline "cic:/CoRN/ftc/MoreIntervals/right_end.con".

(*#*
Some trivia: compact intervals are finite; proper intervals are nonvoid; an interval is nonvoid iff it contains some point.
*)

inline "cic:/CoRN/ftc/MoreIntervals/compact_finite.con".

inline "cic:/CoRN/ftc/MoreIntervals/proper_nonvoid.con".

inline "cic:/CoRN/ftc/MoreIntervals/nonvoid_point.con".

inline "cic:/CoRN/ftc/MoreIntervals/nonvoid_char.con".

(*#*
For practical reasons it helps to define left end and right end of compact intervals.
*)

inline "cic:/CoRN/ftc/MoreIntervals/Lend.con".

inline "cic:/CoRN/ftc/MoreIntervals/Rend.con".

(*#* In a compact interval, the left end is always less than or equal
to the right end.
*)

inline "cic:/CoRN/ftc/MoreIntervals/Lend_leEq_Rend.con".

(*#*
Some nice characterizations of inclusion:
*)

inline "cic:/CoRN/ftc/MoreIntervals/compact_included.con".

inline "cic:/CoRN/ftc/MoreIntervals/included_interval'.con".

inline "cic:/CoRN/ftc/MoreIntervals/included_interval.con".

(*#*
A weirder inclusion result.
*)

inline "cic:/CoRN/ftc/MoreIntervals/included3_interval.con".

(*#*
Finally, all intervals are characterized by well defined predicates.
*)

inline "cic:/CoRN/ftc/MoreIntervals/iprop_wd.con".

(* UNEXPORTED
End Intervals
*)

(* UNEXPORTED
Implicit Arguments Lend [I].
*)

(* UNEXPORTED
Implicit Arguments Rend [I].
*)

(* UNEXPORTED
Section Compact_Constructions
*)

(* UNEXPORTED
Section Single_Compact_Interval
*)

(*#* **Constructions with Compact Intervals

Several important constructions are now discussed.

We begin by defining the compact interval [[x,x]].

%\begin{convention}% Let [P:IR->CProp] be well defined, and [x:IR]
such that [P(x)] holds.
%\end{convention}%
*)

alias id "P" = "cic:/CoRN/ftc/MoreIntervals/Compact_Constructions/Single_Compact_Interval/P.var".

alias id "wdP" = "cic:/CoRN/ftc/MoreIntervals/Compact_Constructions/Single_Compact_Interval/wdP.var".

alias id "x" = "cic:/CoRN/ftc/MoreIntervals/Compact_Constructions/Single_Compact_Interval/x.var".

alias id "Hx" = "cic:/CoRN/ftc/MoreIntervals/Compact_Constructions/Single_Compact_Interval/Hx.var".

inline "cic:/CoRN/ftc/MoreIntervals/compact_single.con".

(*#*
This interval contains [x] and only (elements equal to) [x]; furthermore, for every (well-defined) [P], if $x\in P$#x&isin;P# then $[x,x]\subseteq P$#[x,x]&sube;P#.
*)

inline "cic:/CoRN/ftc/MoreIntervals/compact_single_prop.con".

inline "cic:/CoRN/ftc/MoreIntervals/compact_single_pt.con".

inline "cic:/CoRN/ftc/MoreIntervals/compact_single_inc.con".

(* UNEXPORTED
End Single_Compact_Interval
*)

(*#*
The special case of intervals is worth singling out, as one of the hypothesis becomes a theorem.
*)

inline "cic:/CoRN/ftc/MoreIntervals/compact_single_iprop.con".

(*#*
Now for more interesting and important results.

Let [I] be a proper interval and [x] be a point of [I].  Then there is
a proper compact interval [[a,b]] such that $x\in[a,b]\subseteq
I$#x&isin;[a,b]&sube;I#.
*)

(* UNEXPORTED
Section Proper_Compact_with_One_or_Two_Points
*)

(* begin hide *)

inline "cic:/CoRN/ftc/MoreIntervals/Compact_Constructions/Proper_Compact_with_One_or_Two_Points/cip1'.con" "Compact_Constructions__Proper_Compact_with_One_or_Two_Points__".

inline "cic:/CoRN/ftc/MoreIntervals/Compact_Constructions/Proper_Compact_with_One_or_Two_Points/cip1''.con" "Compact_Constructions__Proper_Compact_with_One_or_Two_Points__".

inline "cic:/CoRN/ftc/MoreIntervals/Compact_Constructions/Proper_Compact_with_One_or_Two_Points/cip1'''.con" "Compact_Constructions__Proper_Compact_with_One_or_Two_Points__".

inline "cic:/CoRN/ftc/MoreIntervals/Compact_Constructions/Proper_Compact_with_One_or_Two_Points/cip1''''.con" "Compact_Constructions__Proper_Compact_with_One_or_Two_Points__".

inline "cic:/CoRN/ftc/MoreIntervals/Compact_Constructions/Proper_Compact_with_One_or_Two_Points/cip2.con" "Compact_Constructions__Proper_Compact_with_One_or_Two_Points__".

inline "cic:/CoRN/ftc/MoreIntervals/Compact_Constructions/Proper_Compact_with_One_or_Two_Points/cip2'.con" "Compact_Constructions__Proper_Compact_with_One_or_Two_Points__".

inline "cic:/CoRN/ftc/MoreIntervals/Compact_Constructions/Proper_Compact_with_One_or_Two_Points/cip2''.con" "Compact_Constructions__Proper_Compact_with_One_or_Two_Points__".

inline "cic:/CoRN/ftc/MoreIntervals/Compact_Constructions/Proper_Compact_with_One_or_Two_Points/cip2'''.con" "Compact_Constructions__Proper_Compact_with_One_or_Two_Points__".

inline "cic:/CoRN/ftc/MoreIntervals/Compact_Constructions/Proper_Compact_with_One_or_Two_Points/cip3.con" "Compact_Constructions__Proper_Compact_with_One_or_Two_Points__".

inline "cic:/CoRN/ftc/MoreIntervals/Compact_Constructions/Proper_Compact_with_One_or_Two_Points/cip3'.con" "Compact_Constructions__Proper_Compact_with_One_or_Two_Points__".

inline "cic:/CoRN/ftc/MoreIntervals/Compact_Constructions/Proper_Compact_with_One_or_Two_Points/cip3''.con" "Compact_Constructions__Proper_Compact_with_One_or_Two_Points__".

inline "cic:/CoRN/ftc/MoreIntervals/Compact_Constructions/Proper_Compact_with_One_or_Two_Points/cip3'''.con" "Compact_Constructions__Proper_Compact_with_One_or_Two_Points__".

(* end hide *)

inline "cic:/CoRN/ftc/MoreIntervals/compact_in_interval.con".

inline "cic:/CoRN/ftc/MoreIntervals/compact_compact_in_interval.con".

inline "cic:/CoRN/ftc/MoreIntervals/proper_compact_in_interval.con".

inline "cic:/CoRN/ftc/MoreIntervals/proper_compact_in_interval'.con".

inline "cic:/CoRN/ftc/MoreIntervals/included_compact_in_interval.con".

inline "cic:/CoRN/ftc/MoreIntervals/iprop_compact_in_interval.con".

inline "cic:/CoRN/ftc/MoreIntervals/iprop_compact_in_interval'.con".

inline "cic:/CoRN/ftc/MoreIntervals/iprop_compact_in_interval_inc1.con".

inline "cic:/CoRN/ftc/MoreIntervals/iprop_compact_in_interval_inc2.con".

(*#*
If [x [=] y] then the construction yields the same interval whether we
use [x] or [y] in its definition.  This property is required at some
stage, which is why we formalized this result as a functional
definition rather than as an existential formula.
*)

inline "cic:/CoRN/ftc/MoreIntervals/compact_in_interval_wd1.con".

inline "cic:/CoRN/ftc/MoreIntervals/compact_in_interval_wd2.con".

(*#*
We can make an analogous construction for two points.
*)

inline "cic:/CoRN/ftc/MoreIntervals/compact_in_interval2.con".

inline "cic:/CoRN/ftc/MoreIntervals/compact_compact_in_interval2.con".

inline "cic:/CoRN/ftc/MoreIntervals/proper_compact_in_interval2.con".

inline "cic:/CoRN/ftc/MoreIntervals/proper_compact_in_interval2'.con".

inline "cic:/CoRN/ftc/MoreIntervals/included_compact_in_interval2.con".

inline "cic:/CoRN/ftc/MoreIntervals/iprop_compact_in_interval2x.con".

inline "cic:/CoRN/ftc/MoreIntervals/iprop_compact_in_interval2y.con".

inline "cic:/CoRN/ftc/MoreIntervals/iprop_compact_in_interval2x'.con".

inline "cic:/CoRN/ftc/MoreIntervals/iprop_compact_in_interval2y'.con".

inline "cic:/CoRN/ftc/MoreIntervals/iprop_compact_in_interval2_inc1.con".

inline "cic:/CoRN/ftc/MoreIntervals/iprop_compact_in_interval2_inc2.con".

inline "cic:/CoRN/ftc/MoreIntervals/compact_in_interval_x_lft.con".

inline "cic:/CoRN/ftc/MoreIntervals/compact_in_interval_y_lft.con".

inline "cic:/CoRN/ftc/MoreIntervals/compact_in_interval_x_rht.con".

inline "cic:/CoRN/ftc/MoreIntervals/compact_in_interval_y_rht.con".

(* UNEXPORTED
End Proper_Compact_with_One_or_Two_Points
*)

(*#*
Compact intervals are exactly compact intervals(!).
*)

inline "cic:/CoRN/ftc/MoreIntervals/interval_compact_inc.con".

inline "cic:/CoRN/ftc/MoreIntervals/compact_interval_inc.con".

(*#*
A generalization of the previous results: if $[a,b]\subseteq J$#[a,b]&sube;J#
and [J] is proper, then we can find a proper interval [[a',b']] such that
$[a,b]\subseteq[a',b']\subseteq J$#[a,b]&sube;[a',b']&sube;J#.
*)

inline "cic:/CoRN/ftc/MoreIntervals/compact_proper_in_interval.con".

(* UNEXPORTED
End Compact_Constructions
*)

(* UNEXPORTED
Section Functions
*)

(*#* **Properties of Functions in Intervals

We now define notions of continuity, differentiability and so on on
arbitrary intervals.  As expected, a function [F] has property [P] in
the (proper) interval [I] iff it has property [P] in every compact
interval included in [I].  We can formalize this in a nice way using
previously defined concepts.

%\begin{convention}% Let [n:nat] and [I:interval].
%\end{convention}%
*)

alias id "n" = "cic:/CoRN/ftc/MoreIntervals/Functions/n.var".

alias id "I" = "cic:/CoRN/ftc/MoreIntervals/Functions/I.var".

inline "cic:/CoRN/ftc/MoreIntervals/Continuous.con".

inline "cic:/CoRN/ftc/MoreIntervals/Derivative.con".

inline "cic:/CoRN/ftc/MoreIntervals/Diffble.con".

inline "cic:/CoRN/ftc/MoreIntervals/Derivative_n.con".

inline "cic:/CoRN/ftc/MoreIntervals/Diffble_n.con".

(* UNEXPORTED
End Functions
*)

(* UNEXPORTED
Section Reflexivity_Properties
*)

(*#*
In the case of compact intervals, this definitions collapse to the old ones.
*)

inline "cic:/CoRN/ftc/MoreIntervals/Continuous_Int.con".

inline "cic:/CoRN/ftc/MoreIntervals/Int_Continuous.con".

inline "cic:/CoRN/ftc/MoreIntervals/Derivative_Int.con".

inline "cic:/CoRN/ftc/MoreIntervals/Int_Derivative.con".

inline "cic:/CoRN/ftc/MoreIntervals/Diffble_Int.con".

inline "cic:/CoRN/ftc/MoreIntervals/Int_Diffble.con".

(* UNEXPORTED
End Reflexivity_Properties
*)

(* UNEXPORTED
Section Lemmas
*)

(*#*
Interestingly, inclusion and equality in an interval are also characterizable in a similar way:
*)

inline "cic:/CoRN/ftc/MoreIntervals/included_imp_inc.con".

inline "cic:/CoRN/ftc/MoreIntervals/included_Feq''.con".

inline "cic:/CoRN/ftc/MoreIntervals/included_Feq'.con".

(* UNEXPORTED
End Lemmas
*)

(* UNEXPORTED
Hint Resolve included_interval included_interval' included3_interval
  compact_single_inc compact_single_iprop included_compact_in_interval
  iprop_compact_in_interval_inc1 iprop_compact_in_interval_inc2
  included_compact_in_interval2 iprop_compact_in_interval2_inc1
  iprop_compact_in_interval2_inc2 interval_compact_inc compact_interval_inc
  iprop_wd: included.
*)

