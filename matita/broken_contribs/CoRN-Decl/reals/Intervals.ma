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

set "baseuri" "cic:/matita/CoRN-Decl/reals/Intervals".

include "CoRN.ma".

(* $Id: Intervals.v,v 1.10 2004/04/23 10:01:04 lcf Exp $ *)

include "algebra/CSetoidInc.ma".

include "reals/RealLists.ma".

(* UNEXPORTED
Section Intervals
*)

(*#* * Intervals
In this section we define (compact) intervals of the real line and
some useful functions to work with them.

** Definitions

We start by defining the compact interval [[a,b]] as being the set of
points less or equal than [b] and greater or equal than [a].  We
require [a [<=] b], as we want to work only in nonempty intervals.
*)

inline "cic:/CoRN/reals/Intervals/compact.con".

(*#*
%\begin{convention}% Let [a,b : IR] and [Hab : a [<=] b].
%\end{convention}%

As expected, both [a] and [b] are members of [[a,b]].  Also they are
members of the interval [[Min(a,b),Max(a,b)]].
*)

alias id "a" = "cic:/CoRN/reals/Intervals/Intervals/a.var".

alias id "b" = "cic:/CoRN/reals/Intervals/Intervals/b.var".

alias id "Hab" = "cic:/CoRN/reals/Intervals/Intervals/Hab.var".

inline "cic:/CoRN/reals/Intervals/compact_inc_lft.con".

inline "cic:/CoRN/reals/Intervals/compact_inc_rht.con".

inline "cic:/CoRN/reals/Intervals/compact_Min_lft.con".

inline "cic:/CoRN/reals/Intervals/compact_Min_rht.con".

(*#*
As we will be interested in taking functions with domain in a compact
interval, we want this predicate to be well defined.
*)

inline "cic:/CoRN/reals/Intervals/compact_wd.con".

(*#*
Also, it will sometimes be necessary to rewrite the endpoints of an interval.
*)

inline "cic:/CoRN/reals/Intervals/compact_wd'.con".

(*#*
As we identify subsets with predicates, inclusion is simply implication.
*)

(*#*
Finally, we define a restriction operator that takes a function [F]
and a well defined predicate [P] included in the domain of [F] and
returns the restriction $F|_P$# of F to P#.
*)

inline "cic:/CoRN/reals/Intervals/Frestr.con".

(* UNEXPORTED
End Intervals
*)

(* NOTATION
Notation Compact := (compact _ _).
*)

(* UNEXPORTED
Implicit Arguments Frestr [F P].
*)

(* NOTATION
Notation FRestr := (Frestr (compact_wd _ _ _)).
*)

(* UNEXPORTED
Section More_Intervals
*)

inline "cic:/CoRN/reals/Intervals/included_refl'.con".

(*#* We prove some inclusions of compact intervals.  *)

inline "cic:/CoRN/reals/Intervals/compact_map1.con".

inline "cic:/CoRN/reals/Intervals/compact_map2.con".

inline "cic:/CoRN/reals/Intervals/compact_map3.con".

(* UNEXPORTED
End More_Intervals
*)

(* UNEXPORTED
Hint Resolve included_refl' compact_map1 compact_map2 compact_map3 : included.
*)

(* UNEXPORTED
Section Totally_Bounded
*)

(*#* ** Totally Bounded

Totally bounded sets will play an important role in what is
to come.  The definition (equivalent to the classical one) states that
[P] is totally bounded iff
%\[\forall_{\varepsilon>0}\exists_{x_1,\ldots,x_n}\forall_{y\in P}
\exists_{1\leq i\leq n}|y-x_i|<\varepsilon\]%#&forall;e&gt;0
&exist;x<sub>1</sub>,...,x<sub>n</sub>&forall;y&isin;P&exist;
1&le;i&le;n.|y-x<sub>i</sub>|&lt;e#.

Notice the use of lists for quantification.
*)

inline "cic:/CoRN/reals/Intervals/totally_bounded.con".

(*#*
This definition is classically, but not constructively, equivalent to
the definition of compact (if completeness is assumed); the next
result, classically equivalent to the Heine-Borel theorem, justifies
that we take the definition of totally bounded to be the relevant one
and that we defined compacts as we did.
*)

inline "cic:/CoRN/reals/Intervals/compact_is_totally_bounded.con".

(*#*
Suprema and infima will be needed throughout; we define them here both
for arbitrary subsets of [IR] and for images of functions.
*)

inline "cic:/CoRN/reals/Intervals/set_glb_IR.con".

inline "cic:/CoRN/reals/Intervals/set_lub_IR.con".

inline "cic:/CoRN/reals/Intervals/fun_image.con".

inline "cic:/CoRN/reals/Intervals/fun_glb_IR.con".

inline "cic:/CoRN/reals/Intervals/fun_lub_IR.con".

(* begin hide *)

inline "cic:/CoRN/reals/Intervals/Totally_Bounded/aux_seq_lub.con" "Totally_Bounded__".

inline "cic:/CoRN/reals/Intervals/Totally_Bounded/aux_seq_lub_prop.con" "Totally_Bounded__".

(* end hide *)

(*#*
The following are probably the most important results in this section.
*)

inline "cic:/CoRN/reals/Intervals/totally_bounded_has_lub.con".

(* begin hide *)

inline "cic:/CoRN/reals/Intervals/Totally_Bounded/aux_seq_glb.con" "Totally_Bounded__".

inline "cic:/CoRN/reals/Intervals/Totally_Bounded/aux_seq_glb_prop.con" "Totally_Bounded__".

(* end hide *)

inline "cic:/CoRN/reals/Intervals/totally_bounded_has_glb.con".

(* UNEXPORTED
End Totally_Bounded
*)

(* UNEXPORTED
Section Compact
*)

(*#* ** Compact sets

In this section we dwell a bit farther into the definition of compactness
and explore some of its properties.

The following characterization of inclusion can be very useful:
*)

inline "cic:/CoRN/reals/Intervals/included_compact.con".

(*#*
At several points in our future development of a theory we will need
to partition a compact interval in subintervals of length smaller than
some predefined value [eps]. Although this seems a
consequence of every compact interval being totally bounded, it is in
fact a stronger property.  In this section we perform that
construction (requiring the endpoints of the interval to be distinct)
and prove some of its good properties.

%\begin{convention}% Let [a,b : IR], [Hab : (a [<=] b)] and denote by [I]
the compact interval [[a,b]].  Also assume that [a [<] b], and let [e] be
a positive real number.
%\end{convention}%
*)

alias id "a" = "cic:/CoRN/reals/Intervals/Compact/a.var".

alias id "b" = "cic:/CoRN/reals/Intervals/Compact/b.var".

alias id "Hab" = "cic:/CoRN/reals/Intervals/Compact/Hab.var".

(* begin hide *)

inline "cic:/CoRN/reals/Intervals/Compact/I.con" "Compact__".

(* end hide *)

alias id "Hab'" = "cic:/CoRN/reals/Intervals/Compact/Hab'.var".

alias id "e" = "cic:/CoRN/reals/Intervals/Compact/e.var".

alias id "He" = "cic:/CoRN/reals/Intervals/Compact/He.var".

(*#*
We start by finding a natural number [n] such that [(b[-]a) [/] n [<] e].
*)

inline "cic:/CoRN/reals/Intervals/compact_nat.con".

(*#* Obviously such an [n] must be greater than zero.*)

inline "cic:/CoRN/reals/Intervals/pos_compact_nat.con".

(*#*
We now define a sequence on [n] points in [[a,b]] by
[x_i [=] Min(a,b) [+]i[*] (b[-]a) [/]n] and
prove that all of its points are really in that interval.
*)

inline "cic:/CoRN/reals/Intervals/compact_part.con".

inline "cic:/CoRN/reals/Intervals/compact_part_hyp.con".

(*#*
This sequence is strictly increasing and each two consecutive points
are apart by less than [e].*)

inline "cic:/CoRN/reals/Intervals/compact_less.con".

inline "cic:/CoRN/reals/Intervals/compact_leEq.con".

(*#* When we proceed to integration, this lemma will also be useful: *)

inline "cic:/CoRN/reals/Intervals/compact_partition_lemma.con".

(*#* The next lemma provides an upper bound for the distance between two points in an interval: *)

inline "cic:/CoRN/reals/Intervals/compact_elements.con".

(* UNEXPORTED
Opaque Min Max.
*)

(*#* The following is a variation on the previous lemma: *)

inline "cic:/CoRN/reals/Intervals/compact_elements'.con".

(*#* The following lemma is a bit more specific: it shows that we can
also estimate the distance from the center of a compact interval to
any of its points. *)

inline "cic:/CoRN/reals/Intervals/compact_bnd_AbsIR.con".

(*#* Finally, two more useful lemmas to prove inclusion of compact
intervals.  They will be necessary for the definition and proof of the
elementary properties of the integral.  *)

inline "cic:/CoRN/reals/Intervals/included2_compact.con".

inline "cic:/CoRN/reals/Intervals/included3_compact.con".

(* UNEXPORTED
End Compact
*)

(* UNEXPORTED
Hint Resolve included_compact included2_compact included3_compact : included.
*)

