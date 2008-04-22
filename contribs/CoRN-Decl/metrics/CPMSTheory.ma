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

set "baseuri" "cic:/matita/CoRN-Decl/metrics/CPMSTheory".

include "CoRN.ma".

(* $Id: CPMSTheory.v,v 1.6 2004/04/23 10:01:02 lcf Exp $ *)

include "metrics/Prod_Sub.ma".

(* UNEXPORTED
Section lists
*)

(*#* **Lists
*)

(*#*
 List and membership of lists are used in the definition of 
%''totally bounded''% #"totally bounded"#. Note that we use the Leibniz equality in the definition 
of [MSmember], and not the setoid equality. So we are really talking about
finite sets of representants, instead of finite subsetoids. This seems to make
 the proofs a bit easier.
*)

inline "cic:/CoRN/metrics/CPMSTheory/MSmember.con".

(* UNEXPORTED
Implicit Arguments MSmember [X].
*)

inline "cic:/CoRN/metrics/CPMSTheory/to_IR.con".

inline "cic:/CoRN/metrics/CPMSTheory/from_IR.con".

inline "cic:/CoRN/metrics/CPMSTheory/list_IR.con".

inline "cic:/CoRN/metrics/CPMSTheory/is_P.con".

(*#*
If a real number is element of a list in the above defined sense,
it is an element of the list in the sense of [member], 
that uses the setoid equality.
*)

inline "cic:/CoRN/metrics/CPMSTheory/member1.con".

(*#*
The image under a certain mapping of an element of a list $l$ #<I>l</I># is member 
of the list of images of elements of $l$ #<I>l</I>#.
*)

inline "cic:/CoRN/metrics/CPMSTheory/map_member.con".

(* UNEXPORTED
End lists
*)

(* UNEXPORTED
Section loc_and_bound
*)

(*#* **Pseudo Metric Space theory
*)

inline "cic:/CoRN/metrics/CPMSTheory/Re_co_do.con".

inline "cic:/CoRN/metrics/CPMSTheory/Re_co_do_strext.con".

inline "cic:/CoRN/metrics/CPMSTheory/re_co_do.con".

inline "cic:/CoRN/metrics/CPMSTheory/re_co_do_well_def.con".

(* UNEXPORTED
Implicit Arguments MSmember [X].
*)

(*#*
Again we see that the image under a certain mapping of an element of a list $l$
#<I>l</I># is member of the list of images of elements of $l$ #<I>l</I>#.
*)

inline "cic:/CoRN/metrics/CPMSTheory/map_member'.con".

inline "cic:/CoRN/metrics/CPMSTheory/bounded.con".

inline "cic:/CoRN/metrics/CPMSTheory/MStotally_bounded.con".

(*#*
Total boundedness is preserved under uniformly continuous mappings.
*)

(* UNEXPORTED
Implicit Arguments SubPsMetricSpace [X].
*)

inline "cic:/CoRN/metrics/CPMSTheory/unicon_resp_totallybounded.con".

inline "cic:/CoRN/metrics/CPMSTheory/MStotallybounded_totallybounded.con".

(*#*
Every image under an uniformly continuous function of an totally bounded 
pseudo metric space has an infimum and a supremum.
*)

inline "cic:/CoRN/metrics/CPMSTheory/infimum_exists.con".

inline "cic:/CoRN/metrics/CPMSTheory/supremum_exists.con".

(*#*
A subspace $P$#<I>P</I># of a pseudo metric space $X$#<I>X</I># is said to be located if for all 
elements $x$#<I>x</I># of $X$#<I>X</I># there exists an infimum for the distance 
between $x$#<I>x</I># and the elements of $P$#<I>P</I>#.
*)

(* UNEXPORTED
Implicit Arguments dsub'_as_cs_fun [X].
*)

inline "cic:/CoRN/metrics/CPMSTheory/located.con".

(* UNEXPORTED
Implicit Arguments located [X].
*)

inline "cic:/CoRN/metrics/CPMSTheory/located'.con".

(* UNEXPORTED
Implicit Arguments located' [X].
*)

inline "cic:/CoRN/metrics/CPMSTheory/located_imp_located'.con".

(*#*
Every totally bounded pseudo metric space is located.
*)

inline "cic:/CoRN/metrics/CPMSTheory/MStotally_bounded_imp_located.con".

(*#*
For all $x$#<I>x</I># in a pseudo metric space $X$#<I>X</I>#, for all located subspaces $P$#<I>P</I># of $X$#<I>X</I>#,
[Floc] chooses for a given natural number $n$#<I>n</I># an $y$#<I>y</I># in $P$#<I>P</I># such that:
$d(x,y)\leq \mbox{inf}\{d(x,p)|p \in P\}+(n+1)^{-1}$
#d(x,y) &le; inf&#x007B;d(x,p)&#x007C; p&#x03F5;P&#x007D; + (n+1)<SUP>-1</SUP>#.
[Flocfun] does (almost) the same, but has a different type. This enables 
one to use the latter as an argument of [map].
*)

inline "cic:/CoRN/metrics/CPMSTheory/Floc.con".

inline "cic:/CoRN/metrics/CPMSTheory/Flocfun.con".

(*#*
A located subset $P$#<I>P</I># of a totally bounded pseudo metric space $X$
#<I>X</I># is totally
bounded.
*)

inline "cic:/CoRN/metrics/CPMSTheory/locatedsub_totallybounded_imp_totallyboundedsub.con".

(*#*
Here are some definitions that could come in handy:
*)

inline "cic:/CoRN/metrics/CPMSTheory/MSCauchy_seq.con".

(* UNEXPORTED
Implicit Arguments MSseqLimit' [X].
*)

inline "cic:/CoRN/metrics/CPMSTheory/MSComplete.con".

(*#*
A compact pseudo metric space is a pseudo metric space which is complete and 
totally bounded.
*)

inline "cic:/CoRN/metrics/CPMSTheory/MSCompact.con".

(*#*
A subset $P$#<I>P</I># is %\emph{open}%#<I>open</I># if for all $x$#<I>x</I># in $P$#<I>P</I># there exists an open sphere 
with centre $x$#<I>x</I># that is contained in $P$#<I>P</I>#.
*)

inline "cic:/CoRN/metrics/CPMSTheory/open.con".

(* UNEXPORTED
Implicit Arguments open [X].
*)

(*#*
The operator [infima] gives the infimum for the distance between an 
element $x$#<I>x</I># of a located pseudo metric space $X$#<I>X</I># and the elements of a 
subspace $P$#<I>P</I># of $X$#<I>X</I>#.
*)

inline "cic:/CoRN/metrics/CPMSTheory/infima.con".

(* UNEXPORTED
Implicit Arguments infima [X].
*)

(*#*
A non-empty totally bounded sub-pseudo-metric-space $P$#<I>P</I># is said to be 
%\emph{well contained}% #<I>well contained</I># in an open sub-pseudo-metric-space $Q$#<I>Q</I># if $Q$#<I>Q</I># contains 
all points that are in some sense close to $P$#<I>P</I>#.
*)

inline "cic:/CoRN/metrics/CPMSTheory/well_contained.con".

(* UNEXPORTED
End loc_and_bound
*)

