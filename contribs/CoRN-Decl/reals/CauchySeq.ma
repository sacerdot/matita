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

set "baseuri" "cic:/matita/CoRN-Decl/reals/CauchySeq".

include "CoRN.ma".

(* $Id: CauchySeq.v,v 1.8 2004/04/23 10:01:04 lcf Exp $ *)

(*#* printing IR %\ensuremath{\mathbb R}% *)

(*#* printing PartIR %\ensuremath{\mathbb R\!\not\rightarrow\!\mathbb R}% *)

(*#* printing ZeroR %\ensuremath{\mathbf0}% #0# *)

(*#* printing OneR %\ensuremath{\mathbf1}% #1# *)

(*#* printing AbsIR %\ensuremath{|\cdot|_{\mathbb R}}% *)

include "reals/CReals.ma".

(*#* *Real Number Structures
%\begin{convention}% Let [IR] be a structure for real numbers.
%\end{convention}%
*)

(*
Require Export R_CReals.
Definition IR : CReals := Concrete_R.
Opaque IR.
*)

alias id "IR" = "cic:/CoRN/reals/CauchySeq/IR.var".

(* NOTATION
Notation PartIR := (PartFunct IR).
*)

(* NOTATION
Notation ProjIR1 := (prj1 IR _ _ _).
*)

(* NOTATION
Notation ProjIR2 := (prj2 IR _ _ _).
*)

include "tactics/Transparent_algebra.ma".

(* begin hide *)

(* NOTATION
Notation ZeroR := (Zero:IR).
*)

(* NOTATION
Notation OneR := (One:IR).
*)

(* end hide *)

(* UNEXPORTED
Section CReals_axioms
*)

(*#* ** [CReals] axioms *)

inline "cic:/CoRN/reals/CauchySeq/CReals_is_CReals.con".

(*#* First properties which follow trivially from the axioms.  *)

inline "cic:/CoRN/reals/CauchySeq/Lim_Cauchy.con".

inline "cic:/CoRN/reals/CauchySeq/Archimedes.con".

inline "cic:/CoRN/reals/CauchySeq/Archimedes'.con".

(*#* A stronger version, which often comes in useful.  *)

inline "cic:/CoRN/reals/CauchySeq/str_Archimedes.con".

inline "cic:/CoRN/reals/CauchySeq/CauchySeqR.con".

(* UNEXPORTED
End CReals_axioms
*)

(* UNEXPORTED
Section Cauchy_Defs
*)

(*#* ** Cauchy sequences
*** Alternative definitions
This section gives several definitions of Cauchy sequences. There
are no lemmas in this section.

The current definition of Cauchy ([Cauchy_prop]) is:

%\[\forall \epsilon>0. \exists N. \forall m\geq N. |seq_m - seq_N|\leq\varepsilon\]%
#for all e&gt;0 there exists N such that for all m&ge; N |seqm-seqN|&le; e#

Variant 1 of Cauchy ([Cauchy_prop1]) is:

%\[\forall k. \exists N. \forall m \geq N. |seq_m - seq_N|\leq1/(k+1)\]%
#for all k there exists N such that for all m &ge; N |seqm-seqN| &le; 1/(k+1)#

In all of the following variants the limit occurs in the definition.
Therefore it is useful to define an auxiliary predicate
[Cauchy_Lim_prop?], in terms of which [Cauchy_prop?] is defined.

Variant 2 of Cauchy ([Cauchy_prop2]) is [exists y, (Cauchy_Lim_prop2 seq y)]
where
[[
Cauchy_Lim_prop2 seq y := forall eps [>] Zero, exists N, forall m >= N, (AbsIR seq m - y) [<=] eps
]]

Note that [Cauchy_Lim_prop2] equals [seqLimit].

Variant 3 of Cauchy ([Cauchy_prop3]) reads [exists y, (Cauchy_Lim_prop3 seq y)]
where
[[
Cauchy_Lim_prop3 seq y := forall k, exists N, forall m >= N, (AbsIR seq m - y) [<=] One[/] (k[+]1)
]]

The following variant is more restricted.

Variant 4 of Cauchy ([Cauchy_prop4]): [exists y, (Cauchy_Lim_prop4 seq y)]
where
[[
Cauchy_Lim_prop4 seq y := forall k, (AbsIR seq m - y) [<=] One[/] (k[+]1)
]]

So
[[
Cauchy_prop4 -> Cauchy_prop3 Iff Cauchy_prop2 Iff Cauchy_prop1 Iff Cauchy_prop
]]
Note: we don't know which formulations are useful.

The inequalities are stated with [[<=]] rather than with [<] for the
following reason: both formulations are equivalent, as is well known;
and [[<=]] being a negative statement, this makes proofs
sometimes easier and program extraction much more efficient.
*)

inline "cic:/CoRN/reals/CauchySeq/Cauchy_prop1.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_Lim_prop2.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_prop2.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_Lim_prop3.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_prop3.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_Lim_prop4.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_prop4.con".

(* UNEXPORTED
End Cauchy_Defs
*)

(* UNEXPORTED
Section Inequalities
*)

(*#* *** Inequalities of Limits

The next lemma is equal to lemma [Lim_Cauchy].  *)

inline "cic:/CoRN/reals/CauchySeq/Cauchy_complete.con".

inline "cic:/CoRN/reals/CauchySeq/less_Lim_so_less_seq.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_less_so_seq_less.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_less_Lim_so_seq_less_seq.con".

(*#* The next lemma follows from [less_Lim_so_less_seq] with [y := (y[+] (Lim seq)) [/]TwoNZ].  *)

inline "cic:/CoRN/reals/CauchySeq/less_Lim_so.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_less_so.con".

inline "cic:/CoRN/reals/CauchySeq/leEq_seq_so_leEq_Lim.con".

inline "cic:/CoRN/reals/CauchySeq/str_leEq_seq_so_leEq_Lim.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_leEq_Lim.con".

inline "cic:/CoRN/reals/CauchySeq/seq_leEq_so_Lim_leEq.con".

inline "cic:/CoRN/reals/CauchySeq/str_seq_leEq_so_Lim_leEq.con".

inline "cic:/CoRN/reals/CauchySeq/Limits_unique.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_wd.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_strext.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_ap_imp_seq_ap.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_ap_imp_seq_ap'.con".

(* UNEXPORTED
End Inequalities
*)

(* UNEXPORTED
Section Equiv_Cauchy
*)

(*#* *** Equivalence of formulations of Cauchy *)

inline "cic:/CoRN/reals/CauchySeq/Cauchy_prop1_prop.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_prop2_prop.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_Lim_prop3_prop2.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_prop3_prop2.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_prop3_prop.con".

inline "cic:/CoRN/reals/CauchySeq/Build_CauchySeq1.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_Lim_prop4_prop3.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_Lim_prop4_prop2.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_prop4_prop3.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_prop4_prop.con".

inline "cic:/CoRN/reals/CauchySeq/Build_CauchySeq4.con".

inline "cic:/CoRN/reals/CauchySeq/Build_CauchySeq4_y.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_CauchySeq4.con".

inline "cic:/CoRN/reals/CauchySeq/Build_CauchySeq2.con".

inline "cic:/CoRN/reals/CauchySeq/Build_CauchySeq2_y.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_CauchySeq2.con".

(*#* Well definedness. *)

inline "cic:/CoRN/reals/CauchySeq/Cauchy_prop_wd.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_Lim_prop2_wd.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_wd'.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_unique.con".

(* UNEXPORTED
End Equiv_Cauchy
*)

(* UNEXPORTED
Section Cauchy_props
*)

(*#* *** Properties of Cauchy sequences

Some of these lemmas are now obsolete, because they were reproved for arbitrary ordered fields$\ldots$#...#

We begin by defining the constant sequence and proving that it is Cauchy with the expected limit.
*)

inline "cic:/CoRN/reals/CauchySeq/Cauchy_const.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_const.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_Lim_plus.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_plus.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_plus.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_Lim_inv.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_inv.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_inv.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_Lim_minus.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_minus.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_minus.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_Lim_mult.con".

inline "cic:/CoRN/reals/CauchySeq/Cauchy_mult.con".

inline "cic:/CoRN/reals/CauchySeq/Lim_mult.con".

(* UNEXPORTED
End Cauchy_props
*)

