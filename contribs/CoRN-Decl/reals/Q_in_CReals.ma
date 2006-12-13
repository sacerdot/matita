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

set "baseuri" "cic:/matita/CoRN-Decl/reals/Q_in_CReals".

include "CoRN.ma".

(* $Id: Q_in_CReals.v,v 1.10 2004/04/23 10:01:05 lcf Exp $ *)

(*#* * On density of the image of [Q] in an arbitrary real number structure
In this file we introduce the image of the concrete rational numbers
(as defined earlier) in an arbitrary structure of type
[CReals]. At the end of this file we assign to any real number two
rational numbers for which the real number lies betwen image of them;
in other words we will prove that the image of rational numbers in
dense in any real number structure. *)

include "model/reals/Cauchy_IR.ma".

include "model/monoids/Nmonoid.ma".

include "model/rings/Zring.ma".

(* UNEXPORTED
Section Rational_sequence_prelogue
*)

(*#*
%\begin{convention}% Let [R1] be a real number structure.
%\end{convention}%
*)

alias id "R1" = "cic:/CoRN/reals/Q_in_CReals/Rational_sequence_prelogue/R1.var".

(* We clone these proofs from CReals1.v just because there IR is an axiom *)

(* begin hide *)

inline "cic:/CoRN/reals/Q_in_CReals/CReals_is_CReals.con".

inline "cic:/CoRN/reals/Q_in_CReals/Lim_Cauchy.con".

inline "cic:/CoRN/reals/Q_in_CReals/Archimedes.con".

inline "cic:/CoRN/reals/Q_in_CReals/Archimedes'.con".

(*#**************************************)

coercion cic:/Coq/NArith/BinPos/nat_of_P.con 0 (* compounds *).

(* end hide *)

(*#*
** Injection from [Q] to an arbitrary real number structure
 First we need to define the injection from [Q] to [R1]. Note that in [Cauchy_CReals] we defined [inject_Q] from an arbitray field [F] to [(R_COrdField F)] which was the set of Cauchy sequences of that field. But since [R1] is an %\emph{arbitrary}%#<i>arbitrary</i># real number structure we can not use [inject_Q].

 To define the injection we need one elemntary lemma about the denominator:
*)

inline "cic:/CoRN/reals/Q_in_CReals/den_is_nonzero.con".

(*#* And we define the injection in the natural way, using [zring] and [nring]. We call this [inj_Q], in contrast with [inject_Q] defined in [Cauchy_CReals]. *)

inline "cic:/CoRN/reals/Q_in_CReals/inj_Q.con".

(*#* Next we need some properties of [nring], on the setoid of natural numbers: *)

inline "cic:/CoRN/reals/Q_in_CReals/nring_strext.con".

inline "cic:/CoRN/reals/Q_in_CReals/nring_wd.con".

inline "cic:/CoRN/reals/Q_in_CReals/nring_eq.con".

inline "cic:/CoRN/reals/Q_in_CReals/nring_leEq.con".

(* begin hide *)

(* UNEXPORTED
Unset Printing Coercions.
*)

(* end hide *)

(*#* Similarly we prove some properties of [zring] on the ring of integers: *)

inline "cic:/CoRN/reals/Q_in_CReals/zring_strext.con".

inline "cic:/CoRN/reals/Q_in_CReals/zring_wd.con".

inline "cic:/CoRN/reals/Q_in_CReals/zring_less.con".

(*#* Using the above lemmata we prove the basic properties of [inj_Q], i.e.%\% it is a setoid function and preserves the ring operations and oreder operation. *)

inline "cic:/CoRN/reals/Q_in_CReals/inj_Q_strext.con".

inline "cic:/CoRN/reals/Q_in_CReals/inj_Q_wd.con".

inline "cic:/CoRN/reals/Q_in_CReals/inj_Q_plus.con".

inline "cic:/CoRN/reals/Q_in_CReals/inj_Q_mult.con".

inline "cic:/CoRN/reals/Q_in_CReals/inj_Q_less.con".

inline "cic:/CoRN/reals/Q_in_CReals/less_inj_Q.con".

inline "cic:/CoRN/reals/Q_in_CReals/leEq_inj_Q.con".

inline "cic:/CoRN/reals/Q_in_CReals/inj_Q_leEq.con".

inline "cic:/CoRN/reals/Q_in_CReals/inj_Q_min.con".

inline "cic:/CoRN/reals/Q_in_CReals/inj_Q_minus.con".

(*#* Moreover, and as expected, the [AbsSmall] predicate is also
preserved under the [inj_Q] *)

inline "cic:/CoRN/reals/Q_in_CReals/inj_Q_AbsSmall.con".

inline "cic:/CoRN/reals/Q_in_CReals/AbsSmall_inj_Q.con".

(*#* ** Injection preserves Cauchy property
We apply the above lemmata to obtain following theorem, which says
that a Cauchy sequence of elemnts of [Q] will be Cauchy in [R1].
*)

inline "cic:/CoRN/reals/Q_in_CReals/inj_Q_Cauchy.con".

(*#* Furthermore we prove that applying [nring] (which is adding the
ring unit [n] times) is the same whether we do it in [Q] or in [R1]:
*)

inline "cic:/CoRN/reals/Q_in_CReals/inj_Q_nring.con".

(*#* ** Injection of [Q] is dense
Finally we are able to prove the density of image of [Q] in [R1]. We
state this fact in two different ways. Both of them have their
specific use.

The first theorem states the fact that any real number can be bound by
the image of two rational numbers. This is called [start_of_sequence]
because it can be used as an starting point for the typical "interval
trisection" argument, which is ubiquitous in constructive analysis.
*)

inline "cic:/CoRN/reals/Q_in_CReals/start_of_sequence.con".

(*#* The second version of the density of [Q] in [R1] states that given
any positive real number, there is a rational number between it and
zero. This lemma can be used to prove the more general fact that there
is a rational number between any two real numbers. *)

inline "cic:/CoRN/reals/Q_in_CReals/Q_dense_in_CReals.con".

(* UNEXPORTED
End Rational_sequence_prelogue
*)

