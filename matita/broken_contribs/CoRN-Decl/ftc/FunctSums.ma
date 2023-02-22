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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/FunctSums".

include "CoRN.ma".

(* $Id: FunctSums.v,v 1.5 2004/04/23 10:00:59 lcf Exp $ *)

(*#* printing FSum0 %\ensuremath{\sum_0}% #&sum;<sub>0</sub># *)

(*#* printing FSum %\ensuremath{\sum}% #&sum;# *)

(*#* printing FSumx %\ensuremath{\sum'}% #&sum;'&*)

include "reals/CSumsReals.ma".

include "ftc/PartFunEquality.ma".

(*#* *Sums of Functions

In this file we define sums are defined of arbitrary families of
partial functions.

Given a countable family of functions, their sum is defined on the
intersection of all the domains.  As is the case for groups, we will
define three different kinds of sums.

We will first consider the case of a family
$\{f_i\}_{i\in\NN}$#{f<sub>i</sub>}# of functions; we can both define
$\sum_{i=0}^{n-1}f_i$#the sum of the first n functions# ( [FSum0]) or
$\sum_{i=m}^nf_i$#the sum of f<sub>m</sub> through f<sub>n</sub>#
( [FSum]).
*)

inline "cic:/CoRN/ftc/FunctSums/FSum0.con".

inline "cic:/CoRN/ftc/FunctSums/FSum.con".

(*#*
Although [FSum] is here defined directly, it has the same relationship
to the [FSum0] operator as [Sum] has to [Sum0].  Also, all the results
for [Sum] and [Sum0] hold when these operators are replaced by their
functional equivalents.  This is an immediate consequence of the fact
that the partial functions form a group; however, as we already
mentioned, their forming too big a type makes it impossible to use
those results.
*)

inline "cic:/CoRN/ftc/FunctSums/FSum_FSum0.con".

inline "cic:/CoRN/ftc/FunctSums/FSum0_wd.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_one.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_FSum.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_first.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_last.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_last'.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_wd.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_plus_FSum.con".

inline "cic:/CoRN/ftc/FunctSums/inv_FSum.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_minus_FSum.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_wd'.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_resp_less.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_resp_leEq.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_comm_scal.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_comm_scal'.con".

(*#*
Also important is the case when we have a finite family
$\{f_i\}_{i=0}^{n-1}$ of #exactly n# functions; in this case we need
to use the [FSumx] operator.
*)

inline "cic:/CoRN/ftc/FunctSums/FSumx.con".

(*#*
This operator is well defined, as expected.
*)

inline "cic:/CoRN/ftc/FunctSums/FSumx_wd.con".

inline "cic:/CoRN/ftc/FunctSums/FSumx_wd'.con".

(*#*
As was already the case for [Sumx], in many cases we will need to
explicitly assume that $f_i$#f<sub>1</sub># is independent of the proof that
[i [<] n].  This holds both for the value and the domain of the partial
function $f_i$#f<sub>i</sub>#.
*)

inline "cic:/CoRN/ftc/FunctSums/ext_fun_seq.con".

inline "cic:/CoRN/ftc/FunctSums/ext_fun_seq'.con".

(* UNEXPORTED
Implicit Arguments ext_fun_seq [n].
*)

(* UNEXPORTED
Implicit Arguments ext_fun_seq' [n].
*)

(*#*
Under these assumptions, we can characterize the domain and the value of the sum function from the domains and values of the summands:
*)

inline "cic:/CoRN/ftc/FunctSums/FSumx_pred.con".

inline "cic:/CoRN/ftc/FunctSums/FSumx_pred'.con".

inline "cic:/CoRN/ftc/FunctSums/FSumx_char.con".

(*#*
As we did for arbitrary groups, it is often useful to rewrite this sums as ordinary sums.
*)

inline "cic:/CoRN/ftc/FunctSums/FSumx_to_FSum.con".

inline "cic:/CoRN/ftc/FunctSums/FSumx_lt.con".

inline "cic:/CoRN/ftc/FunctSums/FSumx_le.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_FSumx_to_FSum.con".

(*#*
Some useful lemmas follow.
*)

inline "cic:/CoRN/ftc/FunctSums/FSum0_0.con".

inline "cic:/CoRN/ftc/FunctSums/FSum0_S.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_0.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_S.con".

inline "cic:/CoRN/ftc/FunctSums/FSum_FSum0'.con".

