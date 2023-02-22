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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/WeakIVT".

include "CoRN.ma".

(* $Id: WeakIVT.v,v 1.9 2004/04/23 10:01:01 lcf Exp $ *)

(*#* printing ** %\ensuremath\times% #&times;# *)

(* begin hide *)

(* NOTATION
Infix "**" := prodT (at level 20).
*)

(* end hide *)

include "ftc/Continuity.ma".

(*#* *IVT for Partial Functions

In general, we cannot prove the classically valid Intermediate Value
Theorem for arbitrary partial functions, which states that in any
interval [[a,b]], for any value [z] between [f(a)] and [f(b)]
there exists $x\in[a,b]$#x&isin;[a,b]# such that [f(x) [=] z].

However, as is usually the case, there are some good aproximation results.  We
will prove them here.
*)

(* UNEXPORTED
Section Lemma1
*)

alias id "a" = "cic:/CoRN/ftc/WeakIVT/Lemma1/a.var".

alias id "b" = "cic:/CoRN/ftc/WeakIVT/Lemma1/b.var".

alias id "Hab" = "cic:/CoRN/ftc/WeakIVT/Lemma1/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/WeakIVT/Lemma1/I.con" "Lemma1__".

(* end hide *)

alias id "F" = "cic:/CoRN/ftc/WeakIVT/Lemma1/F.var".

alias id "contF" = "cic:/CoRN/ftc/WeakIVT/Lemma1/contF.var".

(*#* **First Lemmas

%\begin{convention}% Let [a, b : IR] and [Hab : a [<=] b] and denote by [I]
the interval [[a,b]].  Let [F] be a continuous function on [I].
%\end{convention}%

We begin by proving that, if [f(a) [<] f(b)], then for every [y] in 
[[f(a),f(b)]] there is an $x\in[a,b]$#x&isin;[a,b]# such that [f(x)] is close
enough to [z].
*)

inline "cic:/CoRN/ftc/WeakIVT/Weak_IVT_ap_lft.con".

(* UNEXPORTED
End Lemma1
*)

(* UNEXPORTED
Section Lemma2
*)

alias id "a" = "cic:/CoRN/ftc/WeakIVT/Lemma2/a.var".

alias id "b" = "cic:/CoRN/ftc/WeakIVT/Lemma2/b.var".

alias id "Hab" = "cic:/CoRN/ftc/WeakIVT/Lemma2/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/WeakIVT/Lemma2/I.con" "Lemma2__".

(* end hide *)

alias id "F" = "cic:/CoRN/ftc/WeakIVT/Lemma2/F.var".

alias id "contF" = "cic:/CoRN/ftc/WeakIVT/Lemma2/contF.var".

(*#*
If [f(b) [<] f(a)], a similar result holds:
*)

inline "cic:/CoRN/ftc/WeakIVT/Weak_IVT_ap_rht.con".

(* UNEXPORTED
End Lemma2
*)

(* UNEXPORTED
Section IVT
*)

(*#* **The IVT

We will now assume that [a [<] b] and that [F] is not only
continuous, but also strictly increasing in [I].  Under
these assumptions, we can build two sequences of values which
converge to [x0] such that [f(x0) [=] z].
*)

alias id "a" = "cic:/CoRN/ftc/WeakIVT/IVT/a.var".

alias id "b" = "cic:/CoRN/ftc/WeakIVT/IVT/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/WeakIVT/IVT/Hab'.var".

alias id "Hab" = "cic:/CoRN/ftc/WeakIVT/IVT/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/WeakIVT/IVT/I.con" "IVT__".

(* end hide *)

alias id "F" = "cic:/CoRN/ftc/WeakIVT/IVT/F.var".

alias id "contF" = "cic:/CoRN/ftc/WeakIVT/IVT/contF.var".

(* begin hide *)

inline "cic:/CoRN/ftc/WeakIVT/IVT/incF.con" "IVT__".

(* end hide *)

(* begin show *)

alias id "incrF" = "cic:/CoRN/ftc/WeakIVT/IVT/incrF.var".

(* end show *)

(* begin hide *)

inline "cic:/CoRN/ftc/WeakIVT/IVT/Ha.con" "IVT__".

inline "cic:/CoRN/ftc/WeakIVT/IVT/Hb.con" "IVT__".

inline "cic:/CoRN/ftc/WeakIVT/IVT/HFab'.con" "IVT__".

(* end hide *)

(* begin show *)

alias id "z" = "cic:/CoRN/ftc/WeakIVT/IVT/z.var".

alias id "Haz" = "cic:/CoRN/ftc/WeakIVT/IVT/Haz.var".

alias id "Hzb" = "cic:/CoRN/ftc/WeakIVT/IVT/Hzb.var".

(* end show *)

(*#* Given any two points [x [<] y] in [[a,b]] such that [x [<=] z [<=] y],
we can find [x' [<] y'] such that $|x'-y'|=\frac23|x-y|$#|x'-y'|=2/3|x-y|#
and [x' [<=] z [<=] y'].
*)

inline "cic:/CoRN/ftc/WeakIVT/IVT_seq_lemma.con".

(* end hide *)

(*#*
We now iterate this construction.
*)

inline "cic:/CoRN/ftc/WeakIVT/IVT_aux_seq_type.ind".

inline "cic:/CoRN/ftc/WeakIVT/IVT_iter.con".

inline "cic:/CoRN/ftc/WeakIVT/IVT_seq.con".

(*#*
We now define the sequences built from this iteration, starting with [a] and [b].
*)

inline "cic:/CoRN/ftc/WeakIVT/a_seq.con".

inline "cic:/CoRN/ftc/WeakIVT/b_seq.con".

inline "cic:/CoRN/ftc/WeakIVT/a_seq_I.con".

inline "cic:/CoRN/ftc/WeakIVT/b_seq_I.con".

inline "cic:/CoRN/ftc/WeakIVT/a_seq_less_b_seq.con".

inline "cic:/CoRN/ftc/WeakIVT/a_seq_leEq_z.con".

inline "cic:/CoRN/ftc/WeakIVT/z_leEq_b_seq.con".

inline "cic:/CoRN/ftc/WeakIVT/a_seq_mon.con".

inline "cic:/CoRN/ftc/WeakIVT/b_seq_mon.con".

inline "cic:/CoRN/ftc/WeakIVT/a_seq_b_seq_dist_n.con".

inline "cic:/CoRN/ftc/WeakIVT/a_seq_b_seq_dist.con".

inline "cic:/CoRN/ftc/WeakIVT/a_seq_Cauchy.con".

inline "cic:/CoRN/ftc/WeakIVT/b_seq_Cauchy.con".

inline "cic:/CoRN/ftc/WeakIVT/IVT/xa.con" "IVT__".

inline "cic:/CoRN/ftc/WeakIVT/IVT/xb.con" "IVT__".

inline "cic:/CoRN/ftc/WeakIVT/a_seq_b_seq_lim.con".

inline "cic:/CoRN/ftc/WeakIVT/xa_in_interval.con".

inline "cic:/CoRN/ftc/WeakIVT/IVT_I.con".

(* UNEXPORTED
End IVT
*)

