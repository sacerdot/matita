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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/Rolle".

(* $Id: Rolle.v,v 1.6 2004/04/23 10:01:01 lcf Exp $ *)

(* INCLUDE
DiffTactics2
*)

(* INCLUDE
MoreFunctions
*)

(* UNEXPORTED
Section Rolle.
*)

(*#* *Rolle's Theorem

We now begin to work with partial functions.  We begin by stating and proving Rolle's theorem in various forms and some of its corollaries.

%\begin{convention}% Assume that:
 - [a,b:IR] with [a [<] b] and denote by [I] the interval [[a,b]];
 - [F,F'] are partial functions such that [F'] is the derivative of [F] in [I];
 - [e] is a positive real number.

%\end{convention}%
*)

(* begin hide *)

inline cic:/CoRN/ftc/Rolle/a.var.

inline cic:/CoRN/ftc/Rolle/b.var.

inline cic:/CoRN/ftc/Rolle/Hab'.var.

inline cic:/CoRN/ftc/Rolle/Hab.con.

inline cic:/CoRN/ftc/Rolle/I.con.

inline cic:/CoRN/ftc/Rolle/F.var.

inline cic:/CoRN/ftc/Rolle/F'.var.

inline cic:/CoRN/ftc/Rolle/derF.var.

inline cic:/CoRN/ftc/Rolle/Ha.var.

inline cic:/CoRN/ftc/Rolle/Hb.var.

(* end hide *)

(* begin show *)

inline cic:/CoRN/ftc/Rolle/Fab.var.

(* end show *)

(* begin hide *)

inline cic:/CoRN/ftc/Rolle/e.var.

inline cic:/CoRN/ftc/Rolle/He.var.

inline cic:/CoRN/ftc/Rolle/contF'.con.

inline cic:/CoRN/ftc/Rolle/derivF.con.

inline cic:/CoRN/ftc/Rolle/Rolle_lemma2.con.

inline cic:/CoRN/ftc/Rolle/df.con.

inline cic:/CoRN/ftc/Rolle/Hdf.con.

inline cic:/CoRN/ftc/Rolle/Hf.con.

inline cic:/CoRN/ftc/Rolle/Rolle_lemma3.con.

inline cic:/CoRN/ftc/Rolle/df'.con.

inline cic:/CoRN/ftc/Rolle/Hdf'.con.

inline cic:/CoRN/ftc/Rolle/Hf'.con.

inline cic:/CoRN/ftc/Rolle/d.con.

inline cic:/CoRN/ftc/Rolle/Hd.con.

inline cic:/CoRN/ftc/Rolle/incF.con.

inline cic:/CoRN/ftc/Rolle/n.con.

inline cic:/CoRN/ftc/Rolle/fcp.con.

inline cic:/CoRN/ftc/Rolle/Rolle_lemma1.con.

inline cic:/CoRN/ftc/Rolle/incF'.con.

inline cic:/CoRN/ftc/Rolle/fcp'.con.

inline cic:/CoRN/ftc/Rolle/Rolle_lemma4.con.

inline cic:/CoRN/ftc/Rolle/Rolle_lemma5.con.

inline cic:/CoRN/ftc/Rolle/Rolle_lemma6.con.

inline cic:/CoRN/ftc/Rolle/Rolle_lemma7.con.

inline cic:/CoRN/ftc/Rolle/j.con.

inline cic:/CoRN/ftc/Rolle/Hj.con.

inline cic:/CoRN/ftc/Rolle/Hj'.con.

inline cic:/CoRN/ftc/Rolle/k.con.

inline cic:/CoRN/ftc/Rolle/Hk.con.

inline cic:/CoRN/ftc/Rolle/Hk'.con.

inline cic:/CoRN/ftc/Rolle/Rolle_lemma8.con.

inline cic:/CoRN/ftc/Rolle/Rolle_lemma9.con.

inline cic:/CoRN/ftc/Rolle/Rolle_lemma10.con.

inline cic:/CoRN/ftc/Rolle/Rolle_lemma11.con.

inline cic:/CoRN/ftc/Rolle/Rolle_lemma12.con.

inline cic:/CoRN/ftc/Rolle/Rolle_lemma13.con.

inline cic:/CoRN/ftc/Rolle/Rolle_lemma15.con.

(* end hide *)

inline cic:/CoRN/ftc/Rolle/Rolle.con.

(* UNEXPORTED
End Rolle.
*)

(* UNEXPORTED
Section Law_of_the_Mean.
*)

(*#*
The following is a simple corollary:
*)

inline cic:/CoRN/ftc/Rolle/a.var.

inline cic:/CoRN/ftc/Rolle/b.var.

inline cic:/CoRN/ftc/Rolle/Hab'.var.

(* begin hide *)

inline cic:/CoRN/ftc/Rolle/Hab.con.

inline cic:/CoRN/ftc/Rolle/I.con.

(* end hide *)

inline cic:/CoRN/ftc/Rolle/F.var.

inline cic:/CoRN/ftc/Rolle/F'.var.

inline cic:/CoRN/ftc/Rolle/HF.var.

(* begin show *)

inline cic:/CoRN/ftc/Rolle/HA.var.

inline cic:/CoRN/ftc/Rolle/HB.var.

(* end show *)

inline cic:/CoRN/ftc/Rolle/Law_of_the_Mean_I.con.

(* UNEXPORTED
End Law_of_the_Mean.
*)

(* UNEXPORTED
Section Corollaries.
*)

(*#*
We can also state these theorems without expliciting the derivative of [F].
*)

inline cic:/CoRN/ftc/Rolle/a.var.

inline cic:/CoRN/ftc/Rolle/b.var.

inline cic:/CoRN/ftc/Rolle/Hab'.var.

(* begin hide *)

inline cic:/CoRN/ftc/Rolle/Hab.con.

(* end hide *)

inline cic:/CoRN/ftc/Rolle/F.var.

(* begin show *)

inline cic:/CoRN/ftc/Rolle/HF.var.

(* end show *)

inline cic:/CoRN/ftc/Rolle/Rolle'.con.

inline cic:/CoRN/ftc/Rolle/Law_of_the_Mean'_I.con.

(* UNEXPORTED
End Corollaries.
*)

(* UNEXPORTED
Section Generalizations.
*)

(*#*
The mean law is more useful if we abstract [a] and [b] from the
context---allowing them in particular to be equal.  In the case where
[F(a) [=] F(b)] we get Rolle's theorem again, so there is no need to
state it also in this form.

%\begin{convention}% Assume [I] is a proper interval, [F,F':PartIR].
%\end{convention}%
*)

inline cic:/CoRN/ftc/Rolle/I.var.

inline cic:/CoRN/ftc/Rolle/pI.var.

inline cic:/CoRN/ftc/Rolle/F.var.

inline cic:/CoRN/ftc/Rolle/F'.var.

(* begin show *)

inline cic:/CoRN/ftc/Rolle/derF.var.

(* end show *)

(* begin hide *)

inline cic:/CoRN/ftc/Rolle/incF.con.

inline cic:/CoRN/ftc/Rolle/incF'.con.

(* end hide *)

inline cic:/CoRN/ftc/Rolle/Law_of_the_Mean.con.

(*#*
We further generalize the mean law by writing as an explicit bound.
*)

inline cic:/CoRN/ftc/Rolle/Law_of_the_Mean_ineq.con.

(* UNEXPORTED
End Generalizations.
*)

