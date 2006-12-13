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

include "CoRN.ma".

(* $Id: Rolle.v,v 1.6 2004/04/23 10:01:01 lcf Exp $ *)

include "tactics/DiffTactics2.ma".

include "ftc/MoreFunctions.ma".

(* UNEXPORTED
Section Rolle
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

alias id "a" = "cic:/CoRN/ftc/Rolle/Rolle/a.var".

alias id "b" = "cic:/CoRN/ftc/Rolle/Rolle/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/Rolle/Rolle/Hab'.var".

inline "cic:/CoRN/ftc/Rolle/Rolle/Hab.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/I.con" "Rolle__".

alias id "F" = "cic:/CoRN/ftc/Rolle/Rolle/F.var".

alias id "F'" = "cic:/CoRN/ftc/Rolle/Rolle/F'.var".

alias id "derF" = "cic:/CoRN/ftc/Rolle/Rolle/derF.var".

alias id "Ha" = "cic:/CoRN/ftc/Rolle/Rolle/Ha.var".

alias id "Hb" = "cic:/CoRN/ftc/Rolle/Rolle/Hb.var".

(* end hide *)

(* begin show *)

alias id "Fab" = "cic:/CoRN/ftc/Rolle/Rolle/Fab.var".

(* end show *)

(* begin hide *)

alias id "e" = "cic:/CoRN/ftc/Rolle/Rolle/e.var".

alias id "He" = "cic:/CoRN/ftc/Rolle/Rolle/He.var".

inline "cic:/CoRN/ftc/Rolle/Rolle/contF'.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/derivF.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Rolle_lemma2.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/df.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Hdf.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Hf.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Rolle_lemma3.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/df'.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Hdf'.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Hf'.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/d.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Hd.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/incF.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/n.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/fcp.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Rolle_lemma1.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/incF'.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/fcp'.con" "Rolle__".

(* NOTATION
Notation cp := (compact_part a b Hab' d Hd).
*)

inline "cic:/CoRN/ftc/Rolle/Rolle/Rolle_lemma4.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Rolle_lemma5.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Rolle_lemma6.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Rolle_lemma7.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/j.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Hj.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Hj'.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/k.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Hk.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Hk'.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Rolle_lemma8.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Rolle_lemma9.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Rolle_lemma10.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Rolle_lemma11.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Rolle_lemma12.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Rolle_lemma13.con" "Rolle__".

inline "cic:/CoRN/ftc/Rolle/Rolle/Rolle_lemma15.con" "Rolle__".

(* end hide *)

inline "cic:/CoRN/ftc/Rolle/Rolle.con".

(* UNEXPORTED
End Rolle
*)

(* UNEXPORTED
Section Law_of_the_Mean
*)

(*#*
The following is a simple corollary:
*)

alias id "a" = "cic:/CoRN/ftc/Rolle/Law_of_the_Mean/a.var".

alias id "b" = "cic:/CoRN/ftc/Rolle/Law_of_the_Mean/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/Rolle/Law_of_the_Mean/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Rolle/Law_of_the_Mean/Hab.con" "Law_of_the_Mean__".

inline "cic:/CoRN/ftc/Rolle/Law_of_the_Mean/I.con" "Law_of_the_Mean__".

(* end hide *)

alias id "F" = "cic:/CoRN/ftc/Rolle/Law_of_the_Mean/F.var".

alias id "F'" = "cic:/CoRN/ftc/Rolle/Law_of_the_Mean/F'.var".

alias id "HF" = "cic:/CoRN/ftc/Rolle/Law_of_the_Mean/HF.var".

(* begin show *)

alias id "HA" = "cic:/CoRN/ftc/Rolle/Law_of_the_Mean/HA.var".

alias id "HB" = "cic:/CoRN/ftc/Rolle/Law_of_the_Mean/HB.var".

(* end show *)

inline "cic:/CoRN/ftc/Rolle/Law_of_the_Mean_I.con".

(* UNEXPORTED
End Law_of_the_Mean
*)

(* UNEXPORTED
Section Corollaries
*)

(*#*
We can also state these theorems without expliciting the derivative of [F].
*)

alias id "a" = "cic:/CoRN/ftc/Rolle/Corollaries/a.var".

alias id "b" = "cic:/CoRN/ftc/Rolle/Corollaries/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/Rolle/Corollaries/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Rolle/Corollaries/Hab.con" "Corollaries__".

(* end hide *)

alias id "F" = "cic:/CoRN/ftc/Rolle/Corollaries/F.var".

(* begin show *)

alias id "HF" = "cic:/CoRN/ftc/Rolle/Corollaries/HF.var".

(* end show *)

inline "cic:/CoRN/ftc/Rolle/Rolle'.con".

inline "cic:/CoRN/ftc/Rolle/Law_of_the_Mean'_I.con".

(* UNEXPORTED
End Corollaries
*)

(* UNEXPORTED
Section Generalizations
*)

(*#*
The mean law is more useful if we abstract [a] and [b] from the
context---allowing them in particular to be equal.  In the case where
[F(a) [=] F(b)] we get Rolle's theorem again, so there is no need to
state it also in this form.

%\begin{convention}% Assume [I] is a proper interval, [F,F':PartIR].
%\end{convention}%
*)

alias id "I" = "cic:/CoRN/ftc/Rolle/Generalizations/I.var".

alias id "pI" = "cic:/CoRN/ftc/Rolle/Generalizations/pI.var".

alias id "F" = "cic:/CoRN/ftc/Rolle/Generalizations/F.var".

alias id "F'" = "cic:/CoRN/ftc/Rolle/Generalizations/F'.var".

(* begin show *)

alias id "derF" = "cic:/CoRN/ftc/Rolle/Generalizations/derF.var".

(* end show *)

(* begin hide *)

inline "cic:/CoRN/ftc/Rolle/Generalizations/incF.con" "Generalizations__".

inline "cic:/CoRN/ftc/Rolle/Generalizations/incF'.con" "Generalizations__".

(* end hide *)

inline "cic:/CoRN/ftc/Rolle/Law_of_the_Mean.con".

(*#*
We further generalize the mean law by writing as an explicit bound.
*)

inline "cic:/CoRN/ftc/Rolle/Law_of_the_Mean_ineq.con".

(* UNEXPORTED
End Generalizations
*)

