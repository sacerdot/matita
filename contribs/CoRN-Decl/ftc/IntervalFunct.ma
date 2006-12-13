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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/IntervalFunct".

include "CoRN.ma".

(* $Id: IntervalFunct.v,v 1.5 2004/04/08 15:28:06 lcf Exp $ *)

include "ftc/PartFunEquality.ma".

(* UNEXPORTED
Section Operations
*)

(*#* * Functions with compact domain

In this section we concern ourselves with defining operations on the
set of functions from an arbitrary interval [[a,b]] to [IR].
Although these are a particular kind of partial function, they have
the advantage that, given [a] and [b], they have type [Set] and can
thus be quantified over and extracted from existential hypothesis.
This will be important when we want to define concepts like
differentiability, which involve the existence of an object satisfying
some given properties.

Throughout this section we will focus on a compact interval and define
operators analogous to those we already have for arbitrary partial
functions.

%\begin{convention}% Let [a,b] be real numbers and denote by [I] the
compact interval [[a,b]].  Let [f, g] be setoid functions of
type [I -> IR].
%\end{convention}%
*)

alias id "a" = "cic:/CoRN/ftc/IntervalFunct/Operations/a.var".

alias id "b" = "cic:/CoRN/ftc/IntervalFunct/Operations/b.var".

alias id "Hab" = "cic:/CoRN/ftc/IntervalFunct/Operations/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/IntervalFunct/Operations/I.con" "Operations__".

(* end hide *)

alias id "f" = "cic:/CoRN/ftc/IntervalFunct/Operations/f.var".

alias id "g" = "cic:/CoRN/ftc/IntervalFunct/Operations/g.var".

(* UNEXPORTED
Section Const
*)

(*#*
Constant and identity functions are defined.

%\begin{convention}% Let [c:IR].
%\end{convention}%
*)

alias id "c" = "cic:/CoRN/ftc/IntervalFunct/Operations/Const/c.var".

inline "cic:/CoRN/ftc/IntervalFunct/IConst_strext.con".

inline "cic:/CoRN/ftc/IntervalFunct/IConst.con".

(* UNEXPORTED
End Const
*)

inline "cic:/CoRN/ftc/IntervalFunct/IId_strext.con".

inline "cic:/CoRN/ftc/IntervalFunct/IId.con".

(*#*
Next, we define addition, algebraic inverse, subtraction and product of functions.
*)

inline "cic:/CoRN/ftc/IntervalFunct/IPlus_strext.con".

inline "cic:/CoRN/ftc/IntervalFunct/IPlus.con".

inline "cic:/CoRN/ftc/IntervalFunct/IInv_strext.con".

inline "cic:/CoRN/ftc/IntervalFunct/IInv.con".

inline "cic:/CoRN/ftc/IntervalFunct/IMinus_strext.con".

inline "cic:/CoRN/ftc/IntervalFunct/IMinus.con".

inline "cic:/CoRN/ftc/IntervalFunct/IMult_strext.con".

inline "cic:/CoRN/ftc/IntervalFunct/IMult.con".

(* UNEXPORTED
Section Nth_Power
*)

(*#*
Exponentiation to a natural power [n] is also useful.
*)

alias id "n" = "cic:/CoRN/ftc/IntervalFunct/Operations/Nth_Power/n.var".

inline "cic:/CoRN/ftc/IntervalFunct/INth_strext.con".

inline "cic:/CoRN/ftc/IntervalFunct/INth.con".

(* UNEXPORTED
End Nth_Power
*)

(*#*
If a function is non-zero in all the interval then we can define its multiplicative inverse.
*)

(* UNEXPORTED
Section Recip_Div
*)

(* begin show *)

alias id "Hg" = "cic:/CoRN/ftc/IntervalFunct/Operations/Recip_Div/Hg.var".

(* end show *)

inline "cic:/CoRN/ftc/IntervalFunct/IRecip_strext.con".

inline "cic:/CoRN/ftc/IntervalFunct/IRecip.con".

inline "cic:/CoRN/ftc/IntervalFunct/IDiv_strext.con".

inline "cic:/CoRN/ftc/IntervalFunct/IDiv.con".

(* UNEXPORTED
End Recip_Div
*)

(*#*
Absolute value will also be needed at some point.
*)

inline "cic:/CoRN/ftc/IntervalFunct/IAbs_strext.con".

inline "cic:/CoRN/ftc/IntervalFunct/IAbs.con".

(* UNEXPORTED
End Operations
*)

(*#* 
The set of these functions form a ring with relation to the operations
of sum and multiplication.  As they actually form a set, this fact can
be proved in Coq for this class of functions; unfortunately, due to a
problem with the coercions, we are not able to use it (Coq will not
recognize the elements of that ring as functions which can be applied
to elements of [[a,b]]), so we merely state this fact here as a
curiosity.

Finally, we define composition; for this we need two functions with
different domains.

%\begin{convention}% [a',b'] be real numbers and denote by [I'] the
compact interval [[a',b']], and let [g] be a setoid function of type
[I' -> IR].
%\end{convention}%
*)

(* UNEXPORTED
Section Composition
*)

alias id "a" = "cic:/CoRN/ftc/IntervalFunct/Composition/a.var".

alias id "b" = "cic:/CoRN/ftc/IntervalFunct/Composition/b.var".

alias id "Hab" = "cic:/CoRN/ftc/IntervalFunct/Composition/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/IntervalFunct/Composition/I.con" "Composition__".

(* end hide *)

alias id "a'" = "cic:/CoRN/ftc/IntervalFunct/Composition/a'.var".

alias id "b'" = "cic:/CoRN/ftc/IntervalFunct/Composition/b'.var".

alias id "Hab'" = "cic:/CoRN/ftc/IntervalFunct/Composition/Hab'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/IntervalFunct/Composition/I'.con" "Composition__".

(* end hide *)

alias id "f" = "cic:/CoRN/ftc/IntervalFunct/Composition/f.var".

alias id "g" = "cic:/CoRN/ftc/IntervalFunct/Composition/g.var".

alias id "Hfg" = "cic:/CoRN/ftc/IntervalFunct/Composition/Hfg.var".

inline "cic:/CoRN/ftc/IntervalFunct/IComp_strext.con".

inline "cic:/CoRN/ftc/IntervalFunct/IComp.con".

(* UNEXPORTED
End Composition
*)

(* UNEXPORTED
Implicit Arguments IConst [a b Hab].
*)

(* UNEXPORTED
Implicit Arguments IId [a b Hab].
*)

(* UNEXPORTED
Implicit Arguments IPlus [a b Hab].
*)

(* UNEXPORTED
Implicit Arguments IInv [a b Hab].
*)

(* UNEXPORTED
Implicit Arguments IMinus [a b Hab].
*)

(* UNEXPORTED
Implicit Arguments IMult [a b Hab].
*)

(* UNEXPORTED
Implicit Arguments INth [a b Hab].
*)

(* UNEXPORTED
Implicit Arguments IRecip [a b Hab].
*)

(* UNEXPORTED
Implicit Arguments IDiv [a b Hab].
*)

(* UNEXPORTED
Implicit Arguments IAbs [a b Hab].
*)

(* UNEXPORTED
Implicit Arguments IComp [a b Hab a' b' Hab'].
*)

