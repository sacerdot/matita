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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/PartInterval".

(* $Id: PartInterval.v,v 1.6 2004/04/23 10:01:00 lcf Exp $ *)

(* INCLUDE
IntervalFunct
*)

(* UNEXPORTED
Section Conversion.
*)

(*#* *Correspondence

In this file we prove that there are mappings going in both ways
between the set of partial functions whose domain contains
[[a,b]] and the set of real-valued functions with domain on
that interval.  These mappings form an adjunction, and thus they have
all the good properties for preservation results.

**Mappings

We begin by defining the map from partial functions to setoid
functions as simply being the restriction of the partial function to
the interval [[a,b]].

%\begin{convention}% Let [F] be a partial function and [a,b:IR] such
that [I [=] [a,b]] is included in the domain of [F].
%\end{convention}%
*)

inline cic:/CoRN/ftc/PartInterval/F.var.

inline cic:/CoRN/ftc/PartInterval/a.var.

inline cic:/CoRN/ftc/PartInterval/b.var.

inline cic:/CoRN/ftc/PartInterval/Hab.var.

(* begin hide *)

inline cic:/CoRN/ftc/PartInterval/I.con.

(* end hide *)

inline cic:/CoRN/ftc/PartInterval/Hf.var.

inline cic:/CoRN/ftc/PartInterval/IntPartIR_strext.con.

inline cic:/CoRN/ftc/PartInterval/IntPartIR.con.

(* UNEXPORTED
End Conversion.
*)

(* UNEXPORTED
Implicit Arguments IntPartIR [F a b Hab].
*)

(* UNEXPORTED
Section AntiConversion.
*)

(*#*
To go the other way around, we simply take a setoid function [f] with
domain [[a,b]] and build the corresponding partial function.
*)

inline cic:/CoRN/ftc/PartInterval/a.var.

inline cic:/CoRN/ftc/PartInterval/b.var.

inline cic:/CoRN/ftc/PartInterval/Hab.var.

(* begin hide *)

inline cic:/CoRN/ftc/PartInterval/I.con.

(* end hide *)

inline cic:/CoRN/ftc/PartInterval/f.var.

inline cic:/CoRN/ftc/PartInterval/PartInt_strext.con.

inline cic:/CoRN/ftc/PartInterval/PartInt.con.

(* UNEXPORTED
End AntiConversion.
*)

(* UNEXPORTED
Implicit Arguments PartInt [a b Hab].
*)

(* UNEXPORTED
Section Inverses.
*)

(*#*
In one direction these operators are inverses.
*)

inline cic:/CoRN/ftc/PartInterval/int_part_int.con.

(* UNEXPORTED
End Inverses.
*)

(* UNEXPORTED
Section Equivalences.
*)

(*#* **Mappings Preserve Operations

We now prove that all the operations we have defined on both sets are
preserved by [PartInt].

%\begin{convention}% Let [F,G] be partial functions and [a,b:IR] and
denote by [I] the interval [[a,b]].  Let [f,g] be setoid functions of
type [I->IR] equal respectively to [F] and [G] in [I].
%\end{convention}%
*)

inline cic:/CoRN/ftc/PartInterval/F.var.

inline cic:/CoRN/ftc/PartInterval/G.var.

inline cic:/CoRN/ftc/PartInterval/a.var.

inline cic:/CoRN/ftc/PartInterval/b.var.

inline cic:/CoRN/ftc/PartInterval/c.var.

inline cic:/CoRN/ftc/PartInterval/Hab.var.

(* begin hide *)

inline cic:/CoRN/ftc/PartInterval/I.con.

(* end hide *)

inline cic:/CoRN/ftc/PartInterval/f.var.

inline cic:/CoRN/ftc/PartInterval/g.var.

inline cic:/CoRN/ftc/PartInterval/Ff.var.

inline cic:/CoRN/ftc/PartInterval/Gg.var.

inline cic:/CoRN/ftc/PartInterval/part_int_const.con.

inline cic:/CoRN/ftc/PartInterval/part_int_id.con.

inline cic:/CoRN/ftc/PartInterval/part_int_plus.con.

inline cic:/CoRN/ftc/PartInterval/part_int_inv.con.

inline cic:/CoRN/ftc/PartInterval/part_int_minus.con.

inline cic:/CoRN/ftc/PartInterval/part_int_mult.con.

inline cic:/CoRN/ftc/PartInterval/part_int_nth.con.

(* begin show *)

inline cic:/CoRN/ftc/PartInterval/HG.var.

inline cic:/CoRN/ftc/PartInterval/Hg.var.

(* end show *)

inline cic:/CoRN/ftc/PartInterval/part_int_recip.con.

inline cic:/CoRN/ftc/PartInterval/part_int_div.con.

(* UNEXPORTED
End Equivalences.
*)

