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

set "baseuri" "cic:/matita/CoRN-Decl/ftc/Composition".

include "CoRN.ma".

(* $Id: Composition.v,v 1.4 2004/04/23 10:00:58 lcf Exp $ *)

include "ftc/MoreFunctions.ma".

(* UNEXPORTED
Section Maps_into_Compacts
*)

(* UNEXPORTED
Section Part_Funct
*)

(*#* *Composition

Preservation results for functional composition are treated in this
separate file.  We start by defining some auxiliary predicates, and
then prove the preservation of continuity through composition and the
chain rule for differentiation, both for compact and arbitrary
intervals.

%\begin{convention}% Throughout this section:
- [a, b : IR] and [I] will denote [[a,b]];
- [c, d : IR] and [J] will denote [[c,d]];
- [F, F', G, G'] will be partial functions.

%\end{convention}%

** Maps into Compacts

Both continuity and differentiability proofs require extra hypothesis
on the functions involved---namely, that every compact interval is
mapped into another compact interval.  We define this concept for
partial functions, and prove some trivial results.
*)

alias id "F" = "cic:/CoRN/ftc/Composition/Maps_into_Compacts/Part_Funct/F.var".

alias id "G" = "cic:/CoRN/ftc/Composition/Maps_into_Compacts/Part_Funct/G.var".

alias id "a" = "cic:/CoRN/ftc/Composition/Maps_into_Compacts/Part_Funct/a.var".

alias id "b" = "cic:/CoRN/ftc/Composition/Maps_into_Compacts/Part_Funct/b.var".

alias id "Hab" = "cic:/CoRN/ftc/Composition/Maps_into_Compacts/Part_Funct/Hab.var".

alias id "c" = "cic:/CoRN/ftc/Composition/Maps_into_Compacts/Part_Funct/c.var".

alias id "d" = "cic:/CoRN/ftc/Composition/Maps_into_Compacts/Part_Funct/d.var".

alias id "Hcd" = "cic:/CoRN/ftc/Composition/Maps_into_Compacts/Part_Funct/Hcd.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Composition/Maps_into_Compacts/Part_Funct/I.con" "Maps_into_Compacts__Part_Funct__".

(* end hide *)

(* begin show *)

alias id "Hf" = "cic:/CoRN/ftc/Composition/Maps_into_Compacts/Part_Funct/Hf.var".

(* end show *)

inline "cic:/CoRN/ftc/Composition/maps_into_compacts.con".

(* begin show *)

alias id "maps" = "cic:/CoRN/ftc/Composition/Maps_into_Compacts/Part_Funct/maps.var".

(* end show *)

inline "cic:/CoRN/ftc/Composition/maps_lemma'.con".

inline "cic:/CoRN/ftc/Composition/maps_lemma.con".

inline "cic:/CoRN/ftc/Composition/maps_lemma_less.con".

inline "cic:/CoRN/ftc/Composition/maps_lemma_inc.con".

(* UNEXPORTED
End Part_Funct
*)

(* UNEXPORTED
End Maps_into_Compacts
*)

(* UNEXPORTED
Section Mapping
*)

(*#*
As was the case for division of partial functions, this condition
completely characterizes the domain of the composite function.
*)

alias id "F" = "cic:/CoRN/ftc/Composition/Mapping/F.var".

alias id "G" = "cic:/CoRN/ftc/Composition/Mapping/G.var".

alias id "a" = "cic:/CoRN/ftc/Composition/Mapping/a.var".

alias id "b" = "cic:/CoRN/ftc/Composition/Mapping/b.var".

alias id "Hab" = "cic:/CoRN/ftc/Composition/Mapping/Hab.var".

alias id "c" = "cic:/CoRN/ftc/Composition/Mapping/c.var".

alias id "d" = "cic:/CoRN/ftc/Composition/Mapping/d.var".

alias id "Hcd" = "cic:/CoRN/ftc/Composition/Mapping/Hcd.var".

(* begin show *)

alias id "Hf" = "cic:/CoRN/ftc/Composition/Mapping/Hf.var".

alias id "Hg" = "cic:/CoRN/ftc/Composition/Mapping/Hg.var".

alias id "maps" = "cic:/CoRN/ftc/Composition/Mapping/maps.var".

(* end show *)

inline "cic:/CoRN/ftc/Composition/included_comp.con".

(* UNEXPORTED
End Mapping
*)

(* UNEXPORTED
Section Interval_Continuity
*)

(*#* **Continuity

We now prove that the composition of two continuous partial functions is continuous.
*)

alias id "a" = "cic:/CoRN/ftc/Composition/Interval_Continuity/a.var".

alias id "b" = "cic:/CoRN/ftc/Composition/Interval_Continuity/b.var".

alias id "Hab" = "cic:/CoRN/ftc/Composition/Interval_Continuity/Hab.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Composition/Interval_Continuity/I.con" "Interval_Continuity__".

(* end hide *)

alias id "c" = "cic:/CoRN/ftc/Composition/Interval_Continuity/c.var".

alias id "d" = "cic:/CoRN/ftc/Composition/Interval_Continuity/d.var".

alias id "Hcd" = "cic:/CoRN/ftc/Composition/Interval_Continuity/Hcd.var".

alias id "F" = "cic:/CoRN/ftc/Composition/Interval_Continuity/F.var".

alias id "G" = "cic:/CoRN/ftc/Composition/Interval_Continuity/G.var".

(* begin show *)

alias id "contF" = "cic:/CoRN/ftc/Composition/Interval_Continuity/contF.var".

alias id "contG" = "cic:/CoRN/ftc/Composition/Interval_Continuity/contG.var".

alias id "Hmap" = "cic:/CoRN/ftc/Composition/Interval_Continuity/Hmap.var".

(* end show *)

inline "cic:/CoRN/ftc/Composition/Continuous_I_comp.con".

(* UNEXPORTED
End Interval_Continuity
*)

(* UNEXPORTED
Section Derivative
*)

(*#* **Derivative

We now work with the derivative relation and prove the chain rule for partial functions.
*)

alias id "F" = "cic:/CoRN/ftc/Composition/Derivative/F.var".

alias id "F'" = "cic:/CoRN/ftc/Composition/Derivative/F'.var".

alias id "G" = "cic:/CoRN/ftc/Composition/Derivative/G.var".

alias id "G'" = "cic:/CoRN/ftc/Composition/Derivative/G'.var".

alias id "a" = "cic:/CoRN/ftc/Composition/Derivative/a.var".

alias id "b" = "cic:/CoRN/ftc/Composition/Derivative/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/Composition/Derivative/Hab'.var".

alias id "c" = "cic:/CoRN/ftc/Composition/Derivative/c.var".

alias id "d" = "cic:/CoRN/ftc/Composition/Derivative/d.var".

alias id "Hcd'" = "cic:/CoRN/ftc/Composition/Derivative/Hcd'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Composition/Derivative/Hab.con" "Derivative__".

inline "cic:/CoRN/ftc/Composition/Derivative/Hcd.con" "Derivative__".

inline "cic:/CoRN/ftc/Composition/Derivative/I.con" "Derivative__".

(* end hide *)

(* begin show *)

alias id "derF" = "cic:/CoRN/ftc/Composition/Derivative/derF.var".

alias id "derG" = "cic:/CoRN/ftc/Composition/Derivative/derG.var".

alias id "Hmap" = "cic:/CoRN/ftc/Composition/Derivative/Hmap.var".

(* end show *)

inline "cic:/CoRN/ftc/Composition/included_comp'.con".

inline "cic:/CoRN/ftc/Composition/maps'.con".

inline "cic:/CoRN/ftc/Composition/Derivative_I_comp.con".

(*#*
The next lemma will be useful when we move on to differentiability.
*)

inline "cic:/CoRN/ftc/Composition/Diffble_I_comp_aux.con".

(* UNEXPORTED
End Derivative
*)

(* UNEXPORTED
Section Differentiability
*)

(*#* **Differentiability

Finally, we move on to differentiability.
*)

alias id "F" = "cic:/CoRN/ftc/Composition/Differentiability/F.var".

alias id "G" = "cic:/CoRN/ftc/Composition/Differentiability/G.var".

alias id "a" = "cic:/CoRN/ftc/Composition/Differentiability/a.var".

alias id "b" = "cic:/CoRN/ftc/Composition/Differentiability/b.var".

alias id "Hab'" = "cic:/CoRN/ftc/Composition/Differentiability/Hab'.var".

alias id "c" = "cic:/CoRN/ftc/Composition/Differentiability/c.var".

alias id "d" = "cic:/CoRN/ftc/Composition/Differentiability/d.var".

alias id "Hcd'" = "cic:/CoRN/ftc/Composition/Differentiability/Hcd'.var".

(* begin hide *)

inline "cic:/CoRN/ftc/Composition/Differentiability/Hab.con" "Differentiability__".

inline "cic:/CoRN/ftc/Composition/Differentiability/Hcd.con" "Differentiability__".

inline "cic:/CoRN/ftc/Composition/Differentiability/I.con" "Differentiability__".

(* end hide *)

(* begin show *)

alias id "diffF" = "cic:/CoRN/ftc/Composition/Differentiability/diffF.var".

alias id "diffG" = "cic:/CoRN/ftc/Composition/Differentiability/diffG.var".

alias id "Hmap" = "cic:/CoRN/ftc/Composition/Differentiability/Hmap.var".

(* end show *)

inline "cic:/CoRN/ftc/Composition/Diffble_I_comp.con".

(* UNEXPORTED
End Differentiability
*)

(* UNEXPORTED
Section Generalized_Intervals
*)

(*#* **Generalizations

We now generalize this results to arbitrary intervals.  We begin by generalizing the notion of mapping compacts into compacts.

%\begin{convention}% We assume [I,J] to be proper intervals.
%\end{convention}%
*)

alias id "I" = "cic:/CoRN/ftc/Composition/Generalized_Intervals/I.var".

alias id "J" = "cic:/CoRN/ftc/Composition/Generalized_Intervals/J.var".

alias id "pI" = "cic:/CoRN/ftc/Composition/Generalized_Intervals/pI.var".

alias id "pJ" = "cic:/CoRN/ftc/Composition/Generalized_Intervals/pJ.var".

inline "cic:/CoRN/ftc/Composition/maps_compacts_into.con".

(*#*
Now everything comes naturally:
*)

inline "cic:/CoRN/ftc/Composition/comp_inc_lemma.con".

alias id "F" = "cic:/CoRN/ftc/Composition/Generalized_Intervals/F.var".

alias id "F'" = "cic:/CoRN/ftc/Composition/Generalized_Intervals/F'.var".

alias id "G" = "cic:/CoRN/ftc/Composition/Generalized_Intervals/G.var".

alias id "G'" = "cic:/CoRN/ftc/Composition/Generalized_Intervals/G'.var".

(* begin show *)

alias id "Hmap" = "cic:/CoRN/ftc/Composition/Generalized_Intervals/Hmap.var".

(* end show *)

inline "cic:/CoRN/ftc/Composition/Continuous_comp.con".

(* begin show *)

alias id "Hmap'" = "cic:/CoRN/ftc/Composition/Generalized_Intervals/Hmap'.var".

(* end show *)

inline "cic:/CoRN/ftc/Composition/Derivative_comp.con".

(* UNEXPORTED
End Generalized_Intervals
*)

(* UNEXPORTED
Section Corollaries
*)

(*#*
Finally, some criteria to prove that a function with a specific domain maps compacts into compacts:
*)

inline "cic:/CoRN/ftc/Composition/positive_fun.con".

inline "cic:/CoRN/ftc/Composition/negative_fun.con".

inline "cic:/CoRN/ftc/Composition/positive_imp_maps_compacts_into.con".

inline "cic:/CoRN/ftc/Composition/negative_imp_maps_compacts_into.con".

inline "cic:/CoRN/ftc/Composition/Continuous_imp_maps_compacts_into.con".

(*#*
As a corollary, we get the generalization of differentiability property.
*)

inline "cic:/CoRN/ftc/Composition/Diffble_comp.con".

(* UNEXPORTED
End Corollaries
*)

(* UNEXPORTED
Hint Immediate included_comp: included.
*)

(* UNEXPORTED
Hint Immediate Continuous_I_comp Continuous_comp: continuous.
*)

