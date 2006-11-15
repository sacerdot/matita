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

(* $Id: Composition.v,v 1.4 2004/04/23 10:00:58 lcf Exp $ *)

(* INCLUDE
MoreFunctions
*)

(* UNEXPORTED
Section Maps_into_Compacts.
*)

(* UNEXPORTED
Section Part_Funct.
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

inline cic:/CoRN/ftc/Composition/F.var.

inline cic:/CoRN/ftc/Composition/G.var.

inline cic:/CoRN/ftc/Composition/a.var.

inline cic:/CoRN/ftc/Composition/b.var.

inline cic:/CoRN/ftc/Composition/Hab.var.

inline cic:/CoRN/ftc/Composition/c.var.

inline cic:/CoRN/ftc/Composition/d.var.

inline cic:/CoRN/ftc/Composition/Hcd.var.

(* begin hide *)

inline cic:/CoRN/ftc/Composition/I.con.

(* end hide *)

(* begin show *)

inline cic:/CoRN/ftc/Composition/Hf.var.

(* end show *)

inline cic:/CoRN/ftc/Composition/maps_into_compacts.con.

(* begin show *)

inline cic:/CoRN/ftc/Composition/maps.var.

(* end show *)

inline cic:/CoRN/ftc/Composition/maps_lemma'.con.

inline cic:/CoRN/ftc/Composition/maps_lemma.con.

inline cic:/CoRN/ftc/Composition/maps_lemma_less.con.

inline cic:/CoRN/ftc/Composition/maps_lemma_inc.con.

(* UNEXPORTED
End Part_Funct.
*)

(* UNEXPORTED
End Maps_into_Compacts.
*)

(* UNEXPORTED
Section Mapping.
*)

(*#*
As was the case for division of partial functions, this condition
completely characterizes the domain of the composite function.
*)

inline cic:/CoRN/ftc/Composition/F.var.

inline cic:/CoRN/ftc/Composition/G.var.

inline cic:/CoRN/ftc/Composition/a.var.

inline cic:/CoRN/ftc/Composition/b.var.

inline cic:/CoRN/ftc/Composition/Hab.var.

inline cic:/CoRN/ftc/Composition/c.var.

inline cic:/CoRN/ftc/Composition/d.var.

inline cic:/CoRN/ftc/Composition/Hcd.var.

(* begin show *)

inline cic:/CoRN/ftc/Composition/Hf.var.

inline cic:/CoRN/ftc/Composition/Hg.var.

inline cic:/CoRN/ftc/Composition/maps.var.

(* end show *)

inline cic:/CoRN/ftc/Composition/included_comp.con.

(* UNEXPORTED
End Mapping.
*)

(* UNEXPORTED
Section Interval_Continuity.
*)

(*#* **Continuity

We now prove that the composition of two continuous partial functions is continuous.
*)

inline cic:/CoRN/ftc/Composition/a.var.

inline cic:/CoRN/ftc/Composition/b.var.

inline cic:/CoRN/ftc/Composition/Hab.var.

(* begin hide *)

inline cic:/CoRN/ftc/Composition/I.con.

(* end hide *)

inline cic:/CoRN/ftc/Composition/c.var.

inline cic:/CoRN/ftc/Composition/d.var.

inline cic:/CoRN/ftc/Composition/Hcd.var.

inline cic:/CoRN/ftc/Composition/F.var.

inline cic:/CoRN/ftc/Composition/G.var.

(* begin show *)

inline cic:/CoRN/ftc/Composition/contF.var.

inline cic:/CoRN/ftc/Composition/contG.var.

inline cic:/CoRN/ftc/Composition/Hmap.var.

(* end show *)

inline cic:/CoRN/ftc/Composition/Continuous_I_comp.con.

(* UNEXPORTED
End Interval_Continuity.
*)

(* UNEXPORTED
Section Derivative.
*)

(*#* **Derivative

We now work with the derivative relation and prove the chain rule for partial functions.
*)

inline cic:/CoRN/ftc/Composition/F.var.

inline cic:/CoRN/ftc/Composition/F'.var.

inline cic:/CoRN/ftc/Composition/G.var.

inline cic:/CoRN/ftc/Composition/G'.var.

inline cic:/CoRN/ftc/Composition/a.var.

inline cic:/CoRN/ftc/Composition/b.var.

inline cic:/CoRN/ftc/Composition/Hab'.var.

inline cic:/CoRN/ftc/Composition/c.var.

inline cic:/CoRN/ftc/Composition/d.var.

inline cic:/CoRN/ftc/Composition/Hcd'.var.

(* begin hide *)

inline cic:/CoRN/ftc/Composition/Hab.con.

inline cic:/CoRN/ftc/Composition/Hcd.con.

inline cic:/CoRN/ftc/Composition/I.con.

(* end hide *)

(* begin show *)

inline cic:/CoRN/ftc/Composition/derF.var.

inline cic:/CoRN/ftc/Composition/derG.var.

inline cic:/CoRN/ftc/Composition/Hmap.var.

(* end show *)

inline cic:/CoRN/ftc/Composition/included_comp'.con.

inline cic:/CoRN/ftc/Composition/maps'.con.

inline cic:/CoRN/ftc/Composition/Derivative_I_comp.con.

(*#*
The next lemma will be useful when we move on to differentiability.
*)

inline cic:/CoRN/ftc/Composition/Diffble_I_comp_aux.con.

(* UNEXPORTED
End Derivative.
*)

(* UNEXPORTED
Section Differentiability.
*)

(*#* **Differentiability

Finally, we move on to differentiability.
*)

inline cic:/CoRN/ftc/Composition/F.var.

inline cic:/CoRN/ftc/Composition/G.var.

inline cic:/CoRN/ftc/Composition/a.var.

inline cic:/CoRN/ftc/Composition/b.var.

inline cic:/CoRN/ftc/Composition/Hab'.var.

inline cic:/CoRN/ftc/Composition/c.var.

inline cic:/CoRN/ftc/Composition/d.var.

inline cic:/CoRN/ftc/Composition/Hcd'.var.

(* begin hide *)

inline cic:/CoRN/ftc/Composition/Hab.con.

inline cic:/CoRN/ftc/Composition/Hcd.con.

inline cic:/CoRN/ftc/Composition/I.con.

(* end hide *)

(* begin show *)

inline cic:/CoRN/ftc/Composition/diffF.var.

inline cic:/CoRN/ftc/Composition/diffG.var.

inline cic:/CoRN/ftc/Composition/Hmap.var.

(* end show *)

inline cic:/CoRN/ftc/Composition/Diffble_I_comp.con.

(* UNEXPORTED
End Differentiability.
*)

(* UNEXPORTED
Section Generalized_Intervals.
*)

(*#* **Generalizations

We now generalize this results to arbitrary intervals.  We begin by generalizing the notion of mapping compacts into compacts.

%\begin{convention}% We assume [I,J] to be proper intervals.
%\end{convention}%
*)

inline cic:/CoRN/ftc/Composition/I.var.

inline cic:/CoRN/ftc/Composition/J.var.

inline cic:/CoRN/ftc/Composition/pI.var.

inline cic:/CoRN/ftc/Composition/pJ.var.

inline cic:/CoRN/ftc/Composition/maps_compacts_into.con.

(*#*
Now everything comes naturally:
*)

inline cic:/CoRN/ftc/Composition/comp_inc_lemma.con.

inline cic:/CoRN/ftc/Composition/F.var.

inline cic:/CoRN/ftc/Composition/F'.var.

inline cic:/CoRN/ftc/Composition/G.var.

inline cic:/CoRN/ftc/Composition/G'.var.

(* begin show *)

inline cic:/CoRN/ftc/Composition/Hmap.var.

(* end show *)

inline cic:/CoRN/ftc/Composition/Continuous_comp.con.

(* begin show *)

inline cic:/CoRN/ftc/Composition/Hmap'.var.

(* end show *)

inline cic:/CoRN/ftc/Composition/Derivative_comp.con.

(* UNEXPORTED
End Generalized_Intervals.
*)

(* UNEXPORTED
Section Corollaries.
*)

(*#*
Finally, some criteria to prove that a function with a specific domain maps compacts into compacts:
*)

inline cic:/CoRN/ftc/Composition/positive_fun.con.

inline cic:/CoRN/ftc/Composition/negative_fun.con.

inline cic:/CoRN/ftc/Composition/positive_imp_maps_compacts_into.con.

inline cic:/CoRN/ftc/Composition/negative_imp_maps_compacts_into.con.

inline cic:/CoRN/ftc/Composition/Continuous_imp_maps_compacts_into.con.

(*#*
As a corollary, we get the generalization of differentiability property.
*)

inline cic:/CoRN/ftc/Composition/Diffble_comp.con.

(* UNEXPORTED
End Corollaries.
*)

(* UNEXPORTED
Hint Immediate included_comp: included.
*)

(* UNEXPORTED
Hint Immediate Continuous_I_comp Continuous_comp: continuous.
*)

