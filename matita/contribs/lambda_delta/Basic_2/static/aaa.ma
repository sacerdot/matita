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

include "Basic_2/grammar/aarity.ma".
include "Basic_2/substitution/ldrop.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

inductive aaa: lenv → term → predicate aarity ≝
| aaa_sort: ∀L,k. aaa L (⋆k) 𝕒
| aaa_lref: ∀I,L,K,V,B,i. ⇩[0, i] L ≡ K. 𝕓{I} V → aaa K V B → aaa L (#i) B
| aaa_abbr: ∀L,V,T,B,A.
            aaa L V B → aaa (L. 𝕓{Abbr} V) T A → aaa L (𝕔{Abbr} V. T) A
| aaa_abst: ∀L,V,T,B,A.
            aaa L V B → aaa (L. 𝕓{Abst} V) T A → aaa L (𝕔{Abst} V. T) (𝕔 B. A)
| aaa_appl: ∀L,V,T,B,A. aaa L V B → aaa L T (𝕔 B. A) → aaa L (𝕔{Appl} V. T) A
| aaa_cast: ∀L,V,T,A. aaa L V A → aaa L T A → aaa L (𝕔{Cast} V. T) A
.

interpretation
   "atomic arity assignment (term)"
   'AtomicArity L T A = (aaa L T A).
