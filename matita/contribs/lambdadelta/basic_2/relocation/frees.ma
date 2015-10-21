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

include "basic_2/notation/relations/freestar_3.ma".
include "basic_2/grammar/trace_sor.ma".
include "basic_2/grammar/lenv.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

inductive frees: relation3 lenv term trace ≝
| frees_atom: ∀I. frees (⋆) (⓪{I}) (◊)
| frees_sort: ∀L,k,cs. frees L (⋆k) cs →
              ∀I,T. frees (L.ⓑ{I}T) (⋆k) (Ⓕ @ cs)
| frees_zero: ∀L,T,cs. frees L T cs →
              ∀I. frees (L.ⓑ{I}T) (#0) (Ⓣ @ cs)
| frees_lref: ∀L,i,cs. frees L (#i) cs →
              ∀I,T. frees (L.ⓑ{I}T) (#(S i)) (Ⓕ @ cs)
| frees_gref: ∀L,p,cs. frees L (§p) cs →
              ∀I,T. frees (L.ⓑ{I}T) (§p) (Ⓕ @ cs)
| frees_bind: ∀cv,ct,cs. cv ⋓ ct ≡ cs →
              ∀L,V. frees L V cv → ∀I,T,b. frees (L.ⓑ{I}V) T (b @ ct) →
              ∀a. frees L (ⓑ{a,I}V.T) cs
| frees_flat: ∀cv,ct,cs. cv ⋓ ct ≡ cs →
              ∀L,V. frees L V cv → ∀T. frees L T ct →
              ∀I. frees L (ⓕ{I}V.T) cs
.

interpretation
   "context-sensitive free variables (term)"
   'FreeStar L T cs = (frees L T cs).
