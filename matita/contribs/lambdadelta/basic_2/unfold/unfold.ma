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

include "basic_2/notation/relations/unfold_4.ma".
include "basic_2/grammar/lenv_append.ma".
include "basic_2/grammar/genv.ma".
include "basic_2/substitution/drop.ma".

(* CONTEXT-SENSITIVE UNFOLD FOR TERMS ***************************************)

(* activate genv *)
inductive unfold: relation4 genv lenv term lenv ≝
| unfold_sort: ∀G,L,k. unfold G L (⋆k) L
| unfold_lref: ∀I,G,L1,L2,K1,K2,V,i. ⇩[i] L1 ≡ K1. ⓑ{I}V →
               unfold G K1 V K2 → ⇩[Ⓣ, |L2|, i] L2 ≡ K2 →
               unfold G L1 (#i) (L1@@L2)
| unfold_bind: ∀a,I,G,L1,L2,V,T.
               unfold G (L1.ⓑ{I}V) T L2 → unfold G L1 (ⓑ{a,I}V.T) L2
| unfold_flat: ∀I,G,L1,L2,V,T.
               unfold G L1 T L2 → unfold G L1 (ⓕ{I}V.T) L2
.

interpretation "context-sensitive unfold (term)"
   'Unfold G L1 T L2 = (unfold G L1 T L2).
