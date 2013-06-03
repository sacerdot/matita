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

include "basic_2/grammar/lenv_append.ma".
include "basic_2/relocation/ldrop.ma".

(* CONTEXT-SENSITIVE UNFOLD FOR TERMS ***************************************)

inductive unfold: lenv → relation2 term lenv ≝
| unfold_sort: ∀L,k. unfold L (⋆k) L
| unfold_lref: ∀I,L1,L2,K1,K2,V,i. ⇩[0, i] L1 ≡ K1. ⓑ{I}V →
               unfold K1 V K2 → ⇩[|L2|, i] L2 ≡ K2 →
               unfold L1 (#i) (L1@@L2)
| unfold_bind: ∀a,I,L1,L2,V,T.
               unfold (L1.ⓑ{I}V) T L2 → unfold L1 (ⓑ{a,I}V.T) L2
| unfold_flat: ∀I,L1,L2,V,T.
               unfold L1 T L2 → unfold L1 (ⓕ{I}V.T) L2
.

interpretation "context-sensitive unfold (term)"
   'Unwind L1 T L2 = (unfold L1 T L2).
