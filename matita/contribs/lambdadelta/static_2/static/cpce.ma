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

include "static_2/notation/relations/pconveta_4.ma".
include "static_2/relocation/lifts.ma".
include "static_2/static/aaa.ma".

(* CONTEXT-SENSITIVE PARALLEL ETA-CONVERSION FOR TERMS **********************)

(* avtivate genv *)
inductive cpce: relation4 genv lenv term term ≝
| cpce_sort: ∀G,L,s. cpce G L (⋆s) (⋆s)
| cpce_abbr: ∀G,K,V. cpce G (K.ⓓV) (#0) (#0)
| cpce_abst: ∀G,K,W,B,A. ⦃G,K⦄ ⊢ W ⁝ ②B.A →
             cpce G (K.ⓛW) (#0) (+ⓛW.ⓐ#0.#1)
| cpce_lref: ∀I,G,K,T,U,i. cpce G K (#i) T →
             ⬆*[1] T ≘ U → cpce G (K.ⓘ{I}) (#↑i) U
| cpce_bind: ∀p,I,G,K,V1,V2,T1,T2.
             cpce G K V1 V2 → cpce G (K.ⓑ{I}V1) T1 T2 →
             cpce G K (ⓑ{p,I}V1.T1) (ⓑ{p,I}V2.T2)
| cpce_flat: ∀I,G,L,V1,V2,T1,T2.
             cpce G L V1 V2 → cpce G L T1 T2 →
             cpce G L (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
.

interpretation
   "context-sensitive parallel eta-conversion (term)"
   'PConvEta G L T1 T2 = (cpce G L T1 T2).
