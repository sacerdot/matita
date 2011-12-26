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

include "Basic_2/computation/acp_cr.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR ABSTRACT CANDIDATES OF REDUCIBILITY *****)

inductive lsubc (RP:lenv→predicate term): relation lenv ≝
| lsubc_atom: lsubc RP (⋆) (⋆)
| lsubc_pair: ∀I,L1,L2,V. lsubc RP L1 L2 → lsubc RP (L1. 𝕓{I} V) (L2. 𝕓{I} V)
| lsubc_abbr: ∀L1,L2,V,W,A. ⦃L1, V⦄ [RP] ϵ 〚A〛 → ⦃L2, W⦄ [RP] ϵ 〚A〛 →
              lsubc RP L1 L2 → lsubc RP (L1. 𝕓{Abbr} V) (L2. 𝕓{Abst} W)
.

interpretation
  "local environment refinement (abstract candidates of reducibility)"
  'CrSubEq L1 RP L2 = (lsubc RP L1 L2).

(* Basic properties *********************************************************)

lemma lsubc_refl: ∀RP,L. L [RP] ⊑ L.
#RP #L elim L -L // /2 width=1/
qed.

(* Basic inversion lemmas ***************************************************)
