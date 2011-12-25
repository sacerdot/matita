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

include "Basic_2/substitution/ldrop.ma".

(* ABSTRACT COMPUTATION PROPERTIES ******************************************)

definition CP1 ≝ λRR:lenv→relation term. λRS:relation term.
                 ∀L,k. NF … (RR L) RS (⋆k).

definition CP2 ≝ λRR:lenv→relation term. λRS:relation term.
                 ∀L,K,W,i. ⇓[0,i] L ≡ K. 𝕓{Abst} W → NF … (RR L) RS (#i).

definition CP3 ≝ λRR:lenv→relation term. λRP:lenv→predicate term.
                 ∀L,V,k. RP L (𝕔{Appl}⋆k.V) → RP L V.

(* requirements for abstract computation properties *)
record acp (RR:lenv->relation term) (RS:relation term) (RP:lenv→predicate term) : Prop ≝
{ cp1: CP1 RR RS;
  cp2: CP2 RR RS;
  cp3: CP3 RR RP
}.
