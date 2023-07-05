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

include "ground/relocation/fu/fur_uni_nexts.ma".
include "ground/relocation/fu/fur_after_dapp.ma".

(* UNIFORM ELEMENTS FOR FINITE RELOCATION MAPS FOR UNWIND *******************)

(* Constructions with fur_after *********************************************)

lemma fur_after_uni_dx (f) (n):
      (⮤*[n]f) ≐ f•𝐮❨n❩.
// qed.

lemma fur_after_uni_sn (f) (n):
      ↑*[n]f ≐ 𝐮❨n❩•f.
// qed.

lemma fur_after_uni_bi (m) (n):
      (𝐮❨n+m❩) ≐ 𝐮❨m❩•𝐮❨n❩.
// qed.
