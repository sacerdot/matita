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
include "ground/relocation/fu/fur_tails_nexts.ma".
include "ground/relocation/fu/fur_drops_nexts.ma".
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

(* Main constructions with fur_tails and fur_drops and fur_after ************)

theorem fur_after_uni_dx_xapp (f) (n):
        (𝐮❨f＠❨n❩❩)•⫰*[n]f ≐ f•𝐮❨n❩.
#f #n
@fur_eq_repl
[3: @fur_eq_sym @fur_nexts_xapp_tails
|4: @fur_after_uni_sn |1: skip
|5: @fur_after_uni_dx |2: skip
]
qed.

theorem fur_after_uni_dx_lapp (f) (n):
        (𝐮❨f＠§❨n❩❩)•⇩*[n]f ≐ f•𝐮❨n❩.
#f #n
@fur_eq_repl
[3: @fur_eq_sym @fur_nexts_lapp_drops
|4: @fur_after_uni_sn |1: skip
|5: @fur_after_uni_dx |2: skip
]
qed.
