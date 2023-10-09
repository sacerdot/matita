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

include "ground/notation/functions/element_b_2.ma".
include "ground/relocation/p1/pr_pushs.ma".
include "ground/relocation/p1/pr_uni.ma".

(* BASIC ELEMENTS FOR PARTIAL RELOCATION MAPS *******************************)

definition basic (d) (h): pr_map ≝ ⫯*[d] 𝐮❨h❩.

interpretation
  "basic elements (partial relocation maps)"
  'ElementB d h = (basic d h).

(* Basic constructions ******************************************************)

(*** at_basic_succ_sn *)
lemma pr_basic_succ_sn (d) (h): ⫯𝐛❨d,h❩ = 𝐛❨⁤↑d,h❩.
#d #h >pr_pushs_succ //
qed.

(*** at_basic_zero_succ *)
lemma pr_basic_zero_succ (h): ↑𝐛❨𝟎,h❩ = 𝐛❨𝟎,⁤↑h❩.
#h >pr_nexts_succ //
qed.
