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

include "ground/relocation/fu/fur_map.ma".
include "ground/notation/functions/element_u_1.ma".

(* UNIFORM ELEMENTS FOR FINITE RELOCATION MAPS FOR UNWIND *******************)

definition fur_uni (n): fur_map ≝
           (⮤*[n]𝐢)
.

interpretation
  "uniform elements (finite relocation maps for unwind)"
  'ElementU n = (fur_uni n).

(* Basic constructions ******************************************************)

lemma fur_uni_unfold (n):
      (⮤*[n]𝐢) = 𝐮❨n❩.
// qed.
