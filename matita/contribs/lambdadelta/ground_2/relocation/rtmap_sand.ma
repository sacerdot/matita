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

include "ground_2/notation/relations/rintersection_3.ma".
include "ground_2/relocation/rtmap_sle.ma".

coinductive sand: relation3 rtmap rtmap rtmap ≝
| sand_pp: ∀f1,f2,f,g1,g2,g. sand f1 f2 f → ↑f1 = g1 → ↑f2 = g2 → ↑f = g → sand g1 g2 g
| sand_np: ∀f1,f2,f,g1,g2,g. sand f1 f2 f → ⫯f1 = g1 → ↑f2 = g2 → ↑f = g → sand g1 g2 g
| sand_pn: ∀f1,f2,f,g1,g2,g. sand f1 f2 f → ↑f1 = g1 → ⫯f2 = g2 → ↑f = g → sand g1 g2 g
| sand_nn: ∀f1,f2,f,g1,g2,g. sand f1 f2 f → ⫯f1 = g1 → ⫯f2 = g2 → ⫯f = g → sand g1 g2 g
.

interpretation "intersection (rtmap)"
   'RIntersection f1 f2 f = (sand f1 f2 f).

(* Basic properties *********************************************************)

let corec sand_refl: ∀f. f ⋒ f ≡ f ≝ ?.
#f cases (pn_split f) * #g #H
[ @(sand_pp … H H H) | @(sand_nn … H H H) ] -H //
qed.

let corec sand_sym: ∀f1,f2,f. f1 ⋒ f2 ≡ f → f2 ⋒ f1 ≡ f ≝ ?.
#f1 #f2 #f * -f1 -f2 -f
#f1 #f2 #f #g1 #g2 #g #Hf * * * -g1 -g2 -g
[ @sand_pp | @sand_pn | @sand_np | @sand_nn ] /2 width=7 by/
qed-.
