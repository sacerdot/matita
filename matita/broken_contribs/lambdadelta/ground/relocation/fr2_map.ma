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

include "ground/notation/functions/element_e_0.ma".
include "ground/notation/functions/black_halfcircleright_3.ma".
include "ground/arith/nat.ma".

(* FINITE RELOCATION MAPS WITH PAIRS ****************************************)

(*** mr2 *)
inductive fr2_map: Type[0] :=
(*** nil2 *)
| fr2_empty: fr2_map
(*** cons2 *)
| fr2_lcons: nat → nat → fr2_map → fr2_map
.

interpretation
  "empty (finite relocation maps with pairs)"
  'ElementE = (fr2_empty).

interpretation
  "left cons (finite relocation maps with pairs)"
  'BlackHalfCircleRight d h f = (fr2_lcons d h f).
