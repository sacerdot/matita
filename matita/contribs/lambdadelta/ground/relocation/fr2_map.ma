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

include "ground/notation/functions/diamond_0.ma".
include "ground/notation/functions/semicolon_3.ma".
include "ground/arith/nat.ma".

(* FINITE RELOCATION MAPS WITH PAIRS ****************************************)

(*** mr2 *)
inductive fr2_map: Type[0] :=
(*** nil2 *)
  | fr2_nil : fr2_map
(*** cons2 *)
  | fr2_cons: nat → nat → fr2_map → fr2_map.

interpretation
  "nil (finite relocation maps with pairs)"
  'Diamond = (fr2_nil).

interpretation
  "cons (finite relocation maps with pairs)"
  'Semicolon d h f = (fr2_cons d h f).
