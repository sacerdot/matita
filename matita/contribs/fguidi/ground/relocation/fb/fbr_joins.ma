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

include "ground/relocation/fb/fbr_uni.ma".
include "ground/relocation/fb/fbr_after.ma".
include "ground/notation/functions/rightuparrowstar_2.ma".

(* ITERATED JOIN FOR FINITE RELOCATION MAPS WITH BOOLEANS *******************)

interpretation
  "iterated join (finite relocation maps with booleans)"
  'RightUpArrowStar n f = (fbr_after f (fbr_uni n)).
