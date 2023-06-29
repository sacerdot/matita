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

include "ground/relocation/fu/fur_pushs.ma".
include "ground/notation/functions/uparrowstar_2.ma".

(* ITERATED NEXT FOR FINITE RELOCATION MAPS FOR UNWIND **********************)

definition fur_nexts (n) (f): 𝔽𝕌 ≝
           (⮤*[n](⫯*[n]f)).

interpretation
  "iterated next (finite relocation maps for unwind)"
  'UpArrowStar n f = (fur_nexts n f).
