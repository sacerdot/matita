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

include "ground/arith/int.ma".
include "ground/lib/functions.ma".
include "ground/notation/functions/atsharp_2.ma".

(* TOTAL RELOCATION MAPS WITH INTEGERS **************************************)

record trz_map: Type[0] ≝
{ trz_staff    : ℤ → ℤ
; trz_injective: injective_2_fwd … (eq …) (eq …) trz_staff
}.

interpretation
  "depth application (total relocation maps with integers)"
  'AtSharp f z = (trz_staff f z).
