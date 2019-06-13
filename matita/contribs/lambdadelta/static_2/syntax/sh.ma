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

include "ground_2/lib/arith.ma".
include "static_2/notation/functions/upspoon_2.ma".

(* SORT HIERARCHY ***********************************************************)

(* sort hierarchy specification *)
record sh: Type[0] ≝ {
  next: nat → nat (* next sort in the hierarchy *)
}.

interpretation "next sort (sort hierarchy)"
   'UpSpoon h s = (next h s).
