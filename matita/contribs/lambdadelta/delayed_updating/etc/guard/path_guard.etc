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

include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/class_g_0.ma".
include "ground/lib/subset.ma".

(* GUARD CONDITION FOR PATH *************************************************)

inductive pgc: predicate path ≝
| pgc_empty: (𝐞) ϵ pgc
| pgc_L_dx (p): p◖𝗟 ϵ pgc
.

interpretation
  "guard condition (path)"
  'ClassG = (pgc).
