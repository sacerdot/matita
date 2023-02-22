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

include "ground/arith/nat.ma".
include "static_2/notation/functions/uparrow_1_0.ma".

(* SORT HIERARCHY ***********************************************************)

(* sort hierarchy specification *)
record sh: Type[0] ≝ {
  sh_next: nat → nat (* next sort in the hierarchy *)
}.

interpretation "next sort (sort hierarchy)"
   'UpArrow_1_0 h = (sh_next h).

definition sh_is_next (h): relation nat ≝
           λs1,s2. ⇡[h]s1 = s2.
