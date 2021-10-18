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

include "ground/arith/nat_succ.ma".
include "static_2/syntax/genv.ma".

(* LENGTH OF A GLOBAL ENVIRONMENT *******************************************)

rec definition glength G on G ≝ match G with
[ GAtom       ⇒ 𝟎
| GPair G _ _ ⇒ ↑(glength G)
].

interpretation "length (global environment)"
  'card G = (glength G).
