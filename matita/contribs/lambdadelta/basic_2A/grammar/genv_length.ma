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

include "basic_2A/grammar/genv.ma".

(* LENGTH OF A GLOBAL ENVIRONMENT *******************************************)

let rec glength L ≝ match L with
[ GAtom       ⇒ 0
| GPair G _ _ ⇒ glength G + 1
].

interpretation "length (global environment)" 'card G = (glength G).
