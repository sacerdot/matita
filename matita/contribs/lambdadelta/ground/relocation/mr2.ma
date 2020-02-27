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
include "ground/lib/arith.ma".

(* MULTIPLE RELOCATION WITH PAIRS *******************************************)

inductive mr2: Type[0] :=
  | nil2 : mr2
  | cons2: nat → nat → mr2 → mr2.

interpretation "nil (multiple relocation with pairs)"
  'Diamond = (nil2).

interpretation "cons (multiple relocation with pairs)"
  'Semicolon hd1 hd2 tl = (cons2 hd1 hd2 tl).
