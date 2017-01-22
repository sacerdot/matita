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

(* THE FORMAL SYSTEM α: MATITA SOURCE FILES
 * Initial invocation : - Patience on me to gain peace and perfection! -
 * Developed since    : 2014 July 25
 *)

include "ground_2/lib/bool.ma".
include "ground_2/lib/arith.ma".

(* ITEMS ********************************************************************)

(* unary items *)
inductive item1: Type[0] ≝
   | Char: nat → item1 (* character: starting at 0 *)
   | LRef: nat → item1 (* reference by index: starting at 0 *)
   | GRef: nat → item1 (* reference by position: starting at 0 *)
   | Decl:       item1 (* global abstraction *)
.

(* binary items *)
inductive item2: Type[0] ≝
   | Abst:        item2 (* local abstraction *)
   | Abbr: bool → item2 (* local (Ⓣ) or global (Ⓕ) abbreviation *)
   | Proj: bool → item2 (* local (Ⓣ) or global (Ⓕ) projection *)
.
