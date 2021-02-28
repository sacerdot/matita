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

include "ground/lib/ltc.ma".
include "ground/arith/nat_plus.ma".

(* NAT-LABELED REFLEXIVE AND TRANSITIVE CLOSURE FOR λδ-2A *******************)

definition lstar_aux (B) (R:relation B) (l): relation B ≝
           λb1,b2. ∨∨ (∧∧ l = 𝟎 & b1 = b2) | (∧∧ l = 𝟏  & R b1 b2).

definition lstar (B) (R:relation B): nat → relation B ≝
           ltc … nplus … (lstar_aux … R).

definition llstar (A) (B) (R:relation3 A B B) (l:nat): relation3 A B B ≝
           λa. lstar … (R a) l.
