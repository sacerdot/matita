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

(* NOTATION (equivalence relation) ************************************)

notation > "hvbox(a break ∼ term 46 b)"
  non associative with precedence 45
  for @{ 'Equiv ? $a $b }.

notation < "hvbox(term 46 a break maction (∼) (∼\sub t) term 46 b)"
  non associative with precedence 45
  for @{ 'Equiv $t $a $b }.
