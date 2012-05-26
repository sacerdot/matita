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

(* ON NUMBERS AND GAMES: MATITA SOURCE FILES
 * Invocation:
 *   - Patience on me to gain peace and perfection! -
 * 2012 May 25:
 *   specification starts.
 *)

include "basics/pts.ma".
include "notation.ma".

(* GAMES ********************************************************************)

inductive Game: Type[1] ≝
| game: ∀L,R:Type[0]. (L → Game) → (R → Game) → Game
.

interpretation  "game" 'Game = Game.
(*
notation > 
  "'Let' term 46 g ≡ { L , l | R , r } 'in' term 46 t"
  non associative with precedence 46
  for @{ 'Destructor (match $g with [ game ${ident L} ${ident R} ${ident l} ${ident r} ⇒ $t]) }.
*)
interpretation "game destructor" 'Destructor x = x.

definition pippo ≝ λx.
match x with [ game L R F G ⇒ x ].

(*
notation < "hvbox('if' \nbsp term 46 e \nbsp break 'then' \nbsp term 46 t \nbsp break 'else' \nbsp term 49 f \nbsp)" non associative with precedence 46
 for @{ match $e return $T with [ true ⇒ $t | false ⇒ $f]  }.
*)