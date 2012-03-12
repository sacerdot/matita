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

include "basic_2/grammar/term.ma".

(* LOCAL ENVIRONMENTS *******************************************************)

(* local environments *)
inductive lenv: Type[0] ≝
| LAtom: lenv                       (* empty *)
| LPair: lenv → bind2 → term → lenv (* binary binding construction *)
.

interpretation "sort (local environment)"
   'Star = LAtom.

interpretation "environment construction (binary)"
   'DxItem2 L I T = (LPair L I T).

interpretation "environment binding construction (binary)"
   'DxBind2 L I T = (LPair L I T).

interpretation "abbreviation (local environment)"
   'DxAbbr L T = (LPair L Abbr T).

interpretation "abstraction (local environment)"
   'DxAbst L T = (LPair L Abst T).