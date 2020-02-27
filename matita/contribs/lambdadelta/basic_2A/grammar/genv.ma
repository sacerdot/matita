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

include "basic_2A/notation/constructors/star_0.ma".
include "basic_2A/notation/constructors/dxbind2_3.ma".
include "basic_2A/notation/constructors/dxabbr_2.ma".
include "basic_2A/notation/constructors/dxabst_2.ma".
include "basic_2A/grammar/term.ma".

(* GLOBAL ENVIRONMENTS ******************************************************)

(* global environments *)
inductive genv: Type[0] ≝
| GAtom: genv                       (* empty *)
| GPair: genv → bind2 → term → genv (* binary binding construction *)
.

interpretation "sort (global environment)"
   'Star = (GAtom).

interpretation "global environment binding construction (binary)"
   'DxBind2 G I T = (GPair G I T).

interpretation "abbreviation (global environment)"
   'DxAbbr G T = (GPair G Abbr T).

interpretation "abstraction (global environment)"
   'DxAbst G T = (GPair G Abst T).

(* Basic properties *********************************************************)

axiom eq_genv_dec: ∀G1,G2:genv. Decidable (G1 = G2).
