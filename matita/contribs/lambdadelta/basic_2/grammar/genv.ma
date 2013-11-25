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

include "ground_2/lib/list.ma".
include "basic_2/notation/constructors/star_0.ma".
include "basic_2/notation/constructors/dxbind2_3.ma".
include "basic_2/notation/constructors/dxabbr_2.ma".
include "basic_2/notation/constructors/dxabst_2.ma".
include "basic_2/grammar/term.ma".

(* GLOBAL ENVIRONMENTS ******************************************************)

(* global environments *)
definition genv ≝ list2 bind2 term.

interpretation "sort (global environment)"
   'Star = (nil2 bind2 term).

interpretation "global environment binding construction (binary)"
   'DxBind2 L I T = (cons2 bind2 term I T L).

interpretation "abbreviation (global environment)"
   'DxAbbr L T = (cons2 bind2 term Abbr T L).

interpretation "abstraction (global environment)"
   'DxAbst L T = (cons2 bind2 term Abst T L).

(* Basic properties *********************************************************)

axiom eq_genv_dec: ∀G1,G2:genv. Decidable (G1 = G2).
