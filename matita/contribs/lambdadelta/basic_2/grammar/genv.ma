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

include "ground_2/list.ma".
include "basic_2/grammar/term.ma".

(* GLOBAL ENVIRONMENTS ******************************************************)

(* global environments *)
definition genv ≝ list2 bind2 term.

interpretation "sort (global environment)"
   'Star = (nil2 bind2 term).

interpretation "environment construction (binary)"
   'DxItem2 L I T = (cons2 bind2 term I T L).

interpretation "environment binding construction (binary)"
   'DxBind2 L I T = (cons2 bind2 term I T L).

interpretation "abbreviation (global environment)"
   'DxAbbr L T = (cons2 bind2 term Abbr T L).

interpretation "abstraction (global environment)"
   'DxAbst L T = (cons2 bind2 term Abst T L).

(* Basic properties *********************************************************)

axiom genv_eq_dec: ∀T1,T2:genv. Decidable (T1 = T2).
