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

include "Ground_2/list.ma".
include "Basic_2/grammar/term.ma".

(* GLOBAL ENVIRONMENTS ******************************************************)

(* global environments *)
definition genv ≝ list2 bind2 term.

interpretation "sort (global environment)"
   'Star = (nil2 bind2 term).

interpretation "environment binding construction (binary)"
   'DBind L I T = (cons2 bind2 term I T L).

(* Basic properties *********************************************************)

axiom genv_eq_dec: ∀T1,T2:genv. Decidable (T1 = T2).
