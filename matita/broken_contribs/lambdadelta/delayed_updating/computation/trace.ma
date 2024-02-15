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

include "delayed_updating/notation/functions/category_pstar_0.ma".
include "delayed_updating/syntax/path.ma".

(* TRACE ********************************************************************)

(* Note: a trace is a list of redexes fired in a computation *)
(* Note: constructed from the first (left end) to the last (right end) *)
interpretation
  "trace ()"
  'CategoryPStar = (list (list label)).

interpretation
  "empty (trace)"
  'ElementE = (list_empty (list label)).

interpretation
  "left cons (trace)"
  'BlackHalfCircleRight r ss = (list_lcons (list label) r ss).

interpretation
  "append (trace)"
  'BlackCircle rs ss = (list_append (list label) rs ss).

interpretation
  "right cons (trace)"
  'BlackHalfCircleLeft rs s = (list_append (list label) rs (list_lcons (list label) s (list_empty (list label)))).
