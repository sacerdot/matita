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

include "ground/notation/functions/atsharp_2.ma".
include "ground/arith/pnat_plus.ma".
include "ground/relocation/tr_map.ma".

(* POSITIVE APPLICATION FOR TOTAL RELOCATION MAPS ***************************)

(*** apply *)
rec definition tr_pap (i: pnat) on i: tr_map → pnat.
* #p #f cases i -i
[ @p
| #i lapply (tr_pap i f) -tr_pap -i -f
  #i @(i+p)
]
defined.

interpretation
  "functional positive application (total relocation maps)"
  'AtSharp f i = (tr_pap i f).

(* Basic constructions ******************************************************)

(*** apply_O1 *)
lemma tr_cons_pap_unit (f):
      ∀p. p = (p⨮f)＠⧣❨𝟏❩.
// qed.

(*** apply_S1 *)
lemma tr_cons_pap_succ (f):
      ∀p,i. f＠⧣❨i❩+p = (p⨮f)＠⧣❨↑i❩.
// qed.
