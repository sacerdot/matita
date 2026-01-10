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

include "ground/notation/functions/downharpoonright_2.ma".
include "ground/lib/list.ma".

(* TAIL FOR LISTS ***********************************************************)

definition list_tl (A:Type[0]): list A → list A.
#A * [ @(ⓔ) | #_ #t @t ]
defined.

interpretation
  "tail (streams)"
  'DownHarpoonRight A t = (list_tl A t).

(* Basic constructions ******************************************************)

lemma list_tl_empty (A):
      ⓔ = ⇂❪A❫ⓔ.
// qed.

lemma list_tl_lcons (A) (a) (t):
      t = ⇂❪A❫(a⨮t).
// qed.
