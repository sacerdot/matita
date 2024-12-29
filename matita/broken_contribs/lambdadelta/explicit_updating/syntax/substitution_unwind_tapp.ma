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

include "explicit_updating/syntax/substitution_tapp_eq.ma".
include "explicit_updating/syntax/substitution_tapp_lref.ma".
include "explicit_updating/syntax/substitution_unwind_eq.ma".

(* SUBSTITUTION FOR UNWIND **************************************************)

(* Constructions with subst_tapp and_subst_after ****************************)

lemma subst_after_tapp (t:𝕋) (f) (S):
      (S•f)＠⧣❨t❩ ≐ S＠⧣❨𝐬❨f❩＠⧣❨t❩❩.
#t elim t -t
[ #g #S
  <subst_tapp_unit <subst_tapp_unit
  <subst_after_dapp <subst_tapp_lref //
| #b #t #IH #g #S
  <subst_tapp_abst <subst_tapp_abst
  @term_eq_abst
  @(term_eq_repl … (IH (⫯g) (⫯S))) -IH
  /3 width=1 by subst_tapp_eq_repl/
| #v #t #IHv #IHt #g #S
  <subst_tapp_appl <subst_tapp_appl
  /2 width=1 by term_eq_appl/
| #f #t #IH #g #S
  <subst_tapp_lift <subst_tapp_lift
  @(term_eq_repl … (IH (g•f) S)) -IH
  /3 width=1 by subst_tapp_eq_repl/
]
qed.
