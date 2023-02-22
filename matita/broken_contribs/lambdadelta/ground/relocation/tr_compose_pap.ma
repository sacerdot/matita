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

include "ground/relocation/tr_compose.ma".
include "ground/relocation/tr_pap_tls.ma".

(* COMPOSITION FOR TOTAL RELOCATION MAPS ************************************)

(* Constructions with tr_pap ************************************************)

(*** compose_apply *)
lemma tr_compose_pap (i) (f1) (f2):
      f2＠⧣❨f1＠⧣❨i❩❩ = (f2∘f1)＠⧣❨i❩.
#i elim i -i
[ * #p1 #f1 #f2
  <tr_compose_unfold <tr_cons_pap_unit <tr_cons_pap_unit //
| #i #IH * #p1 #f1 #f2
  <tr_compose_unfold <tr_cons_pap_succ <tr_cons_pap_succ //
]
qed.
