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

include "delayed_updating/relocation/tr_minus_pap.ma".
include "ground/relocation/tr_compose_pap.ma".
include "ground/relocation/tr_pap_eq.ma".

(* RIGHT SUBTRACTION FOR TOTAL RELOCATION MAPS ******************************)

(* Constructions with tr_compose ********************************************)

lemma tr_compose_minus_dx (g) (f) (e):
      (g•f)-e ≗ g•(f-e).
#g #f #e
@nstream_eq_inv_ext #i
<tr_compose_pap
elim (pnat_split_le_ge (f＠⧣❨i❩) (i+e)) #Hi
[ <(tr_pap_minus_le … Hi)
  <tr_pap_minus_ge