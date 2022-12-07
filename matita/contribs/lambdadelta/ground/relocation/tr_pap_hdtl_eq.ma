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

include "ground/relocation/tr_pap_hdtl.ma".
include "ground/lib/stream_hdtl_eq.ma".

(* POSITIVE APPLICATION FOR TOTAL RELOCATION MAPS ***************************)

(* Inversions with stream_eq and stream_tl **********************************)

lemma tr_eq_inv_pap_unit_tl_bi (f1) (f2):
      f1＠⧣❨𝟏❩ = f2＠⧣❨𝟏❩ → ⇂f1 ≗ ⇂f2 → f1 ≗ f2.
#f1 #f2 #H1 #H2
/2 width=1 by stream_eq_inv_hd_tl_bi/
qed-.
