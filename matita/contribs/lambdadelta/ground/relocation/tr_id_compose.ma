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

include "ground/relocation/tr_id_pap.ma".
include "ground/relocation/tr_compose_pap.ma".
include "ground/relocation/tr_pap_eq.ma".

(* IDENTITY ELEMENT FOR TOTAL RELOCATION MAPS *******************************)

(* Coonstructions with tr_compose *******************************************)

lemma tr_compose_id_sn (f):
      f â đ˘âf.
#f @nstream_eq_inv_ext #q //
qed.

lemma tr_compose_id_dx (f):
      f â fâđ˘.
#f @nstream_eq_inv_ext #q //
qed.
