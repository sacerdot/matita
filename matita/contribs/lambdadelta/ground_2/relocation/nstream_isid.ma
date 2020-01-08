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

include "ground_2/notation/functions/identity_0.ma".
include "ground_2/relocation/rtmap_isid.ma".

(* RELOCATION N-STREAM ******************************************************)

(* Specific inversion lemmas ************************************************)

lemma isid_inv_seq: ∀f,n. 𝐈❪n⨮f❫ → 𝐈❪f❫ ∧ 0 = n.
#f #n #H elim (isid_inv_gen … H) -H
#g #Hg #H elim (push_inv_seq_dx … H) -H /2 width=1 by conj/
qed-.
