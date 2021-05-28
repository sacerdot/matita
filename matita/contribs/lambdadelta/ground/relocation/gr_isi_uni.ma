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

include "ground/relocation/gr_uni.ma".
include "ground/relocation/gr_isi_id.ma".

(* IDENTITY CONDITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Properties with test for identity ****************************************)

(*** uni_inv_isid uni_isi *)
lemma gr_uni_isi (f): 𝐮❨𝟎❩ ≡ f → 𝐈❪f❫.
/2 width=1 by gr_eq_id_isi/ qed.

(* Inversion lemmas with test for identity **********************************)

(*** uni_isid isi_inv_uni *)
lemma gr_isi_inv_uni (f): 𝐈❪f❫ → 𝐮❨𝟎❩ ≡ f.
/2 width=1 by gr_isi_inv_eq_id/ qed-.
