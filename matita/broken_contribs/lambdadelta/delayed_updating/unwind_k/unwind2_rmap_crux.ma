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

include "ground/relocation/fb/fbr_rconss_xapp.ma".
include "delayed_updating/unwind_k/unwind2_rmap_clear.ma".
include "delayed_updating/unwind_k/unwind2_rmap_closed.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Crucial constructions with tr_uni ****************************************)

(* Note: crux of the commutation between unwind and balanced focused reduction *)
lemma unwind2_rmap_uni_crux (f) (b) (q) (n):
      q ϵ 𝐂❨n❩ →
      (𝐮❨⁤↑(♭b+♭q)❩) • f = ▶[⓪b●𝗟◗q]f • 𝐮❨⁤↑(♭b+n)❩.
#f #b #q #n #Hn
<fbr_after_uni_dx <fbr_xapp_succ_lapp
<unwind2_rmap_append_closed_Lq_dx_lapp_plus //
<unwind2_rmap_clear <fbr_xapp_pushs_le //
<ctls_succ_plus_unwind2_rmap_append_closed_Lq_dx //
qed-.
