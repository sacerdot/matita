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

include "delayed_updating/syntax/path_beta.ma".
include "delayed_updating/unwind/unwind2_rmap_closed.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

(* Constructions with path_beta *********************************************)

lemma unwind2_rmap_beta_bLq (f) (p) (b) (q) (n):
      ▶[b●𝗟◗q]▶[p]f • 𝐮❨n❩ = ▶[𝐫❨p,b,q,n❩]f.
#f #p #b #q #n
<unwind2_rmap_d_dx >unwind2_rmap_A_sx >unwind2_rmap_append //
qed.

lemma unwind2_rmap_p3beta_bLq (f) (p) (b) (q):
      ▶[b●𝗟◗q]▶[p]f = ▶[𝐫❨p,b,q❩]f.
#f #p #b #q
>unwind2_rmap_A_sx >unwind2_rmap_append //
qed.

(* Constructions with path_beta and pcc *************************************)

lemma eq_depth_unwind2_rmap_p3beta_lapp_pcc (f) (p) (b) (q) (n):
      ♭q = ▶[𝐫❨p,b,q❩]f＠§❨n❩ →
      q ϵ 𝐂❨n❩.
#f #p #b #q #n #Hq
@(eq_depth_unwind2_rmap_Lq_lapp_pcc … (▶[(p◖𝗔)●b]f))
>unwind2_rmap_append >Hq -Hq //
qed.

(* Inversions with path_beta and pcc ****************************************)

lemma pcc_eq_depth_unwind2_rmap_p3beta_lapp (f) (p) (b) (q) (n):
      q ϵ 𝐂❨n❩  →
      ♭q = ▶[𝐫❨p,b,q❩]f＠§❨n❩.
#f #p #b #q #n #Hq
>(unwind2_rmap_append_closed_Lq_dx_lapp_depth f (p●𝗔◗b) … Hq) -Hq //
qed-.
