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

include "ground/relocation/fb/fbr_lapp_lt.ma".
include "ground/relocation/fb/fbr_xapp_lapp.ma".
include "ground/relocation/fb/fbr_uni_ctls.ma".
include "delayed_updating/syntax/path_beta.ma".
include "delayed_updating/substitution/lift_rmap_closed.ma".

(* LIFT FOR RELOCATION MAP **************************************************)

(* Destructions with path_beta and pcc **************************************)

lemma pcc_lift_rmap_p3beta_lapp (f) (p) (b) (q) (n):
      q ϵ 𝐂❨n❩ → n = 🠢[𝐫❨p,b,q❩]f＠§❨n❩.
#f #p #b #q #n #Hq
<path_p3beta_unfold_b <fbr_lapp_xapp
<lift_rmap_append_L_closed_dx_xapp_succ //
qed-.

lemma pcc_lift_rmap_p3beta_xapp_immediate (f) (p) (b) (q) (n):
      q ϵ 𝐂❨n❩ → (⁤↑(♭b+n)) = 🠢[𝐫❨p,⓪b,q❩]f＠❨⁤↑(♭b+n)❩.
#f #p #b #q #n #Hq
<path_p3beta_unfold_dx <lift_rmap_append <lift_rmap_A_sx
<lift_rmap_append_clear_L_closed_dx_xapp_succ_plus //
qed-.

lemma pcc_lift_rmap_beta_delayed (f) (p) (b) (q) (n):
      q ϵ 𝐂❨n❩ → 🠢[p]f = 🠢[𝐫❨p,⓪b,q,⁤↑(♭b+n)❩]f.
#f #p #b #q #n #Hq
<path_beta_unfold_dx <lift_rmap_append <lift_rmap_A_sx <lift_rmap_d_dx
<(ctls_succ_plus_lift_rmap_append_clear_L_closed_dx … Hq) //
qed-.

lemma pcc_inv_lift_rmap_p3beta_lapp (f) (p) (b) (q) (n):
      q ϵ 𝐂❨🠢[𝐫❨p,b,q❩]f＠§❨n❩❩ → q ϵ 𝐂❨n❩.
#f #p #b #q #n #Hq
lapply (pcc_lift_rmap_p3beta_lapp f p b … Hq) #H0
lapply (eq_inv_fbr_lapp_bi … H0) -H0 #H0 destruct //
qed-.

lemma pcc_lift_rmap_p3beta_after_uni (f) (p) (b) (q) (n):
      q ϵ 𝐂❨n❩ →
      (𝐮❨⁤↑(♭b+n)❩•🠢[p]f) = 🠢[𝐫❨p,⓪b,q❩]f•𝐮❨⁤↑(♭b+n)❩.
#f #p #b #q #n #Hq
<fbr_after_uni_dx <(pcc_lift_rmap_p3beta_xapp_immediate … Hq)
<path_p3beta_unfold_dx <lift_rmap_append <lift_rmap_A_sx
<(ctls_succ_plus_lift_rmap_append_clear_L_closed_dx … Hq) //
qed-.
