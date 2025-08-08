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

include "delayed_updating/syntax/path_closed_clear.ma".
include "delayed_updating/syntax/path_beta.ma".

(* PATHS FOR β-REDUCTION ****************************************************)

(* Constructions with pcc ***************************************************)

lemma path_beta_in_brd_pcc (b1) (q1) (n1) (n) (z1) (y):
      q1 ϵ 𝐂❨n1❩ → y◖𝗦●z1 ϵ 𝐂❨n❩ →
      (𝐫❨y,⓪b1,q1,⁤↑(♭b1+n1)❩)●z1 ϵ 𝐂❨n❩.
#b1 #q1 #n1 #n #z1 #y #Hq1 #Hq
>nplus_succ_dx >nplus_unit_sn
lapply (pcc_inv_S … Hq) -Hq #Hq
<path_beta_unfold_sx >list_append_rcons_sn
@pcc_d @pcc_d @(pcc_pcc … Hq1) -Hq1
@pcc_L @(pcc_pcc (⓪b1) (♭b1)) [ // ] @pcc_A //
qed.
