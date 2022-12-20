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

include "delayed_updating/substitution/lift_path.ma".
include "delayed_updating/syntax/path_closed.ma".
include "ground/relocation/xap.ma".

(* LIFT FOR PATH ************************************************************)

(* Constructions with pcc ***************************************************)

lemma lift_path_closed (o) (e) (f) (q) (n):
      q ϵ 𝐂❨o,n,e❩ → 🠡[f]q ϵ 𝐂❨o,🠢[f]q＠❨n❩,f＠❨e❩❩.
#o #e #f #q #n #H0 elim H0 -q -n //
#q #n [ #k #Ho ] #_ #IH
/2 width=1 by pcc_m_dx, pcc_L_dx, pcc_A_dx, pcc_S_dx/
/4 width=1 by pcc_d_dx, tr_xap_pos/
qed.

lemma lift_path_rmap_closed (o) (f) (p) (q) (n):
      q ϵ 𝐂❨o,n,𝟎❩ → 🠡[🠢[f]p]q ϵ 𝐂❨o,🠢[f](p●q)＠❨n❩,𝟎❩.
/2 width=1 by lift_path_closed/
qed.

lemma lift_path_rmap_closed_L (o) (f) (p) (q) (n):
      q ϵ 𝐂❨o,n,𝟎❩ → 🠡[🠢[f](p◖𝗟)]q ϵ 𝐂❨o,🠢[f](p●𝗟◗q)＠§❨n❩,𝟎❩.
#o #f #p #q #n #Hq
lapply (lift_path_closed … (🠢[f](p◖𝗟)) … Hq) #Hq0
lapply (pcc_L_sn … Hq) -Hq #Hq1
lapply (lift_path_rmap_closed … f p … Hq1) -Hq1
<lift_path_L_sn >lift_rmap_L_dx #Hq1
elim (pcc_inv_L_sn … Hq1 Hq0) -Hq1 #H0 #_
<H0 in Hq0; -H0 //
qed.
