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

include "delayed_updating/computation/prototerm_originated_irefs.ma".
include "delayed_updating/computation/preterm_sn_wn.ma".

(* STRONG NORMALIZATION FOR PRETERM *****************************************)

(* Constructions with topc **************************************************)

theorem topc_twn_tsn (t):
        t ϵ 𝐓 → t ϵ 𝐎⁺ → t ϵ 𝐖𝐍 → t ϵ 𝐒𝐍.
#t #H1t #H2t #H3t
/3 width=1 by wfinite_pirc_twn_tsn, topc_des_pirc_wfinite/
qed.
