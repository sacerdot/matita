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

include "delayed_updating/notation/functions/subset_n_0.ma".
include "delayed_updating/syntax/path_structure_help.ma".
include "delayed_updating/syntax/path_balanced.ma".

(* SUBSET OF NEUTRAL PATHS **************************************************)

definition pnc: 𝒫❨ℙ❩ ≝
           {r | ∀b,q. ⊗b ϵ 𝐁 → r ⧸= b●𝗟◗q} (**) (* reverse ⧸= *)
.

interpretation
  "neutral (path subset)"
  'SubsetN = (pnc).

(* Basic constructions ******************************************************)

lemma pnc_A_sn (p):
      p ϵ 𝐍 → 𝗔◗p ϵ 𝐍.
#p #H1p #b #q #Hb #H2p
elim (pbc_inv_gen_sn … Hb) -Hb
[ #Hb
  elim (eq_inv_path_A_sn_append_flat_sn … H2p) -H2p // -Hb #H0
  elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
| * #b1 #b2 #Hb1 #_ #H0
  elim (eq_inv_A_sn_structure … H0) -H0 #r1 #r2 #Hr1 #Hr2 #H0 destruct
  <path_append_pAbLq_7 in H2p; #H0
  elim (eq_inv_path_A_sn_append_flat_sn … H0) -H0 // -Hr1 #H0 #_
  elim (eq_inv_list_rcons_bi ????? H0) -H0 #H0 #_ destruct
  elim (eq_inv_append_structure … Hr2) -Hr2 #r3 #r4 #Hr3 #Hr4 #H0 destruct
  elim (eq_inv_L_dx_structure … Hr3) -Hr3 #r5 #r6 #Hr5 #_ #H0 destruct
  <path_append_pLbLq in H1p; #H1p
  @H1p -H1p //
]
qed.
