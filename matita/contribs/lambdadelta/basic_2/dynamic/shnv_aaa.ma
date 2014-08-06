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

include "basic_2/dynamic/snv_aaa.ma".
include "basic_2/dynamic/shnv.ma".

(* STRATIFIED HIGHER NATIVE VALIDITY FOR TERMS ******************************)

(* Advanced properties ******************************************************)

lemma snv_shnv_cast: ∀h,g,G,L,U,T. ⦃G, L⦄ ⊢ ⓝU.T ¡[h, g] → ⦃G, L⦄ ⊢ ⓝU.T ¡[h, g, 0].
#h #g #G #L #U #T #H elim (snv_inv_cast … H) -H
#U0 #HU #HT #HU0 #HTU0 @shnv_cast // -HT
#l #H <(le_n_O_to_eq … H) -l
elim (snv_fwd_da … HU) -HU /3 width=3 by cprs_scpds, scpds_div/
qed.
