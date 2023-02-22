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

include "basic_2/relocation/ldrop_append.ma".
include "basic_2/reduction/crx.ma".

(* REDUCIBLE TERMS FOR CONTEXT-SENSITIVE EXTENDED REDUCTION *****************)

(* Advanved properties ******************************************************)

lemma crx_append_sn: ∀h,g,G,L,K,T. ⦃G, L⦄ ⊢ ➡[h, g] 𝐑⦃T⦄  → ⦃G, K @@ L⦄ ⊢ ➡[h, g] 𝐑⦃T⦄.
#h #g #G #L #K0 #T #H elim H -L -T
/2 width=2 by crx_sort, crx_appl_sn, crx_appl_dx, crx_ri2, crx_ib2_sn, crx_ib2_dx, crx_beta, crx_theta/
#I #L #K #V #i #HLK
lapply (ldrop_fwd_length_lt2 … HLK) #Hi
lapply (ldrop_O1_append_sn_le … HLK … K0) -HLK /2 width=4 by crx_delta, lt_to_le/
qed.

lemma trx_crx: ∀h,g,G,L,T. ⦃G, ⋆⦄ ⊢ ➡[h, g] 𝐑⦃T⦄ → ⦃G, L⦄ ⊢ ➡[h, g] 𝐑⦃T⦄.
#h #g #G #L #T #H lapply (crx_append_sn … H) //
qed.
