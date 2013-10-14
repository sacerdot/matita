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

(* CONTEXT-SENSITIVE EXTENDED REDUCIBLE TERMS *******************************)

(* Advanved properties ******************************************************)

lemma crx_append_sn: ∀h,g,G,L,K,T. ⦃G, L⦄ ⊢ 𝐑[h, g]⦃T⦄  → ⦃G, K @@ L⦄ ⊢ 𝐑[h, g]⦃T⦄.
#h #g #G #L #K0 #T #H elim H -L -T /2 width=1/ /2 width=2/
#I #L #K #V #i #HLK
lapply (ldrop_fwd_length_lt2 … HLK) #Hi
lapply (ldrop_O1_append_sn_le … HLK … K0) -HLK /2 width=2/ -Hi /2 width=4/
qed.

lemma trx_crx: ∀h,g,G,L,T. ⦃G, ⋆⦄ ⊢ 𝐑[h, g]⦃T⦄ → ⦃G, L⦄ ⊢ 𝐑[h, g]⦃T⦄.
#h #g #G #L #T #H lapply (crx_append_sn … H) //
qed.