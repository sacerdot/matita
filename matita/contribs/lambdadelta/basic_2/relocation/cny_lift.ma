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

include "basic_2/relocation/cpy_lift.ma".
include "basic_2/relocation/cny.ma".

(* NORMAL TERMS FOR CONTEXT-SENSITIVE EXTENDED SUBSTITUTION *****************)

(* Properties on relocation *************************************************)

lemma cny_lift_le: ∀G,L,K,T,U,s,d,dt,e,et. ⦃G, K⦄ ⊢ ▶[dt, et] 𝐍⦃T⦄ → ⇩[s, d, e] L ≡ K →
                   ⇧[d, e] T ≡ U → dt + et ≤ d → ⦃G, L⦄ ⊢ ▶[dt, et] 𝐍⦃U⦄.
#G #L #K #T1 #U1 #s #d #dt #e #et #HT1 #HLK #HTU1 #Hdetd #U2 #HU12
elim (cpy_inv_lift1_le … HU12 … HLK … HTU1) // -L -Hdetd #T2 #HT12
>(HT1 … HT12) -K /2 width=5 by lift_mono/
qed-.

lemma cny_lift_be: ∀G,L,K,T,U,s,d,dt,e,et. ⦃G, K⦄ ⊢ ▶[dt, et] 𝐍⦃T⦄ → ⇩[s, d, e] L ≡ K →
                   ⇧[d, e] T ≡ U → dt ≤ d → yinj d ≤ dt + et → ⦃G, L⦄ ⊢ ▶[dt, et+e] 𝐍⦃U⦄.
#G #L #K #T1 #U1 #s #d #dt #e #et #HT1 #HLK #HTU1 #Hdtd #Hddet #U2 #HU12
elim (cpy_inv_lift1_be … HU12 … HLK … HTU1) /2 width=1 by monotonic_yle_plus_dx/ -L -Hdtd -Hddet #T2
>yplus_minus_inj #HT12 >(HT1 … HT12) -K /2 width=5 by lift_mono/
qed-.

lemma cny_lift_ge: ∀G,L,K,T,U,s,d,dt,e,et. ⦃G, K⦄ ⊢ ▶[dt, et] 𝐍⦃T⦄ → ⇩[s, d, e] L ≡ K →
                   ⇧[d, e] T ≡ U → d ≤ dt → ⦃G, L⦄ ⊢ ▶[dt+e, et] 𝐍⦃U⦄.
#G #L #K #T1 #U1 #s #d #dt #e #et #HT1 #HLK #HTU1 #Hddt #U2 #HU12
elim (cpy_inv_lift1_ge … HU12 … HLK … HTU1) /2 width=1 by monotonic_yle_plus_dx/ -L -Hddt #T2
>yplus_minus_inj #HT12 >(HT1 … HT12) -K /2 width=5 by lift_mono/
qed-.

(* Inversion lemmas on relocation *******************************************)

lemma cny_lift_inv_le: ∀G,L,K,T,U,s,d,dt,e,et. ⦃G, L⦄ ⊢ ▶[dt, et] 𝐍⦃U⦄ → ⇩[s, d, e] L ≡ K →
                       ⇧[d, e] T ≡ U → dt + et ≤ d → ⦃G, K⦄ ⊢ ▶[dt, et] 𝐍⦃T⦄.
#G #L #K #T1 #U1 #s #d #dt #e #et #HU1 #HLK #HTU1 #Hdetd #T2 #HT12
elim (lift_total T2 d e) #U2 #HTU2
lapply (cpy_lift_le … HT12 … HLK … HTU1 … HTU2 ?) // -K -Hdetd #HU12
lapply (HU1 … HU12) -L /2 width=5 by lift_inj/
qed-.

lemma cny_lift_inv_be: ∀G,L,K,T,U,s,d,dt,e,et. ⦃G, L⦄ ⊢ ▶[dt, et] 𝐍⦃U⦄ → ⇩[s, d, e] L ≡ K →
                       ⇧[d, e] T ≡ U → dt ≤ d → yinj d + e ≤ dt + et → ⦃G, K⦄ ⊢ ▶[dt, et-e] 𝐍⦃T⦄.
#G #L #K #T1 #U1 #s #d #dt #e #et #HU1 #HLK #HTU1 #Hdtd #Hdedet #T2 #HT12
lapply (yle_fwd_plus_ge_inj … Hdedet) // #Heet
elim (yle_inv_plus_inj2 … Hdedet) -Hdedet #Hddete #Hedet
elim (lift_total T2 d e) #U2 #HTU2
lapply (cpy_lift_be … HT12 … HLK … HTU1 … HTU2 ? ?) // [ >yplus_minus_assoc_inj // ] -K -Hdtd -Hddete
>ymax_pre_sn // -Heet #HU12
lapply (HU1 … HU12) -L /2 width=5 by lift_inj/
qed-.

lemma cny_lift_inv_ge: ∀G,L,K,T,U,s,d,dt,e,et. ⦃G, L⦄ ⊢ ▶[dt, et] 𝐍⦃U⦄ → ⇩[s, d, e] L ≡ K →
                       ⇧[d, e] T ≡ U → yinj d + e ≤ dt → ⦃G, K⦄ ⊢ ▶[dt-e, et] 𝐍⦃T⦄.
#G #L #K #T1 #U1 #s #d #dt #e #et #HU1 #HLK #HTU1 #Hdedt #T2 #HT12
elim (yle_inv_plus_inj2 … Hdedt) -Hdedt #Hddte #Hedt
elim (lift_total T2 d e) #U2 #HTU2
lapply (cpy_lift_ge … HT12 … HLK … HTU1 … HTU2 ?) // -K -Hddte
>ymax_pre_sn // -Hedt #HU12
lapply (HU1 … HU12) -L /2 width=5 by lift_inj/
qed-.
