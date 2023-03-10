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

include "basic_2A/reduction/cpr_lift.ma".
include "basic_2A/reduction/cnr.ma".

(* NORMAL TERMS FOR CONTEXT-SENSITIVE REDUCTION *****************************)

(* Advanced properties ******************************************************)

lemma cnr_lref_abst: ∀G,L,K,V,i. ⬇[i] L ≡ K. ⓛV → ⦃G, L⦄ ⊢ ➡ 𝐍⦃#i⦄.
#G #L #K #V #i #HLK #X #H
elim (cpr_inv_lref1 … H) -H // *
#K0 #V1 #V2 #HLK0 #_ #_
lapply (drop_mono … HLK … HLK0) -L #H destruct
qed.

(* Relocation properties ****************************************************)

lemma cnr_lift: ∀G,L0,L,T,T0,s,l,m. ⦃G, L⦄ ⊢ ➡ 𝐍⦃T⦄ →
                ⬇[s, l, m] L0 ≡ L → ⬆[l, m] T ≡ T0 → ⦃G, L0⦄ ⊢ ➡ 𝐍⦃T0⦄.
#G #L0 #L #T #T0 #s #l #m #HLT #HL0 #HT0 #X #H
elim (cpr_inv_lift1 … H … HL0 … HT0) -L0 #T1 #HT10 #HT1
>(HLT … HT1) in HT0; -L #HT0
>(lift_mono … HT10 … HT0) -T1 -X //
qed.

lemma cnr_inv_lift: ∀G,L0,L,T,T0,s,l,m. ⦃G, L0⦄ ⊢ ➡ 𝐍⦃T0⦄ →
                    ⬇[s, l, m] L0 ≡ L → ⬆[l, m] T ≡ T0 → ⦃G, L⦄ ⊢ ➡ 𝐍⦃T⦄.
#G #L0 #L #T #T0 #s #l #m #HLT0 #HL0 #HT0 #X #H
elim (lift_total X l m) #X0 #HX0
lapply (cpr_lift … H … HL0 … HT0 … HX0) -L #HTX0
<(HLT0 … HTX0) in HX0; -L0 -X0 #H
>(lift_inj … H … HT0) -T0 -X -s -l -m //
qed-.
