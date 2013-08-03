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

include "basic_2/reduction/cpx_lift.ma".
include "basic_2/reduction/cnx.ma".

(* CONTEXT-SENSITIVE EXTENDED NORMAL TERMS **********************************)

(* Advanced properties ******************************************************)

lemma cnx_lref_atom: ∀h,g,G,L,i. ⇩[0, i] L ≡ ⋆ → ⦃G, L⦄ ⊢ 𝐍[h, g]⦃#i⦄.
#h #g #G #L #i #HL #X #H
elim (cpx_inv_lref1 … H) -H // *
#I #K #V1 #V2 #HLK #_ #_
lapply (ldrop_mono … HL … HLK) -L #H destruct
qed.

(* Relocation properties ****************************************************)

lemma cnx_lift: ∀h,g,G,L0,L,T,T0,d,e. ⦃G, L⦄ ⊢ 𝐍[h, g]⦃T⦄ → ⇩[d, e] L0 ≡ L →
                ⇧[d, e] T ≡ T0 → ⦃G, L0⦄ ⊢ 𝐍[h, g]⦃T0⦄.
#h #g #G #L0 #L #T #T0 #d #e #HLT #HL0 #HT0 #X #H
elim (cpx_inv_lift1 … H … HL0 … HT0) -L0 #T1 #HT10 #HT1
<(HLT … HT1) in HT0; -L #HT0
>(lift_mono … HT10 … HT0) -T1 -X //
qed.

lemma cnx_inv_lift: ∀h,g,G,L0,L,T,T0,d,e. ⦃G, L0⦄ ⊢ 𝐍[h, g]⦃T0⦄ → ⇩[d, e] L0 ≡ L →
                    ⇧[d, e] T ≡ T0 → ⦃G, L⦄ ⊢ 𝐍[h, g]⦃T⦄.
#h #g #G #L0 #L #T #T0 #d #e #HLT0 #HL0 #HT0 #X #H
elim (lift_total X d e) #X0 #HX0
lapply (cpx_lift … H … HL0 … HT0 … HX0) -L #HTX0
>(HLT0 … HTX0) in HX0; -L0 -X0 #H
>(lift_inj … H … HT0) -T0 -X -d -e //
qed-.
