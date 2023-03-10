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

include "basic_2A/reduction/cpx_lift.ma".
include "basic_2A/reduction/cnx.ma".

(* NORMAL TERMS FOR CONTEXT-SENSITIVE EXTENDED REDUCTION ********************)

(* Relocation properties ****************************************************)

lemma cnx_lift: ∀h,g,G,L0,L,T,T0,s,l,m. ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃T⦄ → ⬇[s, l, m] L0 ≡ L →
                ⬆[l, m] T ≡ T0 → ⦃G, L0⦄ ⊢ ➡[h, g] 𝐍⦃T0⦄.
#h #g #G #L0 #L #T #T0 #s #l #m #HLT #HL0 #HT0 #X #H
elim (cpx_inv_lift1 … H … HL0 … HT0) -L0 #T1 #HT10 #HT1
>(HLT … HT1) in HT0; -L #HT0
>(lift_mono … HT10 … HT0) -T1 -X //
qed.

lemma cnx_inv_lift: ∀h,g,G,L0,L,T,T0,s,l,m. ⦃G, L0⦄ ⊢ ➡[h, g] 𝐍⦃T0⦄ → ⬇[s, l, m] L0 ≡ L →
                    ⬆[l, m] T ≡ T0 → ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃T⦄.
#h #g #G #L0 #L #T #T0 #s #l #m #HLT0 #HL0 #HT0 #X #H
elim (lift_total X l m) #X0 #HX0
lapply (cpx_lift … H … HL0 … HT0 … HX0) -L #HTX0
<(HLT0 … HTX0) in HX0; -L0 -X0 #H
>(lift_inj … H … HT0) -T0 -X -l -m //
qed-.
