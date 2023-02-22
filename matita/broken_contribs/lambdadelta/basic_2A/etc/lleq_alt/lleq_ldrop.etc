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

include "basic_2/substitution/cpys_lift.ma".
include "basic_2/substitution/lleq.ma".

(* LAZY EQUIVALENCE FOR LOCAL ENVIRONMENTS **********************************)

(* Advanced properties ******************************************************)

lemma lleq_skip: ∀L1,L2,d,i. yinj i < d → |L1| = |L2| → L1 ⋕[#i, d] L2.
#L1 #L2 #d #i #Hid #HL12 @conj // -HL12
#U @conj #H elim (cpys_inv_lref1 … H) -H // *
#I #Z #Y #X #H elim (ylt_yle_false … Hid … H)
qed.

lemma lleq_lref: ∀I1,I2,L1,L2,K1,K2,V,d,i. d ≤ yinj i →
                 ⇩[i] L1 ≡ K1.ⓑ{I1}V → ⇩[i] L2 ≡ K2.ⓑ{I2}V →
                 K1 ⋕[V, 0] K2 → L1 ⋕[#i, d] L2.
#I1 #I2 #L1 #L2 #K1 #K2 #V #d #i #Hdi #HLK1 #HLK2 * #HK12 #IH @conj [ -IH | -HK12 ]
[ lapply (ldrop_fwd_length … HLK1) -HLK1 #H1
  lapply (ldrop_fwd_length … HLK2) -HLK2 #H2
  >H1 >H2 -H1 -H2 normalize //
| #U @conj #H elim (cpys_inv_lref1 … H) -H // *
  >yminus_Y_inj #I #K #X #W #_ #_ #H #HVW #HWU
  [ letin HLK ≝ HLK1 | letin HLK ≝ HLK2 ]
  lapply (ldrop_mono … H … HLK) -H #H destruct elim (IH W)
  /3 width=7 by cpys_subst_Y2/
]
qed.

lemma lleq_free: ∀L1,L2,d,i. |L1| ≤ i → |L2| ≤ i → |L1| = |L2| → L1 ⋕[#i, d] L2.
#L1 #L2 #d #i #HL1 #HL2 #HL12 @conj // -HL12
#U @conj #H elim (cpys_inv_lref1 … H) -H // *
#I #Z #Y #X #_ #_ #H lapply (ldrop_fwd_length_lt2 … H) -H
#H elim (lt_refl_false i) /2 width=3 by lt_to_le_to_lt/
qed.

(* Properties on relocation *************************************************)

lemma lleq_lift_le: ∀K1,K2,T,dt. K1 ⋕[T, dt] K2 →
                    ∀L1,L2,d,e. ⇩[Ⓕ, d, e] L1 ≡ K1 → ⇩[Ⓕ, d, e] L2 ≡ K2 →
                    ∀U. ⇧[d, e] T ≡ U → dt ≤ d → L1 ⋕[U, dt] L2.
#K1 #K2 #T #dt * #HK12 #IHT #L1 #L2 #d #e #HLK1 #HLK2 #U #HTU #Hdtd
lapply (ldrop_fwd_length … HLK1) lapply (ldrop_fwd_length … HLK2)
#H2 #H1 @conj // -HK12 -H1 -H2 #U0 @conj #HU0
[ letin HLKA ≝ HLK1 letin HLKB ≝ HLK2 | letin HLKA ≝ HLK2 letin HLKB ≝ HLK1 ]
elim (cpys_inv_lift1_be … HU0 … HLKA … HTU) // -HU0 >yminus_Y_inj #T0 #HT0 #HTU0
elim (IHT T0) [ #H #_ | #_ #H ] -IHT /3 width=12 by cpys_lift_be/
qed-.

lemma lleq_lift_ge: ∀K1,K2,T,dt. K1 ⋕[T, dt] K2 →
                    ∀L1,L2,d,e. ⇩[Ⓕ, d, e] L1 ≡ K1 → ⇩[Ⓕ, d, e] L2 ≡ K2 →
                    ∀U. ⇧[d, e] T ≡ U → d ≤ dt → L1 ⋕[U, dt+e] L2.
#K1 #K2 #T #dt * #HK12 #IHT #L1 #L2 #d #e #HLK1 #HLK2 #U #HTU #Hddt
lapply (ldrop_fwd_length … HLK1) lapply (ldrop_fwd_length … HLK2)
#H2 #H1 @conj // -HK12 -H1 -H2 #U0 @conj #HU0
[ letin HLKA ≝ HLK1 letin HLKB ≝ HLK2 | letin HLKA ≝ HLK2 letin HLKB ≝ HLK1 ]
elim (cpys_inv_lift1_ge … HU0 … HLKA … HTU) /2 width=1 by monotonic_yle_plus_dx/ -HU0 >yplus_minus_inj #T0 #HT0 #HTU0
elim (IHT T0) [ #H #_ | #_ #H ] -IHT /3 width=10 by cpys_lift_ge/
qed-.

(* Inversion lemmas on relocation *******************************************)

lemma lleq_inv_lift_le: ∀L1,L2,U,dt. L1 ⋕[U, dt] L2 →
                        ∀K1,K2,d,e. ⇩[Ⓕ, d, e] L1 ≡ K1 → ⇩[Ⓕ, d, e] L2 ≡ K2 →
                        ∀T. ⇧[d, e] T ≡ U → dt ≤ d → K1 ⋕[T, dt] K2.
#L1 #L2 #U #dt * #HL12 #IH #K1 #K2 #d #e #HLK1 #HLK2 #T #HTU #Hdtd
lapply (ldrop_fwd_length_minus2 … HLK1) lapply (ldrop_fwd_length_minus2 … HLK2)
#H2 #H1 @conj // -HL12 -H1 -H2
#T0 elim (lift_total T0 d e)
#U0 #HTU0 elim (IH U0) -IH
#H12 #H21 @conj #HT0
[ letin HLKA ≝ HLK1 letin HLKB ≝ HLK2 letin H0 ≝ H12 | letin HLKA ≝ HLK2 letin HLKB ≝ HLK1 letin H0 ≝ H21 ]
lapply (cpys_lift_be … HT0 … HLKA … HTU … HTU0) // -HT0
>yplus_Y1 #HU0 elim (cpys_inv_lift1_be … (H0 HU0) … HLKB … HTU) // -L1 -L2 -U -Hdtd
#X #HT0 #HX lapply (lift_inj … HX … HTU0) -U0 //
qed-.

lemma lleq_inv_lift_ge: ∀L1,L2,U,dt. L1 ⋕[U, dt] L2 →
                        ∀K1,K2,d,e. ⇩[Ⓕ, d, e] L1 ≡ K1 → ⇩[Ⓕ, d, e] L2 ≡ K2 →
                        ∀T. ⇧[d, e] T ≡ U → yinj d + e ≤ dt → K1 ⋕[T, dt-e] K2.
#L1 #L2 #U #dt * #HL12 #IH #K1 #K2 #d #e #HLK1 #HLK2 #T #HTU #Hdedt
lapply (ldrop_fwd_length_minus2 … HLK1) lapply (ldrop_fwd_length_minus2 … HLK2)
#H2 #H1 @conj // -HL12 -H1 -H2
elim (yle_inv_plus_inj2 … Hdedt) #Hddt #Hedt
#T0 elim (lift_total T0 d e)
#U0 #HTU0 elim (IH U0) -IH
#H12 #H21 @conj #HT0
[ letin HLKA ≝ HLK1 letin HLKB ≝ HLK2 letin H0 ≝ H12 | letin HLKA ≝ HLK2 letin HLKB ≝ HLK1 letin H0 ≝ H21 ]
lapply (cpys_lift_ge … HT0 … HLKA … HTU … HTU0) // -HT0 -Hddt
>ymax_pre_sn // #HU0 elim (cpys_inv_lift1_ge … (H0 HU0) … HLKB … HTU) // -L1 -L2 -U -Hdedt -Hedt
#X #HT0 #HX lapply (lift_inj … HX … HTU0) -U0 //
qed-.

lemma lleq_inv_lift_be: ∀L1,L2,U,dt. L1 ⋕[U, dt] L2 →
                        ∀K1,K2,d,e. ⇩[Ⓕ, d, e] L1 ≡ K1 → ⇩[Ⓕ, d, e] L2 ≡ K2 →
                        ∀T. ⇧[d, e] T ≡ U → d ≤ dt → dt ≤ yinj d + e → K1 ⋕[T, d] K2.
#L1 #L2 #U #dt * #HL12 #IH #K1 #K2 #d #e #HLK1 #HLK2 #T #HTU #Hddt #Hdtde
lapply (ldrop_fwd_length_minus2 … HLK1) lapply (ldrop_fwd_length_minus2 … HLK2)
#H2 #H1 @conj // -HL12 -H1 -H2
#T0 elim (lift_total T0 d e)
#U0 #HTU0 elim (IH U0) -IH
#H12 #H21 @conj #HT0
[ letin HLKA ≝ HLK1 letin HLKB ≝ HLK2 letin H0 ≝ H12 | letin HLKA ≝ HLK2 letin HLKB ≝ HLK1 letin H0 ≝ H21 ]
lapply (cpys_lift_ge … HT0 … HLKA … HTU … HTU0) // -HT0
#HU0 lapply (cpys_weak … HU0 dt (∞) ? ?) // -HU0
#HU0 lapply (H0 HU0)
#HU0 lapply (cpys_weak … HU0 d (∞) ? ?) // -HU0
#HU0 elim (cpys_inv_lift1_ge_up … HU0 … HLKB … HTU) // -L1 -L2 -U -Hddt -Hdtde
#X #HT0 #HX lapply (lift_inj … HX … HTU0) -U0 //
qed-.
