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

include "ground_2/xoa/xoa2.ma".
include "basic_2/notation/relations/lazyor_4.ma".
include "basic_2/relocation/lpx_sn_alt.ma".

(* POINTWISE UNION FOR LOCAL ENVIRONMENTS ***********************************)

inductive clor (T) (L2) (K1) (V1): predicate term ≝
| clor_sn: ∀U. |K1| < |L2| → ⇧[|L2|-|K1|-1, 1] U ≡ T → clor T L2 K1 V1 V1
| clor_dx: ∀I,K2,V2. |K1| < |L2| → (∀U. ⇧[|L2|-|K1|-1, 1] U ≡ T → ⊥) →
           ⇩[|L2|-|K1|-1] L2 ≡ K2.ⓑ{I}V2 → clor T L2 K1 V1 V2
.

definition llor: relation4 term lenv lenv lenv ≝
                 λT,L2. lpx_sn (clor T L2).

interpretation
   "lazy union (local environment)"
   'LazyOr L1 T L2 L = (llor T L2 L1 L).

(* Basic properties *********************************************************)

lemma llor_pair_sn: ∀I,L1,L2,L,V,T,U. L1 ⩖[T] L2 ≡ L →
                    |L1| < |L2| → ⇧[|L2|-|L1|-1, 1] U ≡ T →
                    L1.ⓑ{I}V ⩖[T] L2 ≡ L.ⓑ{I}V.
/3 width=2 by clor_sn, lpx_sn_pair/ qed.

lemma llor_pair_dx: ∀I,J,L1,L2,L,K2,V1,V2,T. L1 ⩖[T] L2 ≡ L →
                    |L1| < |L2| → (∀U. ⇧[|L2|-|L1|-1, 1] U ≡ T → ⊥) →
                    ⇩[|L2|-|L1|-1] L2 ≡ K2.ⓑ{J}V2 →
                    L1.ⓑ{I}V1 ⩖[T] L2 ≡ L.ⓑ{I}V2.
/4 width=3 by clor_dx, lpx_sn_pair/ qed.

lemma llor_total: ∀T,L2,L1. |L1| ≤ |L2| → ∃L. L1 ⩖[T] L2 ≡ L.
#T #L2 #L1 elim L1 -L1 /2 width=2 by ex_intro/
#L1 #I1 #V1 #IHL1 normalize
#H elim IHL1 -IHL1 /2 width=3 by transitive_le/
#L #HT elim (is_lift_dec T (|L2|-|L1|-1) 1)
[ * /3 width=2 by llor_pair_sn, ex_intro/
| elim (ldrop_O1_lt L2 (|L2|-|L1|-1))
  /5 width=4 by llor_pair_dx, monotonic_lt_minus_l, ex_intro/
]
qed-.

(* Alternative definition ***************************************************)

(* Note: uses minus_minus_comm, minus_plus_m_m, commutative_plus, plus_minus *)
lemma plus_minus_minus_be: ∀x,y,z. y ≤ z → z ≤ x → (x - z) + (z - y) = x - y.
#x #z #y #Hzy #Hyx >plus_minus // >commutative_plus >plus_minus //
qed-.

fact plus_minus_minus_be_aux: ∀i,x,y,z. y ≤ z → z ≤ x → i = z - y → x - z + i = x - y.
/2 width=1 by plus_minus_minus_be/ qed-.

lemma llor_intro_alt: ∀T,L2,L1,L. |L1| ≤ |L2| → |L1| = |L| →
                      (∀I1,I,K1,K,V1,V,i. ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L ≡ K.ⓑ{I}V →
                         (∀U. ⇧[|L2|-|L1|+i, 1] U ≡ T →
                              ∧∧ I1 = I & V1 = V & K1 ⩖[T] L2 ≡ K
                         ) ∧
                         (∀I2,K2,V2. (∀U. ⇧[|L2|-|L1|+i, 1] U ≡ T → ⊥) →
                                     ⇩[|L2|-|L1|+i] L2 ≡ K2.ⓑ{I2}V2 →
                                     ∧∧ I1 = I & V2 = V & K1 ⩖[T] L2 ≡ K
                         )
                      ) → L1 ⩖[T] L2 ≡ L.
#T #L2 #L1 #L #HL12 #HL1 #IH @lpx_sn_intro_alt // -HL1
#I1 #I #K1 #K #V1 #V #i #HLK1 #HLK
lapply (ldrop_fwd_length_minus4 … HLK1)
lapply (ldrop_fwd_length_le4 … HLK1)
normalize #HKL1 #H1i lapply (plus_minus_minus_be_aux … HL12 H1i) // #H2i
lapply (transitive_le … HKL1 HL12) -HKL1 -HL12 #HKL1
elim (IH … HLK1 HLK) -IH -HLK1 -HLK #IH1 #IH2
elim (is_lift_dec T (|L2|-|L1|+i) 1)
[ -IH2 * #U #HUT elim (IH1 … HUT) -IH1
  /3 width=2 by clor_sn, and3_intro/
| -IH1 #H elim (ldrop_O1_lt L2 (|L2|-|L1|+i)) /2 width=1 by monotonic_lt_minus_l/
  #I2 #K2 #V2 #HLK2 elim (IH2 … HLK2) -IH2
  /5 width=3 by clor_dx, ex_intro, and3_intro/
]
qed.

lemma llor_ind_alt: ∀T,L2. ∀S:relation lenv. (
                       ∀L1,L. |L1| = |L| → (
                          ∀I1,I,K1,K,V1,V,i.
                          ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L ≡ K.ⓑ{I}V →
                          (∃∃U. ⇧[|L2|-|L1|+i, 1] U ≡ T &
                                I1 = I & V1 = V & K1 ⩖[T] L2 ≡ K & S K1 K
                          ) ∨
                          (∃∃I2,K2,V2. (∀U. ⇧[|L2|-|L1|+i, 1] U ≡ T → ⊥) &
                                       ⇩[|L2|-|L1|+i] L2 ≡ K2.ⓑ{I2}V2 &
                                       I1 = I & V2 = V & K1 ⩖[T] L2 ≡ K & S K1 K
                          )
                       ) → |L1| ≤ |L2| → S L1 L
                    ) →
                    ∀L1,L. L1 ⩖[T] L2 ≡ L → |L1| ≤ |L2| → S L1 L.
#T #L2 #S #IH1 #L1 #L #H @(lpx_sn_ind_alt … H) -L1 -L
#L1 #L #HL1 #IH2 #HL12 @IH1 // -IH1 -HL1
#I1 #I #K1 #K #V1 #V #i #HLK1 #HLK
lapply (ldrop_fwd_length_minus4 … HLK1)
lapply (ldrop_fwd_length_le4 … HLK1)
normalize #HKL1 #H1i lapply (plus_minus_minus_be_aux … HL12 H1i) //
lapply (transitive_le … HKL1 HL12) -HKL1 -HL12
elim (IH2 … HLK1 HLK) -IH2 #H *
/5 width=5 by lt_to_le, ex6_3_intro, ex5_intro, or_intror, or_introl/
qed-.

lemma llor_inv_alt: ∀T,L2,L1,L. L1 ⩖[T] L2 ≡ L → |L1| ≤ |L2| →
                    |L1| = |L| ∧
                    (∀I1,I,K1,K,V1,V,i.
                       ⇩[i] L1 ≡ K1.ⓑ{I1}V1 → ⇩[i] L ≡ K.ⓑ{I}V →
                       (∃∃U. ⇧[|L2|-|L1|+i, 1] U ≡ T &
                             I1 = I & V1 = V & K1 ⩖[T] L2 ≡ K
                       ) ∨
                       (∃∃I2,K2,V2. (∀U. ⇧[|L2|-|L1|+i, 1] U ≡ T → ⊥) &
                                    ⇩[|L2|-|L1|+i] L2 ≡ K2.ⓑ{I2}V2 &
                                    I1 = I & V2 = V & K1 ⩖[T] L2 ≡ K
                       )
                    ).
#T #L2 #L1 #L #H #HL12 elim (lpx_sn_inv_alt … H) -H
#HL1 #IH @conj // -HL1
#I1 #I #K1 #K #V1 #V #i #HLK1 #HLK
lapply (ldrop_fwd_length_minus4 … HLK1)
lapply (ldrop_fwd_length_le4 … HLK1)
normalize #HKL1 #H1i lapply (plus_minus_minus_be_aux … HL12 H1i) //
lapply (transitive_le … HKL1 HL12) -HKL1 -HL12
elim (IH … HLK1 HLK) -IH #H *
/4 width=5 by ex5_3_intro, ex4_intro, or_intror, or_introl/
qed-.
