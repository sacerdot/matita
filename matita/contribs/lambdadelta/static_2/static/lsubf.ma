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

include "ground/xoa/ex_3_3.ma".
include "ground/xoa/ex_4_3.ma".
include "ground/xoa/ex_5_5.ma".
include "ground/xoa/ex_5_6.ma".
include "ground/xoa/ex_6_5.ma".
include "ground/xoa/ex_7_6.ma".
include "static_2/notation/relations/lrsubeqf_4.ma".
include "ground/relocation/nstream_sor.ma".
include "static_2/static/frees.ma".

(* RESTRICTED REFINEMENT FOR CONTEXT-SENSITIVE FREE VARIABLES ***************)

inductive lsubf: relation4 lenv rtmap lenv rtmap ≝
| lsubf_atom: ∀f1,f2. f1 ≡ f2 → lsubf (⋆) f1 (⋆) f2
| lsubf_push: ∀f1,f2,I1,I2,L1,L2. lsubf L1 (f1) L2 (f2) →
              lsubf (L1.ⓘ[I1]) (⫯f1) (L2.ⓘ[I2]) (⫯f2)
| lsubf_bind: ∀f1,f2,I,L1,L2. lsubf L1 f1 L2 f2 →
              lsubf (L1.ⓘ[I]) (↑f1) (L2.ⓘ[I]) (↑f2)
| lsubf_beta: ∀f,f0,f1,f2,L1,L2,W,V. L1 ⊢ 𝐅+❪V❫ ≘ f → f0 ⋓ f ≘ f1 →
              lsubf L1 f0 L2 f2 → lsubf (L1.ⓓⓝW.V) (↑f1) (L2.ⓛW) (↑f2)
| lsubf_unit: ∀f,f0,f1,f2,I1,I2,L1,L2,V. L1 ⊢ 𝐅+❪V❫ ≘ f → f0 ⋓ f ≘ f1 →
              lsubf L1 f0 L2 f2 → lsubf (L1.ⓑ[I1]V) (↑f1) (L2.ⓤ[I2]) (↑f2)
.

interpretation
  "local environment refinement (context-sensitive free variables)"
  'LRSubEqF L1 f1 L2 f2 = (lsubf L1 f1 L2 f2).

(* Basic inversion lemmas ***************************************************)

fact lsubf_inv_atom1_aux:
     ∀f1,f2,L1,L2. ❪L1,f1❫ ⫃𝐅+ ❪L2,f2❫ → L1 = ⋆ →
     ∧∧ f1 ≡ f2 & L2 = ⋆.
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ /2 width=1 by conj/
| #f1 #f2 #I1 #I2 #L1 #L2 #_ #H destruct
| #f1 #f2 #I #L1 #L2 #_ #H destruct
| #f #f0 #f1 #f2 #L1 #L2 #W #V #_ #_ #_ #H destruct
| #f #f0 #f1 #f2 #I1 #I2 #L1 #L2 #V #_ #_ #_ #H destruct
]
qed-.

lemma lsubf_inv_atom1: ∀f1,f2,L2. ❪⋆,f1❫ ⫃𝐅+ ❪L2,f2❫ → ∧∧ f1 ≡ f2 & L2 = ⋆.
/2 width=3 by lsubf_inv_atom1_aux/ qed-.

fact lsubf_inv_push1_aux:
     ∀f1,f2,L1,L2. ❪L1,f1❫ ⫃𝐅+ ❪L2,f2❫ →
     ∀g1,I1,K1. f1 = ⫯g1 → L1 = K1.ⓘ[I1] →
     ∃∃g2,I2,K2. ❪K1,g1❫ ⫃𝐅+ ❪K2,g2❫ & f2 = ⫯g2 & L2 = K2.ⓘ[I2].
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ #f1 #f2 #_ #g1 #J1 #K1 #_ #H destruct
| #f1 #f2 #I1 #I2 #L1 #L2 #H12 #g1 #J1 #K1 #H1 #H2 destruct
  <(injective_push … H1) -g1 /2 width=6 by ex3_3_intro/
| #f1 #f2 #I #L1 #L2 #_ #g1 #J1 #K1 #H elim (discr_next_push … H)
| #f #f0 #f1 #f2 #L1 #L2 #W #V #_ #_ #_ #g1 #J1 #K1 #H elim (discr_next_push … H)
| #f #f0 #f1 #f2 #I1 #I2 #L1 #L2 #V #_ #_ #_ #g1 #J1 #K1 #H elim (discr_next_push … H)
]
qed-.

lemma lsubf_inv_push1:
      ∀g1,f2,I1,K1,L2. ❪K1.ⓘ[I1],⫯g1❫ ⫃𝐅+ ❪L2,f2❫ →
      ∃∃g2,I2,K2. ❪K1,g1❫ ⫃𝐅+ ❪K2,g2❫ & f2 = ⫯g2 & L2 = K2.ⓘ[I2].
/2 width=6 by lsubf_inv_push1_aux/ qed-.

fact lsubf_inv_pair1_aux:
     ∀f1,f2,L1,L2. ❪L1,f1❫ ⫃𝐅+ ❪L2,f2❫ →
     ∀g1,I,K1,X. f1 = ↑g1 → L1 = K1.ⓑ[I]X →
     ∨∨ ∃∃g2,K2. ❪K1,g1❫ ⫃𝐅+ ❪K2,g2❫ & f2 = ↑g2 & L2 = K2.ⓑ[I]X
      | ∃∃g,g0,g2,K2,W,V. ❪K1,g0❫ ⫃𝐅+ ❪K2,g2❫ &
          K1 ⊢ 𝐅+❪V❫ ≘ g & g0 ⋓ g ≘ g1 & f2 = ↑g2 &
          I = Abbr & X = ⓝW.V & L2 = K2.ⓛW
      | ∃∃g,g0,g2,J,K2. ❪K1,g0❫ ⫃𝐅+ ❪K2,g2❫ &
          K1 ⊢ 𝐅+❪X❫ ≘ g & g0 ⋓ g ≘ g1 & f2 = ↑g2 & L2 = K2.ⓤ[J].
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ #f1 #f2 #_ #g1 #J #K1 #X #_ #H destruct
| #f1 #f2 #I1 #I2 #L1 #L2 #H12 #g1 #J #K1 #X #H elim (discr_push_next … H)
| #f1 #f2 #I #L1 #L2 #H12 #g1 #J #K1 #X #H1 #H2 destruct
  <(injective_next … H1) -g1 /3 width=5 by or3_intro0, ex3_2_intro/
| #f #f0 #f1 #f2 #L1 #L2 #W #V #Hf #Hf1 #H12 #g1 #J #K1 #X #H1 #H2 destruct
  <(injective_next … H1) -g1 /3 width=12 by or3_intro1, ex7_6_intro/
| #f #f0 #f1 #f2 #I1 #I2 #L1 #L2 #V #Hf #Hf1 #H12 #g1 #J #K1 #X #H1 #H2 destruct
  <(injective_next … H1) -g1 /3 width=10 by or3_intro2, ex5_5_intro/
]
qed-.

lemma lsubf_inv_pair1:
      ∀g1,f2,I,K1,L2,X. ❪K1.ⓑ[I]X,↑g1❫ ⫃𝐅+ ❪L2,f2❫ →
      ∨∨ ∃∃g2,K2. ❪K1,g1❫ ⫃𝐅+ ❪K2,g2❫ & f2 = ↑g2 & L2 = K2.ⓑ[I]X
       | ∃∃g,g0,g2,K2,W,V. ❪K1,g0❫ ⫃𝐅+ ❪K2,g2❫ &
           K1 ⊢ 𝐅+❪V❫ ≘ g & g0 ⋓ g ≘ g1 & f2 = ↑g2 &
           I = Abbr & X = ⓝW.V & L2 = K2.ⓛW
       | ∃∃g,g0,g2,J,K2. ❪K1,g0❫ ⫃𝐅+ ❪K2,g2❫ &
           K1 ⊢ 𝐅+❪X❫ ≘ g & g0 ⋓ g ≘ g1 & f2 = ↑g2 & L2 = K2.ⓤ[J].
/2 width=5 by lsubf_inv_pair1_aux/ qed-.

fact lsubf_inv_unit1_aux:
     ∀f1,f2,L1,L2. ❪L1,f1❫ ⫃𝐅+ ❪L2,f2❫ →
     ∀g1,I,K1. f1 = ↑g1 → L1 = K1.ⓤ[I] →
     ∃∃g2,K2. ❪K1,g1❫ ⫃𝐅+ ❪K2,g2❫ & f2 = ↑g2 & L2 = K2.ⓤ[I].
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ #f1 #f2 #_ #g1 #J #K1 #_ #H destruct
| #f1 #f2 #I1 #I2 #L1 #L2 #H12 #g1 #J #K1 #H elim (discr_push_next … H)
| #f1 #f2 #I #L1 #L2 #H12 #g1 #J #K1 #H1 #H2 destruct
  <(injective_next … H1) -g1 /2 width=5 by ex3_2_intro/
| #f #f0 #f1 #f2 #L1 #L2 #W #V #_ #_ #_ #g1 #J #K1 #_ #H destruct
| #f #f0 #f1 #f2 #I1 #I2 #L1 #L2 #V #_ #_ #_ #g1 #J #K1 #_ #H destruct
]
qed-.

lemma lsubf_inv_unit1:
      ∀g1,f2,I,K1,L2. ❪K1.ⓤ[I],↑g1❫ ⫃𝐅+ ❪L2,f2❫ →
      ∃∃g2,K2. ❪K1,g1❫ ⫃𝐅+ ❪K2,g2❫ & f2 = ↑g2 & L2 = K2.ⓤ[I].
/2 width=5 by lsubf_inv_unit1_aux/ qed-.

fact lsubf_inv_atom2_aux:
     ∀f1,f2,L1,L2. ❪L1,f1❫ ⫃𝐅+ ❪L2,f2❫ → L2 = ⋆ →
     ∧∧ f1 ≡ f2 & L1 = ⋆.
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ /2 width=1 by conj/
| #f1 #f2 #I1 #I2 #L1 #L2 #_ #H destruct
| #f1 #f2 #I #L1 #L2 #_ #H destruct
| #f #f0 #f1 #f2 #L1 #L2 #W #V #_ #_ #_ #H destruct
| #f #f0 #f1 #f2 #I1 #I2 #L1 #L2 #V #_ #_ #_ #H destruct
]
qed-.

lemma lsubf_inv_atom2: ∀f1,f2,L1. ❪L1,f1❫ ⫃𝐅+ ❪⋆,f2❫ → ∧∧f1 ≡ f2 & L1 = ⋆.
/2 width=3 by lsubf_inv_atom2_aux/ qed-.

fact lsubf_inv_push2_aux:
     ∀f1,f2,L1,L2. ❪L1,f1❫ ⫃𝐅+ ❪L2,f2❫ →
     ∀g2,I2,K2. f2 = ⫯g2 → L2 = K2.ⓘ[I2] →
     ∃∃g1,I1,K1. ❪K1,g1❫ ⫃𝐅+ ❪K2,g2❫ & f1 = ⫯g1 & L1 = K1.ⓘ[I1].
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ #f1 #f2 #_ #g2 #J2 #K2 #_ #H destruct
| #f1 #f2 #I1 #I2 #L1 #L2 #H12 #g2 #J2 #K2 #H1 #H2 destruct
  <(injective_push … H1) -g2 /2 width=6 by ex3_3_intro/
| #f1 #f2 #I #L1 #L2 #_ #g2 #J2 #K2 #H elim (discr_next_push … H)
| #f #f0 #f1 #f2 #L1 #L2 #W #V #_ #_ #_ #g2 #J2 #K2 #H elim (discr_next_push … H)
| #f #f0 #f1 #f2 #I1 #I2 #L1 #L2 #V #_ #_ #_ #g2 #J2 #K2 #H elim (discr_next_push … H)
]
qed-.

lemma lsubf_inv_push2:
      ∀f1,g2,I2,L1,K2. ❪L1,f1❫ ⫃𝐅+ ❪K2.ⓘ[I2],⫯g2❫ →
      ∃∃g1,I1,K1. ❪K1,g1❫ ⫃𝐅+ ❪K2,g2❫ & f1 = ⫯g1 & L1 = K1.ⓘ[I1].
/2 width=6 by lsubf_inv_push2_aux/ qed-.

fact lsubf_inv_pair2_aux:
     ∀f1,f2,L1,L2. ❪L1,f1❫ ⫃𝐅+ ❪L2,f2❫ →
     ∀g2,I,K2,W. f2 = ↑g2 → L2 = K2.ⓑ[I]W →
     ∨∨ ∃∃g1,K1. ❪K1,g1❫ ⫃𝐅+ ❪K2,g2❫ & f1 = ↑g1 & L1 = K1.ⓑ[I]W
      | ∃∃g,g0,g1,K1,V. ❪K1,g0❫ ⫃𝐅+ ❪K2,g2❫ &
          K1 ⊢ 𝐅+❪V❫ ≘ g & g0 ⋓ g ≘ g1 & f1 = ↑g1 &
          I = Abst & L1 = K1.ⓓⓝW.V.
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ #f1 #f2 #_ #g2 #J #K2 #X #_ #H destruct
| #f1 #f2 #I1 #I2 #L1 #L2 #H12 #g2 #J #K2 #X #H elim (discr_push_next … H)
| #f1 #f2 #I #L1 #L2 #H12 #g2 #J #K2 #X #H1 #H2 destruct
  <(injective_next … H1) -g2 /3 width=5 by ex3_2_intro, or_introl/
| #f #f0 #f1 #f2 #L1 #L2 #W #V #Hf #Hf1 #H12 #g2 #J #K2 #X #H1 #H2 destruct
  <(injective_next … H1) -g2 /3 width=10 by ex6_5_intro, or_intror/
| #f #f0 #f1 #f2 #I1 #I2 #L1 #L2 #V #_ #_ #_ #g2 #J #K2 #X #_ #H destruct
]
qed-.

lemma lsubf_inv_pair2:
      ∀f1,g2,I,L1,K2,W. ❪L1,f1❫ ⫃𝐅+ ❪K2.ⓑ[I]W,↑g2❫ →
      ∨∨ ∃∃g1,K1. ❪K1,g1❫ ⫃𝐅+ ❪K2,g2❫ & f1 = ↑g1 & L1 = K1.ⓑ[I]W
       | ∃∃g,g0,g1,K1,V. ❪K1,g0❫ ⫃𝐅+ ❪K2,g2❫ &
           K1 ⊢ 𝐅+❪V❫ ≘ g & g0 ⋓ g ≘ g1 & f1 = ↑g1 &
           I = Abst & L1 = K1.ⓓⓝW.V.
/2 width=5 by lsubf_inv_pair2_aux/ qed-.

fact lsubf_inv_unit2_aux:
     ∀f1,f2,L1,L2. ❪L1,f1❫ ⫃𝐅+ ❪L2,f2❫ →
     ∀g2,I,K2. f2 = ↑g2 → L2 = K2.ⓤ[I] →
     ∨∨ ∃∃g1,K1. ❪K1,g1❫ ⫃𝐅+ ❪K2,g2❫ & f1 = ↑g1 & L1 = K1.ⓤ[I]
      | ∃∃g,g0,g1,J,K1,V. ❪K1,g0❫ ⫃𝐅+ ❪K2,g2❫ &
          K1 ⊢ 𝐅+❪V❫ ≘ g & g0 ⋓ g ≘ g1 & f1 = ↑g1 & L1 = K1.ⓑ[J]V.
#f1 #f2 #L1 #L2 * -f1 -f2 -L1 -L2
[ #f1 #f2 #_ #g2 #J #K2 #_ #H destruct
| #f1 #f2 #I1 #I2 #L1 #L2 #H12 #g2 #J #K2 #H elim (discr_push_next … H)
| #f1 #f2 #I #L1 #L2 #H12 #g2 #J #K2 #H1 #H2 destruct
  <(injective_next … H1) -g2 /3 width=5 by ex3_2_intro, or_introl/
| #f #f0 #f1 #f2 #L1 #L2 #W #V #_ #_ #_ #g2 #J #K2 #_ #H destruct
| #f #f0 #f1 #f2 #I1 #I2 #L1 #L2 #V #Hf #Hf1 #H12 #g2 #J #K2 #H1 #H2 destruct
  <(injective_next … H1) -g2 /3 width=11 by ex5_6_intro, or_intror/
]
qed-.

lemma lsubf_inv_unit2:
      ∀f1,g2,I,L1,K2. ❪L1,f1❫ ⫃𝐅+ ❪K2.ⓤ[I],↑g2❫ →
      ∨∨ ∃∃g1,K1. ❪K1,g1❫ ⫃𝐅+ ❪K2,g2❫ & f1 = ↑g1 & L1 = K1.ⓤ[I]
       | ∃∃g,g0,g1,J,K1,V. ❪K1,g0❫ ⫃𝐅+ ❪K2,g2❫ &
           K1 ⊢ 𝐅+❪V❫ ≘ g & g0 ⋓ g ≘ g1 & f1 = ↑g1 & L1 = K1.ⓑ[J]V.
/2 width=5 by lsubf_inv_unit2_aux/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma lsubf_inv_atom: ∀f1,f2. ❪⋆,f1❫ ⫃𝐅+ ❪⋆,f2❫ → f1 ≡ f2.
#f1 #f2 #H elim (lsubf_inv_atom1 … H) -H //
qed-.

lemma lsubf_inv_push_sn:
      ∀g1,f2,I1,I2,K1,K2. ❪K1.ⓘ[I1],⫯g1❫ ⫃𝐅+ ❪K2.ⓘ[I2],f2❫ →
      ∃∃g2. ❪K1,g1❫ ⫃𝐅+ ❪K2,g2❫ & f2 = ⫯g2.
#g1 #f2 #I #K1 #K2 #X #H elim (lsubf_inv_push1 … H) -H
#g2 #I #Y #H0 #H2 #H destruct /2 width=3 by ex2_intro/
qed-.

lemma lsubf_inv_bind_sn:
      ∀g1,f2,I,K1,K2. ❪K1.ⓘ[I],↑g1❫ ⫃𝐅+ ❪K2.ⓘ[I],f2❫ →
      ∃∃g2. ❪K1,g1❫ ⫃𝐅+ ❪K2,g2❫ & f2 = ↑g2.
#g1 #f2 * #I [2: #X ] #K1 #K2 #H
[ elim (lsubf_inv_pair1 … H) -H *
  [ #z2 #Y2 #H2 #H #H0 destruct /2 width=3 by ex2_intro/
  | #z #z0 #z2 #Y2 #W #V #_ #_ #_ #_ #H0 #_ #H destruct
  | #z #z0 #z2 #Z2 #Y2 #_ #_ #_ #_ #H destruct
  ]
| elim (lsubf_inv_unit1 … H) -H
  #z2 #Y2 #H2 #H #H0 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma lsubf_inv_beta_sn:
      ∀g1,f2,K1,K2,V,W. ❪K1.ⓓⓝW.V,↑g1❫ ⫃𝐅+ ❪K2.ⓛW,f2❫ →
      ∃∃g,g0,g2. ❪K1,g0❫ ⫃𝐅+ ❪K2,g2❫ & K1 ⊢ 𝐅+❪V❫ ≘ g & g0 ⋓ g ≘ g1 & f2 = ↑g2.
#g1 #f2 #K1 #K2 #V #W #H elim (lsubf_inv_pair1 … H) -H *
[ #z2 #Y2 #_ #_ #H destruct
| #z #z0 #z2 #Y2 #X0 #X #H02 #Hz #Hg1 #H #_ #H0 #H1 destruct
  /2 width=7 by ex4_3_intro/
| #z #z0 #z2 #Z2 #Y2 #_ #_ #_ #_ #H destruct
]
qed-.

lemma lsubf_inv_unit_sn:
      ∀g1,f2,I,J,K1,K2,V. ❪K1.ⓑ[I]V,↑g1❫ ⫃𝐅+ ❪K2.ⓤ[J],f2❫ →
      ∃∃g,g0,g2. ❪K1,g0❫ ⫃𝐅+ ❪K2,g2❫ & K1 ⊢ 𝐅+❪V❫ ≘ g & g0 ⋓ g ≘ g1 & f2 = ↑g2.
#g1 #f2 #I #J #K1 #K2 #V #H elim (lsubf_inv_pair1 … H) -H *
[ #z2 #Y2 #_ #_ #H destruct
| #z #z0 #z2 #Y2 #X0 #X #_ #_ #_ #_ #_ #_ #H destruct
| #z #z0 #z2 #Z2 #Y2 #H02 #Hz #Hg1 #H0 #H1 destruct
  /2 width=7 by ex4_3_intro/
]
qed-.

lemma lsubf_inv_refl: ∀L,f1,f2. ❪L,f1❫ ⫃𝐅+ ❪L,f2❫ → f1 ≡ f2.
#L elim L -L /2 width=1 by lsubf_inv_atom/
#L #I #IH #f1 #f2 #H12
elim (pn_split f1) * #g1 #H destruct
[ elim (lsubf_inv_push_sn … H12) | elim (lsubf_inv_bind_sn … H12) ] -H12
#g2 #H12 #H destruct /3 width=5 by eq_next, eq_push/
qed-.

(* Basic forward lemmas *****************************************************)

lemma lsubf_fwd_bind_tl:
      ∀f1,f2,I,L1,L2. ❪L1.ⓘ[I],f1❫ ⫃𝐅+ ❪L2.ⓘ[I],f2❫ → ❪L1,⫰f1❫ ⫃𝐅+ ❪L2,⫰f2❫.
#f1 #f2 #I #L1 #L2 #H
elim (pn_split f1) * #g1 #H0 destruct
[ elim (lsubf_inv_push_sn … H) | elim (lsubf_inv_bind_sn … H) ] -H
#g2 #H12 #H destruct //
qed-.

lemma lsubf_fwd_isid_dx: ∀f1,f2,L1,L2. ❪L1,f1❫ ⫃𝐅+ ❪L2,f2❫ → 𝐈❪f2❫ → 𝐈❪f1❫.
#f1 #f2 #L1 #L2 #H elim H -f1 -f2 -L1 -L2
[ /2 width=3 by isid_eq_repl_fwd/
| /4 width=3 by isid_inv_push, isid_push/
| #f1 #f2 #I #L1 #L2 #_ #_ #H elim (isid_inv_next … H) -H //
| #f #f0 #f1 #f2 #L1 #L2 #W #V #_ #_ #_ #_ #H elim (isid_inv_next … H) -H //
| #f #f0 #f1 #f2 #I1 #I2 #L1 #L2 #V #_ #_ #_ #_ #H elim (isid_inv_next … H) -H //
]
qed-.

lemma lsubf_fwd_isid_sn: ∀f1,f2,L1,L2. ❪L1,f1❫ ⫃𝐅+ ❪L2,f2❫ → 𝐈❪f1❫ → 𝐈❪f2❫.
#f1 #f2 #L1 #L2 #H elim H -f1 -f2 -L1 -L2
[ /2 width=3 by isid_eq_repl_back/
| /4 width=3 by isid_inv_push, isid_push/
| #f1 #f2 #I #L1 #L2 #_ #_ #H elim (isid_inv_next … H) -H //
| #f #f0 #f1 #f2 #L1 #L2 #W #V #_ #_ #_ #_ #H elim (isid_inv_next … H) -H //
| #f #f0 #f1 #f2 #I1 #I2 #L1 #L2 #V #_ #_ #_ #_ #H elim (isid_inv_next … H) -H //
]
qed-.

lemma lsubf_fwd_sle: ∀f1,f2,L1,L2. ❪L1,f1❫ ⫃𝐅+ ❪L2,f2❫ → f2 ⊆ f1.
#f1 #f2 #L1 #L2 #H elim H -f1 -f2 -L1 -L2
/3 width=5 by sor_inv_sle_sn_trans, sle_next, sle_push, sle_refl_eq, eq_sym/
qed-.

(* Basic properties *********************************************************)

lemma lsubf_eq_repl_back1: ∀f2,L1,L2. eq_repl_back … (λf1. ❪L1,f1❫ ⫃𝐅+ ❪L2,f2❫).
#f2 #L1 #L2 #f #H elim H -f -f2 -L1 -L2
[ #f1 #f2 #Hf12 #g1 #Hfg1
  /3 width=3 by lsubf_atom, eq_canc_sn/
| #f1 #f2 #I1 #I2 #K1 #K2 #_ #IH #g #H
  elim (eq_inv_px … H) -H [|*: // ] #g1 #Hfg1 #H destruct
  /3 width=1 by lsubf_push/
| #f1 #f2 #I #K1 #K2 #_ #IH #g #H
  elim (eq_inv_nx … H) -H [|*: // ] #g1 #Hfg1 #H destruct
  /3 width=1 by lsubf_bind/
| #f #f0 #f1 #f2 #K1 #L2 #W #V #Hf #Hf1 #_ #IH #g #H
  elim (eq_inv_nx … H) -H [|*: // ] #g1 #Hfg1 #H destruct
  /3 width=5 by lsubf_beta, sor_eq_repl_back3/
| #f #f0 #f1 #f2 #I1 #I2 #K1 #K2 #V #Hf #Hf1 #_ #IH #g #H
  elim (eq_inv_nx … H) -H [|*: // ] #g1 #Hfg1 #H destruct
  /3 width=5 by lsubf_unit, sor_eq_repl_back3/
]
qed-.

lemma lsubf_eq_repl_fwd1: ∀f2,L1,L2. eq_repl_fwd … (λf1. ❪L1,f1❫ ⫃𝐅+ ❪L2,f2❫).
#f2 #L1 #L2 @eq_repl_sym /2 width=3 by lsubf_eq_repl_back1/
qed-.

lemma lsubf_eq_repl_back2: ∀f1,L1,L2. eq_repl_back … (λf2. ❪L1,f1❫ ⫃𝐅+ ❪L2,f2❫).
#f1 #L1 #L2 #f #H elim H -f1 -f -L1 -L2
[ #f1 #f2 #Hf12 #g2 #Hfg2
  /3 width=3 by lsubf_atom, eq_trans/
| #f1 #f2 #I1 #I2 #K1 #K2 #_ #IH #g #H
  elim (eq_inv_px … H) -H [|*: // ] #g2 #Hfg2 #H destruct
  /3 width=1 by lsubf_push/
| #f1 #f2 #I #K1 #K2 #_ #IH #g #H
  elim (eq_inv_nx … H) -H [|*: // ] #g2 #Hfg2 #H destruct
  /3 width=1 by lsubf_bind/
| #f #f0 #f1 #f2 #K1 #L2 #W #V #Hf #Hf1 #_ #IH #g #H
  elim (eq_inv_nx … H) -H [|*: // ] #g2 #Hfg2 #H destruct
  /3 width=5 by lsubf_beta/
| #f #f0 #f1 #f2 #I1 #I2 #K1 #K2 #V #Hf #Hf1 #_ #IH #g #H
  elim (eq_inv_nx … H) -H [|*: // ] #g2 #Hfg2 #H destruct
  /3 width=5 by lsubf_unit/
]
qed-.

lemma lsubf_eq_repl_fwd2: ∀f1,L1,L2. eq_repl_fwd … (λf2. ❪L1,f1❫ ⫃𝐅+ ❪L2,f2❫).
#f1 #L1 #L2 @eq_repl_sym /2 width=3 by lsubf_eq_repl_back2/
qed-.

lemma lsubf_refl: bi_reflexive … lsubf.
#L elim L -L /2 width=1 by lsubf_atom, eq_refl/
#L #I #IH #f elim (pn_split f) * #g #H destruct
/2 width=1 by lsubf_push, lsubf_bind/
qed.

lemma lsubf_refl_eq: ∀f1,f2,L. f1 ≡ f2 → ❪L,f1❫ ⫃𝐅+ ❪L,f2❫.
/2 width=3 by lsubf_eq_repl_back2/ qed.

lemma lsubf_bind_tl_dx:
      ∀g1,f2,I,L1,L2. ❪L1,g1❫ ⫃𝐅+ ❪L2,⫰f2❫ →
      ∃∃f1. ❪L1.ⓘ[I],f1❫ ⫃𝐅+ ❪L2.ⓘ[I],f2❫ & g1 = ⫰f1.
#g1 #f2 #I #L1 #L2 #H
elim (pn_split f2) * #g2 #H2 destruct
@ex2_intro [1,2,4,5: /2 width=2 by lsubf_push, lsubf_bind/ ] // (**) (* constructor needed *)
qed-.

lemma lsubf_beta_tl_dx:
      ∀f,f0,g1,L1,V. L1 ⊢ 𝐅+❪V❫ ≘ f → f0 ⋓ f ≘ g1 →
      ∀f2,L2,W. ❪L1,f0❫ ⫃𝐅+ ❪L2,⫰f2❫ →
      ∃∃f1. ❪L1.ⓓⓝW.V,f1❫ ⫃𝐅+ ❪L2.ⓛW,f2❫ & ⫰f1 ⊆ g1.
#f #f0 #g1 #L1 #V #Hf #Hg1 #f2
elim (pn_split f2) * #x2 #H2 #L2 #W #HL12 destruct
[ /3 width=4 by lsubf_push, sor_inv_sle_sn, ex2_intro/
| @(ex2_intro … (↑g1)) /2 width=5 by lsubf_beta/ (**) (* full auto fails *)
]
qed-.

(* Note: this might be moved *)
lemma lsubf_inv_sor_dx:
      ∀f1,f2,L1,L2. ❪L1,f1❫ ⫃𝐅+ ❪L2,f2❫ →
      ∀f2l,f2r. f2l⋓f2r ≘ f2 →
      ∃∃f1l,f1r. ❪L1,f1l❫ ⫃𝐅+ ❪L2,f2l❫ & ❪L1,f1r❫ ⫃𝐅+ ❪L2,f2r❫ & f1l⋓f1r ≘ f1.
#f1 #f2 #L1 #L2 #H elim H -f1 -f2 -L1 -L2
[ /3 width=7 by sor_eq_repl_fwd3, ex3_2_intro/
| #g1 #g2 #I1 #I2 #L1 #L2 #_ #IH #f2l #f2r #H
  elim (sor_inv_xxp … H) -H [|*: // ] #g2l #g2r #Hg2 #Hl #Hr destruct
  elim (IH … Hg2) -g2 /3 width=11 by lsubf_push, sor_pp, ex3_2_intro/
| #g1 #g2 #I #L1 #L2 #_ #IH #f2l #f2r #H
  elim (sor_inv_xxn … H) -H [1,3,4: * |*: // ] #g2l #g2r #Hg2 #Hl #Hr destruct
  elim (IH … Hg2) -g2 /3 width=11 by lsubf_push, lsubf_bind, sor_np, sor_pn, sor_nn, ex3_2_intro/
| #g #g0 #g1 #g2 #L1 #L2 #W #V #Hg #Hg1 #_ #IH #f2l #f2r #H
  elim (sor_inv_xxn … H) -H [1,3,4: * |*: // ] #g2l #g2r #Hg2 #Hl #Hr destruct
  elim (IH … Hg2) -g2 #g1l #g1r #Hl #Hr #Hg0
  [ lapply (sor_comm_23 … Hg0 Hg1 ?) -g0 [3: |*: // ] #Hg1
    /3 width=11 by lsubf_push, lsubf_beta, sor_np, ex3_2_intro/
  | lapply (sor_assoc_dx … Hg1 … Hg0 ??) -g0 [3: |*: // ] #Hg1
    /3 width=11 by lsubf_push, lsubf_beta, sor_pn, ex3_2_intro/
  | lapply (sor_distr_dx … Hg0 … Hg1) -g0 [5: |*: // ] #Hg1
    /3 width=11 by lsubf_beta, sor_nn, ex3_2_intro/
  ]
| #g #g0 #g1 #g2 #I1 #I2 #L1 #L2 #V #Hg #Hg1 #_ #IH #f2l #f2r #H
  elim (sor_inv_xxn … H) -H [1,3,4: * |*: // ] #g2l #g2r #Hg2 #Hl #Hr destruct
  elim (IH … Hg2) -g2 #g1l #g1r #Hl #Hr #Hg0
  [ lapply (sor_comm_23 … Hg0 Hg1 ?) -g0 [3: |*: // ] #Hg1
    /3 width=11 by lsubf_push, lsubf_unit, sor_np, ex3_2_intro/
  | lapply (sor_assoc_dx … Hg1 … Hg0 ??) -g0 [3: |*: // ] #Hg1
    /3 width=11 by lsubf_push, lsubf_unit, sor_pn, ex3_2_intro/
  | lapply (sor_distr_dx … Hg0 … Hg1) -g0 [5: |*: // ] #Hg1
    /3 width=11 by lsubf_unit, sor_nn, ex3_2_intro/
  ]
]
qed-.
