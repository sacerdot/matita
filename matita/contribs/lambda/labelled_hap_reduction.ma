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

include "labelled_sequential_reduction.ma".

(* KASHIMA'S "HAP" COMPUTATION (LABELLED SINGLE STEP) ***********************)

(* Note: this is one step of the "head in application" computation of:
         R. Kashima: "A proof of the Standization Theorem in λ-Calculus". Typescript note, (2000).
*)
inductive lhap1: rptr → relation term ≝
| hap1_beta: ∀B,A. lhap1 (◊) (@B.𝛌.A) ([⬐B]A)
| hap1_appl: ∀p,B,A1,A2. lhap1 p A1 A2 → lhap1 (false::p) (@B.A1) (@B.A2)
.

interpretation "labelled 'hap' reduction"
   'HAp M p N = (lhap1 p M N).

notation "hvbox( M break ⓗ⇀ [ term 46 p ] break term 46 N )"
   non associative with precedence 45
   for @{ 'HAp $M $p $N }.

lemma lhap1_inv_abst_sn: ∀p,M,N. M ⓗ⇀[p] N → ∀A. 𝛌.A = M → ⊥.
#p #M #N * -p -M -N
[ #B #A #A0 #H destruct
| #p #B #A1 #A2 #_ #A0 #H destruct
]
qed-.

lemma lhap1_inv_appl_sn: ∀p,M,N. M ⓗ⇀[p] N → ∀B,A. @B.A = M →
                         (∃∃C. ◊ = p & 𝛌.C = A & [⬐B]C = N) ∨
                         ∃∃q,C. A ⓗ⇀[q] C & false::q = p & @B.C = N.
#p #M #N * -p -M -N
[ #B #A #B0 #A0 #H destruct /3 width=3/
| #p #B #A1 #A2 #HA12 #B0 #A0 #H destruct /3 width=5/
]
qed-.

lemma lhap1_inv_abst_dx: ∀p,M,N. M ⓗ⇀[p] N → ∀C. 𝛌.C = N →
                         ∃∃B,A. ◊ = p & @B.𝛌.A = M & 𝛌.C = [⬐B]A.
#p #M #N * -p -M -N
[ #B #A #C #H /2 width=4/
| #p #B #A1 #A2 #_ #C #H destruct
]
qed-.

lemma lhap1_lift: ∀p. liftable (lhap1 p).
#p #h #M1 #M2 #H elim H -p -M1 -M2 normalize /2 width=1/
#B #A #d <dsubst_lift_le //
qed.

lemma lhap1_inv_lift: ∀p. deliftable_sn (lhap1 p).
#p #h #N1 #N2 #H elim H -p -N1 -N2
[ #D #C #d #M1 #H
  elim (lift_inv_appl … H) -H #B #M #H0 #HM #H destruct
  elim (lift_inv_abst … HM) -HM #A #H0 #H destruct /3 width=3/
| #p #D1 #C1 #C2 #_ #IHC12 #d #M1 #H
  elim (lift_inv_appl … H) -H #B #A1 #H1 #H2 #H destruct
  elim (IHC12 ???) -IHC12 [4: // |2,3: skip ] #A2 #HA12 #H destruct (**) (* simplify line *)
  @(ex2_intro … (@B.A2)) // /2 width=1/
]
qed-.

lemma lhap1_dsubst: ∀p. dsubstable_dx (lhap1 p).
#p #D1 #M1 #M2 #H elim H -p -M1 -M2 normalize /2 width=1/
#D2 #A #d >dsubst_dsubst_ge //
qed.

lemma lhap1_spine_fwd: ∀p,M,N. M ⓗ⇀[p] N → in_spine p.
#p #M #N #H elim H -p -M -N // /2 width=1/ 
qed-.

lemma lhap1_lsred_fwd: ∀p,M,N. M ⓗ⇀[p] N → M ⇀[p] N.
#p #M #N #H elim H -p -M -N // /2 width=1/
qed-.

lemma lhap1_le_fwd: ∀p1,M1,M. M1 ⓗ⇀[p1] M → ∀p2,M2. M ⓗ⇀[p2] M2 → p1 ≤ p2.
#p1 #M1 #M #H elim H -p1 -M1 -M //
#p1 #B #A1 #A2 #HA12 #IHA12 #p2 #M2 #H
elim (lhap1_inv_appl_sn … H ???) -H [5: // |2,3: skip ] * (**) (* simplify line *)
[ -IHA12 #C2 #Hp2 #HAC2 #_
  elim (lhap1_inv_abst_dx … HA12 … HAC2) -A2 #B1 #C1 #Hp1 #_ #_ //
| -HA12 /3 width=2/
]
qed-.
