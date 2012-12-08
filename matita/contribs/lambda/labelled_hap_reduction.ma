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

include "pointer_order.ma".
include "labelled_sequential_reduction.ma".

(* KASHIMA'S "HAP" COMPUTATION (LABELLED SINGLE STEP) ***********************)

(* Note: this is one step of the "head in application" computation of:
         R. Kashima: "A proof of the Standization Theorem in λ-Calculus". Typescript note, (2000).
*)
inductive lhap1: ptr → relation term ≝
| hap1_beta: ∀B,A. lhap1 (◊) (@B.𝛌.A) ([⬐B]A)
| hap1_appl: ∀p,B,A1,A2. lhap1 p A1 A2 → lhap1 (dx::p) (@B.A1) (@B.A2)
.

interpretation "labelled 'hap' reduction"
   'HAp M p N = (lhap1 p M N).

notation "hvbox( M break ⓗ⇀ [ term 46 p ] break term 46 N )"
   non associative with precedence 45
   for @{ 'HAp $M $p $N }.

lemma lhap1_inv_nil: ∀p,M,N. M ⓗ⇀[p] N → ◊ = p →
                     ∃∃B,A. @B.𝛌.A = M & [⬐B]A = N.
#p #M #N * -p -M -N
[ #B #A #_ /2 width=4/
| #p #B #A1 #A2 #_ #H destruct
]
qed-.

lemma lhap1_inv_cons: ∀p,M,N. M ⓗ⇀[p] N → ∀c,q. c::q = p →
                      ∃∃B,A1,A2. dx = c & A1 ⓗ⇀[q] A2 & @B.A1 = M & @B.A2 = N.
#p #M #N * -p -M -N
[ #B #A #c #q #H destruct
| #p #B #A1 #A2 #HA12 #c #q #H destruct /2 width=6/
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

lemma head_lsred_lhap1: ∀p. in_head p → ∀M,N. M ⇀[p] N → M ⓗ⇀[p] N.
#p #H @(in_head_ind … H) -p
[ #M #N #H elim (lsred_inv_nil … H ?) -H //
| #p #_ #IHp #M #N #H
  elim (lsred_inv_dx … H ??) -H [3: // |2: skip ] /3 width=1/ (**) (* simplify line *)
]
qed.

lemma lhap1_inv_head: ∀p,M,N. M ⓗ⇀[p] N → in_head p.
#p #M #N #H elim H -p -M -N // /2 width=1/
qed-.

lemma lhap1_inv_lsred: ∀p,M,N. M ⓗ⇀[p] N → M ⇀[p] N.
#p #M #N #H elim H -p -M -N // /2 width=1/
qed-.

theorem lhap1_mono: ∀p. singlevalued … (lhap1 p).
#p #M #N1 #H elim H -p -M -N1
[ #B #A #N2 #H
  elim (lhap1_inv_nil … H ?) -H // #D #C #H #HN2 destruct //
| #p #B #A1 #A2 #_ #IHA12 #N2 #H
  elim (lhap1_inv_cons … H ???) -H [4: // |2,3: skip ] (**) (* simplify line *)
  #D #C1 #C2 #_ #HC12 #H #HN2 destruct /3 width=1/
]
qed-.
