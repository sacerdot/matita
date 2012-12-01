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

include "multiplicity.ma".

(* PARALLEL REDUCTION (SINGLE STEP) *****************************************)

(* Note: the application "(A B)" is represented by "@B.A"
         as for labelled sequential reduction
*)
inductive pred: relation term ≝
| pred_vref: ∀i. pred (#i) (#i)
| pred_abst: ∀A,C. pred A C → pred (𝛌.A) (𝛌.C) 
| pred_appl: ∀B,D,A,C. pred B D → pred A C → pred (@B.A) (@D.C)
| pred_beta: ∀B,D,A,C. pred B D → pred A C → pred (@B.𝛌.A) ([⬐D]C)
.

interpretation "parallel reduction"
    'ParRed M N = (pred M N).

notation "hvbox( M break ⥤ break term 46 N )"
   non associative with precedence 45
   for @{ 'ParRed $M $N }.

lemma pred_refl: reflexive … pred.
#M elim M -M // /2 width=1/
qed.

lemma pred_inv_vref: ∀M,N. M ⥤ N → ∀i. #i = M → #i = N.
#M #N * -M -N //
[ #A #C #_ #i #H destruct
| #B #D #A #C #_ #_ #i #H destruct
| #B #D #A #C #_ #_ #i #H destruct
]
qed-.

lemma pred_inv_abst: ∀M,N. M ⥤ N → ∀A. 𝛌.A = M →
                     ∃∃C. A ⥤ C & 𝛌.C = N.
#M #N * -M -N
[ #i #A0 #H destruct
| #A #C #HAC #A0 #H destruct /2 width=3/
| #B #D #A #C #_ #_ #A0 #H destruct
| #B #D #A #C #_ #_ #A0 #H destruct
]
qed-.

lemma pred_lift: liftable pred.
#h #M1 #M2 #H elim H -M1 -M2 normalize // /2 width=1/
#D #D #A #C #_ #_ #IHBD #IHAC #d <dsubst_lift_le // /2 width=1/
qed.

lemma pred_inv_lift: deliftable pred.
#h #N1 #N2 #H elim H -N1 -N2 /2 width=3/
[ #C1 #C2 #_ #IHC12 #d #M1 #H
  elim (lift_inv_abst … H) -H #A1 #HAC1 #H
  elim (IHC12 … HAC1) -C1 #A2 #HA12 #HAC2 destruct
  @(ex2_1_intro … (𝛌.A2)) // /2 width=1/
| #D1 #D2 #C1 #C2 #_ #_ #IHD12 #IHC12 #d #M1 #H
  elim (lift_inv_appl … H) -H #B1 #A1 #HBD1 #HAC1 #H
  elim (IHD12 … HBD1) -D1 #B2 #HB12 #HBD2
  elim (IHC12 … HAC1) -C1 #A2 #HA12 #HAC2 destruct
  @(ex2_1_intro … (@B2.A2)) // /2 width=1/
| #D1 #D2 #C1 #C2 #_ #_ #IHD12 #IHC12 #d #M1 #H
  elim (lift_inv_appl … H) -H #B1 #M #HBD1 #HM #H1
  elim (lift_inv_abst … HM) -HM #A1 #HAC1 #H
  elim (IHD12 … HBD1) -D1 #B2 #HB12 #HBD2
  elim (IHC12 … HAC1) -C1 #A2 #HA12 #HAC2 destruct
  @(ex2_1_intro … ([⬐B2]A2)) /2 width=1/
]
qed-.
