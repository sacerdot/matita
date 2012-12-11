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

include "pointer.ma".
include "multiplicity.ma".

(* LABELLED SEQUENTIAL REDUCTION (SINGLE STEP) ******************************)

(* Note: the application "(A B)" is represented by "@B.A" following:
         F. Kamareddine and R.P. Nederpelt: "A useful λ-notation".
         Theoretical Computer Science 155(1), Elsevier (1996), pp. 85-109.
*)
inductive lsred: ptr → relation term ≝
| lsred_beta   : ∀B,A. lsred (◊) (@B.𝛌.A) ([⬐B]A)
| lsred_abst   : ∀p,A1,A2. lsred p A1 A2 → lsred (sn::p) (𝛌.A1) (𝛌.A2) 
| lsred_appl_sn: ∀p,B1,B2,A. lsred p B1 B2 → lsred (sn::p) (@B1.A) (@B2.A)
| lsred_appl_dx: ∀p,B,A1,A2. lsred p A1 A2 → lsred (dx::p) (@B.A1) (@B.A2)
.

interpretation "labelled sequential reduction"
   'SeqRed M p N = (lsred p M N).

(* Note: we do not use → since it is reserved by CIC *)
notation "hvbox( M break ⇀ [ term 46 p ] break term 46 N )"
   non associative with precedence 45
   for @{ 'SeqRed $M $p $N }.

lemma lsred_inv_vref: ∀p,M,N. M ⇀[p] N → ∀i. #i = M → ⊥.
#p #M #N * -p -M -N
[ #B #A #i #H destruct
| #p #A1 #A2 #_ #i #H destruct
| #p #B1 #B2 #A #_ #i #H destruct
| #p #B #A1 #A2 #_ #i #H destruct
]
qed-.

lemma lsred_inv_nil: ∀p,M,N. M ⇀[p] N → ◊ = p →
                     ∃∃B,A. @B. 𝛌.A = M & [⬐B] A = N.
#p #M #N * -p -M -N
[ #B #A #_ destruct /2 width=4/
| #p #A1 #A2 #_ #H destruct
| #p #B1 #B2 #A #_ #H destruct
| #p #B #A1 #A2 #_ #H destruct
]
qed-.

lemma lsred_inv_sn: ∀p,M,N. M ⇀[p] N → ∀q. sn::q = p →
                    (∃∃A1,A2. A1 ⇀[q] A2 & 𝛌.A1 = M & 𝛌.A2 = N) ∨
                    ∃∃B1,B2,A. B1 ⇀[q] B2 & @B1.A = M & @B2.A = N.
#p #M #N * -p -M -N
[ #B #A #q #H destruct
| #p #A1 #A2 #HA12 #q #H destruct /3 width=5/
| #p #B1 #B2 #A #HB12 #q #H destruct /3 width=6/
| #p #B #A1 #A2 #_ #q #H destruct
]
qed-.

lemma lsred_inv_dx: ∀p,M,N. M ⇀[p] N → ∀q. dx::q = p →
                    ∃∃B,A1,A2. A1 ⇀[q] A2 & @B.A1 = M & @B.A2 = N.
#p #M #N * -p -M -N
[ #B #A #q #H destruct
| #p #A1 #A2 #_ #q #H destruct
| #p #B1 #B2 #A #_ #q #H destruct
| #p #B #A1 #A2 #HA12 #q #H destruct /2 width=6/
]
qed-.

lemma lsred_fwd_mult: ∀p,M,N. M ⇀[p] N → #{N} < #{M} * #{M}.
#p #M #N #H elim H -p -M -N
[ #B #A @(le_to_lt_to_lt … (#{A}*#{B})) //
  normalize /3 width=1 by lt_minus_to_plus_r, lt_times/ (**) (* auto: too slow without trace *) 
| //
| #p #B #D #A #_ #IHBD
  @(lt_to_le_to_lt … (#{B}*#{B}+#{A})) [ /2 width=1/ ] -D -p
| #p #B #A #C #_ #IHAC
  @(lt_to_le_to_lt … (#{B}+#{A}*#{A})) [ /2 width=1/ ] -C -p
]
@(transitive_le … (#{B}*#{B}+#{A}*#{A})) [ /2 width=1/ ]
>distributive_times_plus normalize /2 width=1/
qed-.

lemma lsred_lift: ∀p. liftable (lsred p).
#p #h #M1 #M2 #H elim H -p -M1 -M2 normalize /2 width=1/
#B #A #d <dsubst_lift_le //
qed.

lemma lsred_inv_lift: ∀p. deliftable_sn (lsred p).
#p #h #N1 #N2 #H elim H -p -N1 -N2
[ #D #C #d #M1 #H
  elim (lift_inv_appl … H) -H #B #M #H0 #HM #H destruct
  elim (lift_inv_abst … HM) -HM #A #H0 #H destruct /3 width=3/
| #p #C1 #C2 #_ #IHC12 #d #M1 #H
  elim (lift_inv_abst … H) -H #A1 #HAC1 #H
  elim (IHC12 … HAC1) -C1 #A2 #HA12 #HAC2 destruct
  @(ex2_intro … (𝛌.A2)) // /2 width=1/
| #p #D1 #D2 #C1 #_ #IHD12 #d #M1 #H
  elim (lift_inv_appl … H) -H #B1 #A #HBD1 #H1 #H2
  elim (IHD12 … HBD1) -D1 #B2 #HB12 #HBD2 destruct
  @(ex2_intro … (@B2.A)) // /2 width=1/
| #p #D1 #C1 #C2 #_ #IHC12 #d #M1 #H
  elim (lift_inv_appl … H) -H #B #A1 #H1 #HAC1 #H2
  elim (IHC12 … HAC1) -C1 #A2 #HA12 #HAC2 destruct
  @(ex2_intro … (@B.A2)) // /2 width=1/
]
qed-.

lemma lsred_dsubst: ∀p. dsubstable_dx (lsred p).
#p #D1 #M1 #M2 #H elim H -p -M1 -M2 normalize /2 width=1/
#D2 #A #d >dsubst_dsubst_ge //
qed.

theorem lsred_mono: ∀p. singlevalued … (lsred p).
#p #M #N1 #H elim H -p -M -N1
[ #B #A #N2 #H elim (lsred_inv_nil … H ?) -H // #D #C #H #HN2 destruct //
| #p #A1 #A2 #_ #IHA12 #N2 #H elim (lsred_inv_sn … H ??) -H [4: // |2: skip ] * (**) (* simplify line *)
  [ #C1 #C2 #HC12 #H #HN2 destruct /3 width=1/
  | #D1 #D2 #C #_ #H destruct
  ]
| #p #B1 #B2 #A #_ #IHB12 #N2 #H elim (lsred_inv_sn … H ??) -H [4: // |2: skip ] * (**) (* simplify line *)
  [ #C1 #C2 #_ #H destruct
  | #D1 #D2 #C #HD12 #H #HN2 destruct /3 width=1/
  ]
| #p #B #A1 #A2 #_ #IHA12 #N2 #H elim (lsred_inv_dx … H ??) -H [3: // |2: skip ] #D #C1 #C2 #HC12 #H #HN2 destruct /3 width=1/ (**) (* simplify line *)
]
qed-.
