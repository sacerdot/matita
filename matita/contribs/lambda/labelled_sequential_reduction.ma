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

include "redex_pointer.ma".
include "multiplicity.ma".

(* LABELLED SEQUENTIAL REDUCTION (SINGLE STEP) ******************************)

(* Note: the application "(A B)" is represented by "@B.A" following:
         F. Kamareddine and R.P. Nederpelt: "A useful λ-notation".
         Theoretical Computer Science 155(1), Elsevier (1996), pp. 85-109.
*)
inductive lsred: rpointer → relation term ≝
| lsred_beta   : ∀A,D. lsred (◊) (@D.𝛌.A) ([⬐D]A)
| lsred_abst   : ∀p,A,C. lsred p A C → lsred p (𝛌.A) (𝛌.C) 
| lsred_appl_sn: ∀p,B,D,A. lsred p B D → lsred (true::p) (@B.A) (@D.A)
| lsred_appl_dx: ∀p,B,A,C. lsred p A C → lsred (false::p) (@B.A) (@B.C)
.

interpretation "labelled sequential reduction"
   'SeqRed M p N = (lsred p M N).

(* Note: we do not use → since it is reserved by CIC *)
notation "hvbox( M break ⇀ [ term 46 p ] break term 46 N )"
   non associative with precedence 45
   for @{ 'SeqRed $M $p $N }.

lemma lsred_inv_vref: ∀p,M,N. M ⇀[p] N → ∀i. #i = M → ⊥.
#p #M #N * -p -M -N
[ #A #D #i #H destruct
| #p #A #C #_ #i #H destruct
| #p #B #D #A #_ #i #H destruct
| #p #B #A #C #_ #i #H destruct
]
qed-.

lemma lsred_inv_beta: ∀p,M,N. M ⇀[p] N → ∀D,C. @D.C = M → ◊ = p →
                      ∃∃A. 𝛌.A = C & [⬐D] A = N.
#p #M #N * -p -M -N
[ #A #D #D0 #C0 #H #_ destruct /2 width=3/
| #p #A #C #_ #D0 #C0 #H destruct
| #p #B #D #A #_ #D0 #C0 #_ #H destruct
| #p #B #A #C #_ #D0 #C0 #_ #H destruct
]
qed-.

lemma lsred_inv_abst: ∀p,M,N. M ⇀[p] N → ∀A. 𝛌.A = M →
                      ∃∃C. A ⇀[p] C & 𝛌.C = N.
#p #M #N * -p -M -N
[ #A #D #A0 #H destruct
| #p #A #C #HAC #A0 #H destruct /2 width=3/
| #p #B #D #A #_ #A0 #H destruct
| #p #B #A #C #_ #A0 #H destruct
]
qed-.

lemma lsred_inv_appl_sn: ∀p,M,N. M ⇀[p] N → ∀B,A,q. @B.A = M → true::q = p →
                         ∃∃D. B ⇀[q] D & @D.A = N.
#p #M #N * -p -M -N
[ #A #D #B0 #A0 #p0 #_ #H destruct
| #p #A #C #_ #B0 #D0 #p0 #H destruct
| #p #B #D #A #HBD #B0 #A0 #p0 #H1 #H2 destruct /2 width=3/
| #p #B #A #C #_ #B0 #A0 #p0 #_ #H destruct
]
qed-.

lemma lsred_inv_appl_dx: ∀p,M,N. M ⇀[p] N → ∀B,A,q. @B.A = M → false::q = p →
                         ∃∃C. A ⇀[q] C & @B.C = N.
#p #M #N * -p -M -N
[ #A #D #B0 #A0 #p0 #_ #H destruct
| #p #A #C #_ #B0 #D0 #p0 #H destruct
| #p #B #D #A #_ #B0 #A0 #p0 #_ #H destruct
| #p #B #A #C #HAC #B0 #A0 #p0 #H1 #H2 destruct /2 width=3/
]
qed-.

lemma lsred_fwd_mult: ∀p,M,N. M ⇀[p] N → #{N} < #{M} * #{M}.
#p #M #N #H elim H -p -M -N
[ #A #D @(le_to_lt_to_lt … (#{A}*#{D})) //
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
#A #D #d <dsubst_lift_le //
qed.

lemma lsred_inv_lift: ∀p. deliftable (lsred p).
#p #h #N1 #N2 #H elim H -p -N1 -N2
[ #C #D #d #M1 #H
  elim (lift_inv_appl … H) -H #B #M #H0 #HM #H destruct
  elim (lift_inv_abst … HM) -HM #A #H0 #H destruct /3 width=3/
| #p #C1 #C2 #_ #IHC12 #d #M1 #H
  elim (lift_inv_abst … H) -H #A1 #H0 #H destruct
  elim (IHC12 ???) -IHC12 [4: // |2,3: skip ] #A2 #HA12 #H destruct (**) (* simplify line *)
  @(ex2_1_intro … (𝛌.A2)) // /2 width=1/
| #p #D1 #D2 #C1 #_ #IHD12 #d #M1 #H
  elim (lift_inv_appl … H) -H #B1 #A #H1 #H2 #H destruct
  elim (IHD12 ???) -IHD12 [4: // |2,3: skip ] #B2 #HB12 #H destruct (**) (* simplify line *)
  @(ex2_1_intro … (@B2.A)) // /2 width=1/
| #p #D1 #C1 #C2 #_ #IHC12 #d #M1 #H
  elim (lift_inv_appl … H) -H #B #A1 #H1 #H2 #H destruct
  elim (IHC12 ???) -IHC12 [4: // |2,3: skip ] #A2 #HA12 #H destruct (**) (* simplify line *)
  @(ex2_1_intro … (@B.A2)) // /2 width=1/
]
qed-.

lemma lsred_dsubst: ∀p. dsubstable_dx (lsred p).
#p #D1 #M1 #M2 #H elim H -p -M1 -M2 normalize /2 width=1/
#A #D2 #d >dsubst_dsubst_ge //
qed.

theorem lsred_mono: ∀p. singlevalued … (lsred p).
#p #M #N1 #H elim H -p -M -N1
[ #A #D #N2 #H elim (lsred_inv_beta … H ????) -H [4,5: // |2,3: skip ] #A0 #H1 #H2 destruct // (**) (* simplify line *)
| #p #A #C #_ #IHAC #N2 #H elim (lsred_inv_abst … H ??) -H [3: // |2: skip ] #C0 #HAC #H destruct /3 width=1/ (**) (* simplify line *)
| #p #B #D #A #_ #IHBD #N2 #H elim (lsred_inv_appl_sn … H ?????) -H [5,6: // |2,3,4: skip ] #D0 #HBD #H destruct /3 width=1/ (**) (* simplify line *)
| #p #B #A #C #_ #IHAC #N2 #H elim (lsred_inv_appl_dx … H ?????) -H [5,6: // |2,3,4: skip ] #C0 #HAC #H destruct /3 width=1/ (**) (* simplify line *)
]
qed-.
