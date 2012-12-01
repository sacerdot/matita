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

include "redex_pointer_sequence.ma".
include "labelled_sequential_reduction.ma".

(* LABELLED SEQUENTIAL COMPUTATION (MULTISTEP) ******************************)

(* Note: this comes from "star term lsred" *)
inductive lsreds: rpseq → relation term ≝
| lsreds_nil : ∀M. lsreds (◊) M M
| lsreds_cons: ∀p,M1,M. M1 ⇀[p] M →
               ∀s,M2. lsreds s M M2 → lsreds (p::s) M1 M2
.

interpretation "labelled sequential computation"
   'SeqRedStar M s N = (lsreds s M N).

notation "hvbox( M break ⇀* [ term 46 s ] break term 46 N )"
   non associative with precedence 45
   for @{ 'SeqRedStar $M $s $N }.

lemma lsred_lsreds: ∀p,M1,M2. M1 ⇀[p] M2 → M1 ⇀*[p::◊] M2.
/2 width=3/
qed.

lemma lsreds_inv_nil: ∀s,M1,M2. M1 ⇀*[s] M2 → ◊ = s → M1 = M2.
#s #M1 #M2 * -s -M1 -M2 //
#p #M1 #M #_ #s #M2 #_ #H destruct
qed-.

lemma lsreds_inv_cons: ∀s,M1,M2. M1 ⇀*[s] M2 → ∀q,r. q::r = s →
                       ∃∃M. M1 ⇀[q] M & M ⇀*[r] M2.
#s #M1 #M2 * -s -M1 -M2
[ #M #q #r #H destruct 
| #p #M1 #M #HM1 #s #M2 #HM2 #q #r #H destruct /2 width=3/
]
qed-.

lemma lsreds_inv_lsred: ∀p,M1,M2. M1 ⇀*[p::◊] M2 → M1 ⇀[p] M2.
#p #M1 #M2 #H
elim (lsreds_inv_cons … H ???) -H [4: // |2,3: skip ] #M #HM1 #H (**) (* simplify line *)
<(lsreds_inv_nil … H ?) -H //
qed-.

(* Note: "|s|" should be unparetesized *)
lemma lsreds_fwd_mult: ∀s,M1,M2. M1 ⇀*[s] M2 → #{M2} ≤ #{M1} ^ (2 ^ (|s|)).
#s #M1 #M2 #H elim H -s -M1 -M2 normalize //
#p #M1 #M #HM1 #s #M2 #_ #IHM2
lapply (lsred_fwd_mult … HM1) -p #HM1
@(transitive_le … IHM2) -M2
/3 width=1 by le_exp1, lt_O_exp, lt_to_le/ (**) (* auto: slow without trace *)
qed-.

lemma lsreds_lift: ∀s. liftable (lsreds s).
#s #h #M1 #M2 #H elim H -s -M1 -M2 // /3 width=3/
qed.

lemma lsreds_inv_lift: ∀s. deliftable (lsreds s).
#s #h #N1 #N2 #H elim H -s -N1 -N2 /2 width=3/
#p #N1 #N #HN1 #s #N2 #_ #IHN2 #d #M1 #HMN1
elim (lsred_inv_lift … HN1 … HMN1) -N1 #M #HM1 #HMN
elim (IHN2 … HMN) -N /3 width=3/
qed-.

lemma lsreds_dsubst: ∀s. dsubstable_dx (lsreds s).
#s #D #M1 #M2 #H elim H -s -M1 -M2 // /3 width=3/
qed.

theorem lsreds_mono: ∀s. singlevalued … (lsreds s).
#s #M #N1 #H elim H -s -M -N1
[ /2 width=3 by lsreds_inv_nil/
| #p #M #M1 #HM1 #s #N1 #_ #IHMN1 #N2 #H
  elim (lsreds_inv_cons … H ???) -H [4: // |2,3: skip ] #M2 #HM2 #HMN2 (**) (* simplify line *)
  lapply (lsred_mono … HM1 … HM2) -M #H destruct /2 width=1/
]
qed-.

theorem lsreds_trans: ∀s1,M1,M. M1 ⇀*[s1] M →
                      ∀s2,M2. M ⇀*[s2] M2 → M1 ⇀*[s1@s2] M2.
#s1 #M1 #M #H elim H -s1 -M1 -M normalize // /3 width=3/
qed-.
