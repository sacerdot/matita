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

include "paths/trace.ma".
include "paths/standard_order.ma".

(* STANDARD TRACE ***********************************************************)

(* Note: to us, a "standard" computation contracts redexes in non-decreasing positions *)
definition is_standard: predicate trace ≝ Allr … sle.

lemma is_standard_fwd_append_sn: ∀s,r. is_standard (s@r) → is_standard s.
/2 width=2 by Allr_fwd_append_sn/
qed-.

lemma is_standard_fwd_cons: ∀p,s. is_standard (p::s) → is_standard s.
/2 width=2 by Allr_fwd_cons/
qed-.

lemma is_standard_compatible: ∀o,s. is_standard s → is_standard (o:::s).
#o #s elim s -s // #p * //
#q #s #IHs * /3 width=1/
qed.

lemma is_standard_cons: ∀p,s. is_standard s → is_standard ((dx::p)::sn:::s).
#p #s elim s -s // #q1 * /2 width=1/
#q2 #s #IHs * /4 width=1/
qed.

lemma is_standard_append: ∀r. is_standard r → ∀s. is_standard s → is_standard ((dx:::r)@sn:::s).
#r elim r -r /3 width=1/ #p * /2 width=1/
#q #r #IHr * /3 width=1/
qed.

lemma is_standard_fwd_sle: ∀s2,p2,s1,p1. is_standard ((p1::s1)@(p2::s2)) → p1 ≤ p2.
#s2 #p2 #s1 elim s1 -s1
[ #p1 * //
| #q1 #s1 #IHs1 #p1 * /3 width=3 by sle_trans/
]
qed-.

lemma is_standard_in_whd: ∀p. in_whd p → ∀s. is_standard s → is_standard (p::s).
#p #Hp * // /3 width=1/
qed.

theorem is_whd_is_standard: ∀s. is_whd s → is_standard s.
#s elim s -s // #p * //
#q #s #IHs * /3 width=1/
qed.

theorem is_whd_is_standard_trans: ∀r. is_whd r → ∀s. is_standard s → is_standard (r@s).
#r elim r -r // #p *
[ #_ * /2 width=1/
| #q #r #IHr * /3 width=1/
]
qed.

lemma is_standard_fwd_is_whd: ∀s,p,r. in_whd p → is_standard (r@(p::s)) → is_whd r.
#s #p #r elim r -r // #q #r #IHr #Hp #H
lapply (is_standard_fwd_cons … H)
lapply (is_standard_fwd_sle … H) #Hqp
lapply (sle_fwd_in_whd … Hqp Hp) /3 width=1/
qed-.