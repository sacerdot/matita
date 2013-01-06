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

lemma is_standard_compatible: ∀c,s. is_standard s → is_standard (c:::s).
#c #s elim s -s // #p * //
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

theorem is_whd_is_standard: ∀s. is_whd s → is_standard s.
#s elim s -s // #p * //
#q #s #IHs * /3 width=1/
qed.

lemma is_standard_in_whd: ∀p. in_whd p → ∀s. is_standard s → is_standard (p::s).
#p #Hp * // /3 width=1/
qed.

theorem is_whd_is_standard_trans: ∀r. is_whd r → ∀s. is_standard s → is_standard (r@s).
#r elim r -r // #p *
[ #_ * /2 width=1/
| #q #r #IHr * /3 width=1/
]
qed.
