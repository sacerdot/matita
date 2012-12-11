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

(* POINTER SEQUENCE *********************************************************)

(* Policy: pointer sequence metavariables: r, s *)
definition pseq: Type[0] ≝ list ptr.

(* Note: a "head" computation contracts just redexes in the head *)
definition is_head: predicate pseq ≝ All … in_head.

(* Note: to us, a "normal" computation contracts redexes in non-decreasing positions *)
definition is_le: predicate pseq ≝ Allr … ple.

lemma is_le_compatible: ∀c,s. is_le s → is_le (c:::s).
#c #s elim s -s // #p * //
#q #s #IHs * /3 width=1/
qed.

lemma is_le_cons: ∀p,s. is_le s → is_le ((dx::p)::sn:::s).
#p #s elim s -s // #q1 * /2 width=1/
#q2 #s #IHs * /4 width=1/
qed.

lemma is_le_append: ∀r. is_le r → ∀s. is_le s → is_le ((dx:::r)@sn:::s).
#r elim r -r /3 width=1/ #p * /2 width=1/
#q #r #IHr * /3 width=1/
qed.

theorem is_head_is_le: ∀s. is_head s → is_le s.
#s elim s -s // #p * //
#q #s #IHs * /3 width=1/
qed.

lemma is_le_in_head: ∀p. in_head p → ∀s. is_le s → is_le (p::s).
#p #Hp * // /3 width=1/
qed.

theorem is_head_is_le_trans: ∀r. is_head r → ∀s. is_le s → is_le (r@s).
#r elim r -r // #p *
[ #_ * /2 width=1/
| #q #r #IHr * /3 width=1/
]
qed.

definition ho_compatible_rc: predicate (pseq→relation term) ≝ λR.
                             ∀s,A1,A2. R s A1 A2 → R (sn:::s) (𝛌.A1) (𝛌.A2).

definition ho_compatible_sn: predicate (pseq→relation term) ≝ λR.
                             ∀s,B1,B2,A. R s B1 B2 → R (sn:::s) (@B1.A) (@B2.A).

definition ho_compatible_dx: predicate (pseq→relation term) ≝ λR.
                             ∀s,B,A1,A2. R s A1 A2 → R (dx:::s) (@B.A1) (@B.A2).

lemma lstar_compatible_rc: ∀R. compatible_rc R → ho_compatible_rc (lstar … R).
#R #HR #s #A1 #A2 #H @(lstar_ind_l ????????? H) -s -A1 // /3 width=3/
qed.

lemma lstar_compatible_sn: ∀R. compatible_sn R → ho_compatible_sn (lstar … R).
#R #HR #s #B1 #B2 #A #H @(lstar_ind_l ????????? H) -s -B1 // /3 width=3/
qed.

lemma lstar_compatible_dx: ∀R. compatible_dx R → ho_compatible_dx (lstar … R).
#R #HR #s #B #A1 #A2 #H @(lstar_ind_l ????????? H) -s -A1 // /3 width=3/
qed.
