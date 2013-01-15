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

include "terms/relocating_substitution.ma".
include "subterms/relocating_substitution.ma".

(* BOOLEAN (EMPTY OR FULL) SUBSET *******************************************)

let rec boolean b M on M ≝ match M with
[ VRef i   ⇒ {b}#i
| Abst A   ⇒ {b}𝛌.(boolean b A)
| Appl B A ⇒ {b}@(boolean b B).(boolean b A)
].

interpretation "boolean subset (subterms)"
   'ProjectUp b M = (boolean b M).

notation "hvbox( { term 46 b } ⇑ break term 46 M)"
   non associative with precedence 46
   for @{ 'ProjectUp $b $M }.

lemma boolean_inv_vref: ∀j,b0,b,M. {b}⇑ M = {b0}#j → b = b0 ∧ M = #j.
#j #b0 #b * normalize
[ #i #H destruct /2 width=1/
| #A #H destruct
| #B #A #H destruct
]
qed-.

lemma boolean_inv_abst: ∀U,b0,b,M. {b}⇑ M = {b0}𝛌.U →
                        ∃∃C. b = b0 & {b}⇑C = U & M = 𝛌.C.
#U #b0 #b * normalize
[ #i #H destruct
| #A #H destruct /2 width=3/
| #B #A #H destruct
]
qed-.

lemma boolean_inv_appl: ∀W,U,b0,b,M. {b}⇑ M = {b0}@W.U →
                        ∃∃D,C. b = b0 & {b}⇑D = W & {b}⇑C = U & M = @D.C.
#W #U #b0 #b * normalize
[ #i #H destruct
| #A #H destruct
| #B #A #H destruct /2 width=5/
]
qed-.

lemma boolean_lift: ∀b,h,M,d. {b}⇑ ↑[d, h] M = ↑[d, h] {b}⇑ M.
#b #h #M elim M -M normalize //
qed.

lemma boolean_dsubst: ∀b,N,M,d. {b}⇑ [d ↙ N] M = [d ↙ {b}⇑ N] {b}⇑ M.
#b #N #M elim M -M [2,3: normalize // ]
#i #d elim (lt_or_eq_or_gt i d) #Hid
[ >(sdsubst_vref_lt … Hid) >(dsubst_vref_lt … Hid) //
| destruct normalize //
| >(sdsubst_vref_gt … Hid) >(dsubst_vref_gt … Hid) //
]
qed.
