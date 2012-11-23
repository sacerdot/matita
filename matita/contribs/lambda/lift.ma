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

include "trichotomy.ma".
include "term.ma".

(* RELOCATION ***************************************************************)

(* Policy: depth (level) metavariables: d, e
           height metavariables       : h, k
*)
(* Note: indexes start at zero *)
let rec lift d h M on M ≝ match M with
[ VRef i   ⇒ #(tri … i d i (i + h) (i + h))
| Abst A   ⇒ 𝛌. (lift (d+1) h A)
| Appl B A ⇒ @(lift d h B). (lift d h A)
].

interpretation "relocation" 'Lift d h M = (lift d h M).

notation "hvbox( ↑ [ d , break h ] break term 55 M )"
   non associative with precedence 55
   for @{ 'Lift $d $h $M }.

notation > "hvbox( ↑ [ h ] break term 55 M )"
   non associative with precedence 55
   for @{ 'Lift 0 $h $M }.

notation > "hvbox( ↑ term 55 M )"
   non associative with precedence 55
   for @{ 'Lift 0 1 $M }.

lemma lift_vref_lt: ∀d,h,i. i < d → ↑[d, h] #i = #i.
normalize /3 width=1/
qed.

lemma lift_vref_ge: ∀d,h,i. d ≤ i → ↑[d, h] #i = #(i+h).
#d #h #i #H elim (le_to_or_lt_eq … H) -H
normalize // /3 width=1/
qed.

lemma lift_inv_abst: ∀C,d,h,M. ↑[d, h] M = 𝛌.C →
                     ∃∃A. ↑[d+1, h] A = C & M = 𝛌.A.
#C #d #h * normalize
[ #i #H destruct
| #A #H destruct /2 width=3/
| #B #A #H destruct
]
qed-.

lemma lift_inv_appl: ∀D,C,d,h,M. ↑[d, h] M = @D.C →
                     ∃∃B,A. ↑[d, h] B = D & ↑[d, h] A = C & M = @B.A.
#D #C #d #h * normalize
[ #i #H destruct
| #A #H destruct
| #B #A #H destruct /2 width=5/
]
qed-.
