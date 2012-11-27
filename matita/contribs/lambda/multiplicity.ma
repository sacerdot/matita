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

include "delifting_substitution.ma".

(* MULTIPLICITY *************************************************************)

(* Note: this gives the number of variable references in M *)
let rec mult M on M ≝ match M with
[ VRef i   ⇒ 1
| Abst A   ⇒ mult A
| Appl B A ⇒ (mult B) + (mult A)
].

interpretation "multiplicity"
   'Multiplicity M = (mult M).

notation "hvbox( #{M} )"
   non associative with precedence 55
   for @{ 'Multiplicity $M }.

lemma mult_positive: ∀M. 0 < #{M}.
#M elim M -M // /2 width=1/
qed.

lemma mult_lift: ∀h,M,d. #{↑[d, h] M} = #{M}.
#H #M elim M -M normalize //
qed.

theorem mult_dsubst: ∀C,M,d. #{[d ⬐ C] M} ≤ #{M} * #{C}.
#C #M elim M -M
[ #i #d elim (lt_or_eq_or_gt i d) #Hid
  [ >(dsubst_vref_lt … Hid) normalize //
  | destruct >dsubst_vref_eq normalize //
  | >(dsubst_vref_gt … Hid) normalize //
  ]
| normalize //
| normalize #B #A #IHB #IHA #d
  >distributive_times_plus_r /2 width=1/
]
qed.
