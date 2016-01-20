(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.tcs.unibo.it                            *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "ground_2/notation/functions/apply_2.ma".
include "ground_2/notation/relations/rat_3.ma".
include "ground_2/relocation/nstream.ma".

(* RELOCATION N-STREAM ******************************************************)

let rec apply (i: nat) on i: nstream → nat ≝ ?.
* #b #t cases i -i
[ @b
| #i lapply (apply i t) -apply -i -t
  #i @(⫯(b+i))
]
qed.

interpretation "functional application (nstream)"
   'Apply t i = (apply i t).

inductive at: nstream → relation nat ≝
| at_zero: ∀t. at (0 @ t) 0 0
| at_skip: ∀t,i1,i2. at t i1 i2 → at (0 @ t) (⫯i1) (⫯i2)
| at_lift: ∀t,b,i1,i2. at (b @ t) i1 i2 → at (⫯b @ t) i1 (⫯i2)
.

interpretation "relational application (nstream)"
   'RAt i1 t i2 = (at t i1 i2).

(* Basic properties on apply ************************************************)

lemma apply_S1: ∀t,a,i. (⫯a@t)@❴i❵ = ⫯((a@t)@❴i❵).
#a #t * //
qed.

(* Basic inversion lemmas on at *********************************************)

fact at_inv_xOx_aux: ∀t,i1,i2. @⦃i1, t⦄ ≡ i2 → ∀u. t = 0 @ u →
                     (i1 = 0 ∧ i2 = 0) ∨
                     ∃∃j1,j2. @⦃j1, u⦄ ≡ j2 & i1 = ⫯j1 & i2 = ⫯j2.
#t #i1 #i2 * -t -i1 -i2
[ /3 width=1 by or_introl, conj/
| #t #i1 #i2 #Hi #u #H destruct /3 width=5 by ex3_2_intro, or_intror/
| #t #b #i1 #i2 #_ #u #H destruct
]
qed-.

lemma at_inv_xOx: ∀t,i1,i2. @⦃i1, 0 @ t⦄ ≡ i2 →
                  (i1 = 0 ∧ i2 = 0) ∨
                  ∃∃j1,j2. @⦃j1, t⦄ ≡ j2 & i1 = ⫯j1 & i2 = ⫯j2.
/2 width=3 by at_inv_xOx_aux/ qed-.

lemma at_inv_OOx: ∀t,i. @⦃0, 0 @ t⦄ ≡ i → i = 0.
#t #i #H elim (at_inv_xOx … H) -H * //
#j1 #j2 #_ #H destruct
qed-.

lemma at_inv_xOO: ∀t,i. @⦃i, 0 @ t⦄ ≡ 0 → i = 0.
#t #i #H elim (at_inv_xOx … H) -H * //
#j1 #j2 #_ #_ #H destruct
qed-.

lemma at_inv_SOx: ∀t,i1,i2. @⦃⫯i1, 0 @ t⦄ ≡ i2 →
                  ∃∃j2. @⦃i1, t⦄ ≡ j2 & i2 = ⫯j2.
#t #i1 #i2 #H elim (at_inv_xOx … H) -H *
[ #H destruct
| #j1 #j2 #Hj #H1 #H2 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma at_inv_xOS: ∀t,i1,i2. @⦃i1, 0 @ t⦄ ≡ ⫯i2 →
                  ∃∃j1. @⦃j1, t⦄ ≡ i2 & i1 = ⫯j1.
#t #i1 #i2 #H elim (at_inv_xOx … H) -H *
[ #_ #H destruct
| #j1 #j2 #Hj #H1 #H2 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma at_inv_SOS: ∀t,i1,i2. @⦃⫯i1, 0 @ t⦄ ≡ ⫯i2 → @⦃i1, t⦄ ≡ i2.
#t #i1 #i2 #H elim (at_inv_xOx … H) -H *
[ #H destruct
| #j1 #j2 #Hj #H1 #H2 destruct //
]
qed-.

lemma at_inv_OOS: ∀t,i. @⦃0, 0 @ t⦄ ≡ ⫯i → ⊥.
#t #i #H elim (at_inv_xOx … H) -H *
[ #_ #H destruct
| #j1 #j2 #_ #H destruct
]
qed-.

lemma at_inv_SOO: ∀t,i. @⦃⫯i, 0 @ t⦄ ≡ 0 → ⊥.
#t #i #H elim (at_inv_xOx … H) -H *
[ #H destruct
| #j1 #j2 #_ #_ #H destruct
]
qed-.

fact at_inv_xSx_aux: ∀t,i1,i2. @⦃i1, t⦄ ≡ i2 → ∀u,a. t = ⫯a @ u →
                     ∃∃j2. @⦃i1, a@u⦄ ≡ j2 & i2 = ⫯j2.
#t #i1 #i2 * -t -i1 -i2
[ #t #u #a #H destruct
| #t #i1 #i2 #_ #u #a #H destruct
| #t #b #i1 #i2 #Hi #u #a #H destruct /2 width=3 by ex2_intro/
]
qed-.

lemma at_inv_xSx: ∀t,b,i1,i2. @⦃i1, ⫯b @ t⦄ ≡ i2 →
                  ∃∃j2. @⦃i1, b @ t⦄ ≡ j2 & i2 = ⫯j2.
/2 width=3 by at_inv_xSx_aux/ qed-.

lemma at_inv_xSS: ∀t,b,i1,i2. @⦃i1, ⫯b @ t⦄ ≡ ⫯i2 → @⦃i1, b@t⦄ ≡ i2.
#t #b #i1 #i2 #H elim (at_inv_xSx … H) -H
#j2 #Hj #H destruct //
qed-.

lemma at_inv_xSO: ∀t,b,i. @⦃i, ⫯b @ t⦄ ≡ 0 → ⊥.
#t #b #i #H elim (at_inv_xSx … H) -H
#j2 #_ #H destruct
qed-.

(* alternative definition ***************************************************)

lemma at_O1: ∀b,t. @⦃0, b @ t⦄ ≡ b.
#b elim b -b /2 width=1 by at_lift/
qed.

lemma at_S1: ∀b,t,i1,i2. @⦃i1, t⦄ ≡ i2 → @⦃⫯i1, b@t⦄ ≡ ⫯(b+i2).
#b elim b -b /3 width=1 by at_skip, at_lift/
qed.

lemma at_inv_O1: ∀t,b,i2. @⦃0, b@t⦄ ≡ i2 → i2 = b.
#t #b elim b -b /2 width=2 by at_inv_OOx/
#b #IH #i2 #H elim (at_inv_xSx … H) -H
#j2 #Hj #H destruct /3 width=1 by eq_f/
qed-.

lemma at_inv_S1: ∀t,b,j1,i2. @⦃⫯j1, b@t⦄ ≡ i2 → ∃∃j2. @⦃j1, t⦄ ≡ j2 & i2 =⫯(b+j2).
#t #b elim b -b /2 width=1 by at_inv_SOx/
#b #IH #j1 #i2 #H elim (at_inv_xSx … H) -H
#j2 #Hj #H destruct elim (IH … Hj) -IH -Hj
#i2 #Hi #H destruct /2 width=3 by ex2_intro/
qed-.

lemma at_total: ∀i,t. @⦃i, t⦄ ≡ t@❴i❵.
#i elim i -i
[ * // | #i #IH * /3 width=1 by at_S1/ ]
qed.  

(* Advanced forward lemmas on at ********************************************)

lemma at_increasing: ∀t,i1,i2. @⦃i1, t⦄ ≡ i2 → i1 ≤ i2.
#t #i1 #i2 #H elim H -t -i1 -i2 /2 width=1 by le_S_S, le_S/
qed-.

lemma at_increasing_plus: ∀t,b,i1,i2. @⦃i1, b@t⦄ ≡ i2 → i1 + b ≤ i2.
#t #b *
[ #i2 #H >(at_inv_O1 … H) -i2 //
| #i1 #i2 #H elim (at_inv_S1 … H) -H
  #j1 #Ht #H destruct
  /4 width=2 by at_increasing, monotonic_le_plus_r, le_S_S/
]
qed-.

lemma at_increasing_strict: ∀t,b,i1,i2. @⦃i1, ⫯b @ t⦄ ≡ i2 →
                            i1 < i2 ∧ @⦃i1, b@t⦄ ≡ ⫰i2.
#t #b #i1 #i2 #H elim (at_inv_xSx … H) -H
#j2 #Hj #H destruct /4 width=2 by conj, at_increasing, le_S_S/
qed-.

(* Main properties on at ****************************************************)

let corec at_ext: ∀t1,t2. (∀i,i1,i2. @⦃i, t1⦄ ≡ i1 → @⦃i, t2⦄ ≡ i2 → i1 = i2) → t1 ≐ t2 ≝ ?.
* #b1 #t1 * #b2 #t2 #Hi lapply (Hi 0 b1 b2 ? ?) //
#H lapply (at_ext t1 t2 ?) /2 width=1 by eq_sec/ -at_ext
#j #j1 #j2 #H1 #H2 @(injective_plus_r … b2) /4 width=5 by at_S1, injective_S/ (**) (* full auto fails *)
qed-.

theorem at_monotonic: ∀i1,i2. i1 < i2 → ∀t,j1,j2. @⦃i1, t⦄ ≡ j1 → @⦃i2, t⦄ ≡ j2 → j1 < j2.
#i1 #i2 #H @(lt_elim … H) -i1 -i2
[ #i2 *#b #t #j1 #j2 #H1 #H2 >(at_inv_O1 … H1) elim (at_inv_S1 … H2) -H2 -j1 //
| #i1 #i2 #IH * #b #t #j1 #j2 #H1 #H2 elim (at_inv_S1 … H2) elim (at_inv_S1 … H1) -H1 -H2
  #x1 #Hx1 #H1 #x2 #Hx2 #H2 destruct /4 width=3 by lt_S_S, monotonic_lt_plus_r/
]
qed-.

theorem at_inv_monotonic: ∀t,i1,j1. @⦃i1, t⦄ ≡ j1 → ∀i2,j2. @⦃i2, t⦄ ≡ j2 → j2 < j1 → i2 < i1.
#t #i1 #j1 #H elim H -t -i1 -j1
[ #t #i2 #j2 #_ #H elim (lt_le_false … H) //
| #t #i1 #j1 #_ #IH #i2 #j2 #H #Hj elim (at_inv_xOx … H) -H *
  [ #H1 #H2 destruct //
  | #x2 #y2 #Hxy #H1 #H2 destruct /4 width=3 by lt_S_S_to_lt, lt_S_S/
  ]
| #t #b1 #i1 #j1 #_ #IH #i2 #j2 #H #Hj elim (at_inv_xSx … H) -H
  #y2 #Hy #H destruct /3 width=3 by lt_S_S_to_lt/
]
qed-.

theorem at_mono: ∀t,i,i1. @⦃i, t⦄ ≡ i1 → ∀i2. @⦃i, t⦄ ≡ i2 → i2 = i1.
#t #i #i1 #H1 #i2 #H2 elim (lt_or_eq_or_gt i2 i1) //
#Hi elim (lt_le_false i i) /2 width=6 by at_inv_monotonic/
qed-.

theorem at_inj: ∀t,i1,i. @⦃i1, t⦄ ≡ i → ∀i2. @⦃i2, t⦄ ≡ i → i1 = i2.
#t #i1 #i #H1 #i2 #H2 elim (lt_or_eq_or_gt i2 i1) //
#Hi elim (lt_le_false i i) /2 width=6 by at_monotonic/
qed-.

lemma at_inv_total: ∀t,i1,i2. @⦃i1, t⦄ ≡ i2 → i2 = t@❴i1❵.
/2 width=4 by at_mono/ qed-.

(* Advanced properties on at ************************************************)

(* Note: see also: trace_at/at_dec *)
lemma at_dec: ∀t,i1,i2. Decidable (@⦃i1, t⦄ ≡ i2).
#t #i1 #i2 lapply (at_total i1 t)
#Ht elim (eq_nat_dec i2 (t@❴i1❵))
[ #H destruct /2 width=1 by or_introl/
| /4 width=4 by at_mono, or_intror/
]
qed-.

lemma is_at_dec_le: ∀t,i2,i. (∀i1. i1 + i ≤ i2 → @⦃i1, t⦄ ≡ i2 → ⊥) → Decidable (∃i1. @⦃i1, t⦄ ≡ i2).
#t #i2 #i elim i -i
[ #Ht @or_intror * /3 width=3 by at_increasing/
| #i #IH #Ht elim (at_dec t (i2-i) i2) /3 width=2 by ex_intro, or_introl/
  #Hi2 @IH -IH #i1 #H #Hi elim (le_to_or_lt_eq … H) -H /2 width=3 by/
  #H destruct -Ht /2 width=1 by/
]
qed-.

(* Note: see also: trace_at/is_at_dec *)
lemma is_at_dec: ∀t,i2. Decidable (∃i1. @⦃i1, t⦄ ≡ i2).
#t #i2 @(is_at_dec_le ? ? (⫯i2)) /2 width=4 by lt_le_false/
qed-.

(* Advanced properties on apply *********************************************)

fact apply_inj_aux: ∀t,i,i1,i2. i = t@❴i1❵ → i = t@❴i2❵ → i1 = i2.
/2 width=4 by at_inj/ qed-.
