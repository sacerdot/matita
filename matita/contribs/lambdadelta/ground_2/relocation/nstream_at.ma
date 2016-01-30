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

let rec apply (i: nat) on i: rtmap → nat ≝ ?.
* #b #f cases i -i
[ @b
| #i lapply (apply i f) -apply -i -f
  #i @(⫯(b+i))
]
qed.

interpretation "functional application (nstream)"
   'Apply f i = (apply i f).

inductive at: rtmap → relation nat ≝
| at_zero: ∀f. at (0 @ f) 0 0
| at_skip: ∀f,i1,i2. at f i1 i2 → at (0 @ f) (⫯i1) (⫯i2)
| at_lift: ∀f,b,i1,i2. at (b @ f) i1 i2 → at (⫯b @ f) i1 (⫯i2)
.

interpretation "relational application (nstream)"
   'RAt i1 f i2 = (at f i1 i2).

(* Basic properties on apply ************************************************)

lemma apply_S1: ∀f,a,i. (⫯a@f)@❴i❵ = ⫯((a@f)@❴i❵).
#a #f * //
qed.

(* Basic inversion lemmas on at *********************************************)

fact at_inv_xOx_aux: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 → ∀g. f = 0@g →
                     (i1 = 0 ∧ i2 = 0) ∨
                     ∃∃j1,j2. @⦃j1, g⦄ ≡ j2 & i1 = ⫯j1 & i2 = ⫯j2.
#f #i1 #i2 * -f -i1 -i2
[ /3 width=1 by or_introl, conj/
| #f #i1 #i2 #Hi #g #H destruct /3 width=5 by ex3_2_intro, or_intror/
| #f #b #i1 #i2 #_ #g #H destruct
]
qed-.

lemma at_inv_xOx: ∀f,i1,i2. @⦃i1, 0@f⦄ ≡ i2 →
                  (i1 = 0 ∧ i2 = 0) ∨
                  ∃∃j1,j2. @⦃j1, f⦄ ≡ j2 & i1 = ⫯j1 & i2 = ⫯j2.
/2 width=3 by at_inv_xOx_aux/ qed-.

lemma at_inv_OOx: ∀f,i. @⦃0, 0 @ f⦄ ≡ i → i = 0.
#f #i #H elim (at_inv_xOx … H) -H * //
#j1 #j2 #_ #H destruct
qed-.

lemma at_inv_xOO: ∀f,i. @⦃i, 0@f⦄ ≡ 0 → i = 0.
#f #i #H elim (at_inv_xOx … H) -H * //
#j1 #j2 #_ #_ #H destruct
qed-.

lemma at_inv_SOx: ∀f,i1,i2. @⦃⫯i1, 0@f⦄ ≡ i2 →
                  ∃∃j2. @⦃i1, f⦄ ≡ j2 & i2 = ⫯j2.
#f #i1 #i2 #H elim (at_inv_xOx … H) -H *
[ #H destruct
| #j1 #j2 #Hj #H1 #H2 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma at_inv_xOS: ∀f,i1,i2. @⦃i1, 0@f⦄ ≡ ⫯i2 →
                  ∃∃j1. @⦃j1, f⦄ ≡ i2 & i1 = ⫯j1.
#f #i1 #i2 #H elim (at_inv_xOx … H) -H *
[ #_ #H destruct
| #j1 #j2 #Hj #H1 #H2 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma at_inv_SOS: ∀f,i1,i2. @⦃⫯i1, 0@f⦄ ≡ ⫯i2 → @⦃i1, f⦄ ≡ i2.
#f #i1 #i2 #H elim (at_inv_xOx … H) -H *
[ #H destruct
| #j1 #j2 #Hj #H1 #H2 destruct //
]
qed-.

lemma at_inv_OOS: ∀f,i. @⦃0, 0@f⦄ ≡ ⫯i → ⊥.
#f #i #H elim (at_inv_xOx … H) -H *
[ #_ #H destruct
| #j1 #j2 #_ #H destruct
]
qed-.

lemma at_inv_SOO: ∀f,i. @⦃⫯i, 0@f⦄ ≡ 0 → ⊥.
#f #i #H elim (at_inv_xOx … H) -H *
[ #H destruct
| #j1 #j2 #_ #_ #H destruct
]
qed-.

fact at_inv_xSx_aux: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 → ∀g,a. f = ⫯a @ g →
                     ∃∃j2. @⦃i1, a@g⦄ ≡ j2 & i2 = ⫯j2.
#f #i1 #i2 * -f -i1 -i2
[ #f #g #a #H destruct
| #f #i1 #i2 #_ #g #a #H destruct
| #f #b #i1 #i2 #Hi #g #a #H destruct /2 width=3 by ex2_intro/
]
qed-.

lemma at_inv_xSx: ∀f,b,i1,i2. @⦃i1, ⫯b@f⦄ ≡ i2 →
                  ∃∃j2. @⦃i1, b@f⦄ ≡ j2 & i2 = ⫯j2.
/2 width=3 by at_inv_xSx_aux/ qed-.

lemma at_inv_xSS: ∀f,b,i1,i2. @⦃i1, ⫯b @ f⦄ ≡ ⫯i2 → @⦃i1, b@f⦄ ≡ i2.
#f #b #i1 #i2 #H elim (at_inv_xSx … H) -H
#j2 #Hj #H destruct //
qed-.

lemma at_inv_xSO: ∀f,b,i. @⦃i, ⫯b@f⦄ ≡ 0 → ⊥.
#f #b #i #H elim (at_inv_xSx … H) -H
#j2 #_ #H destruct
qed-.

(* alternative definition ***************************************************)

lemma at_O1: ∀b,f. @⦃0, b@f⦄ ≡ b.
#b elim b -b /2 width=1 by at_lift/
qed.

lemma at_S1: ∀b,f,i1,i2. @⦃i1, f⦄ ≡ i2 → @⦃⫯i1, b@f⦄ ≡ ⫯(b+i2).
#b elim b -b /3 width=1 by at_skip, at_lift/
qed.

lemma at_inv_O1: ∀f,b,i2. @⦃0, b@f⦄ ≡ i2 → i2 = b.
#f #b elim b -b /2 width=2 by at_inv_OOx/
#b #IH #i2 #H elim (at_inv_xSx … H) -H
#j2 #Hj #H destruct /3 width=1 by eq_f/
qed-.

lemma at_inv_S1: ∀f,b,j1,i2. @⦃⫯j1, b@f⦄ ≡ i2 → ∃∃j2. @⦃j1, f⦄ ≡ j2 & i2 =⫯(b+j2).
#f #b elim b -b /2 width=1 by at_inv_SOx/
#b #IH #j1 #i2 #H elim (at_inv_xSx … H) -H
#j2 #Hj #H destruct elim (IH … Hj) -IH -Hj
#i2 #Hi #H destruct /2 width=3 by ex2_intro/
qed-.

lemma at_total: ∀i,f. @⦃i, f⦄ ≡ f@❴i❵.
#i elim i -i
[ * // | #i #IH * /3 width=1 by at_S1/ ]
qed.

(* Advanced forward lemmas on at ********************************************)

lemma at_increasing: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 → i1 ≤ i2.
#f #i1 #i2 #H elim H -f -i1 -i2 /2 width=1 by le_S_S, le_S/
qed-.

lemma at_increasing_plus: ∀f,b,i1,i2. @⦃i1, b@f⦄ ≡ i2 → i1 + b ≤ i2.
#f #b *
[ #i2 #H >(at_inv_O1 … H) -i2 //
| #i1 #i2 #H elim (at_inv_S1 … H) -H
  #j1 #Ht #H destruct
  /4 width=2 by at_increasing, monotonic_le_plus_r, le_S_S/
]
qed-.

lemma at_increasing_strict: ∀f,b,i1,i2. @⦃i1, ⫯b @ f⦄ ≡ i2 →
                            i1 < i2 ∧ @⦃i1, b@f⦄ ≡ ⫰i2.
#f #b #i1 #i2 #H elim (at_inv_xSx … H) -H
#j2 #Hj #H destruct /4 width=2 by conj, at_increasing, le_S_S/
qed-.

lemma at_fwd_id: ∀f,b,i. @⦃i, b@f⦄ ≡ i → b = 0.
#f #b *
[ #H <(at_inv_O1 … H) -f -b //
| #i #H elim (at_inv_S1 … H) -H
  #j #H #H0 destruct lapply (at_increasing … H) -H
  #H lapply (eq_minus_O … H) -H //
]
qed.

(* Main properties on at ****************************************************)

lemma at_id_le: ∀i1,i2. i1 ≤ i2 → ∀f. @⦃i2, f⦄ ≡ i2 → @⦃i1, f⦄ ≡ i1.
#i1 #i2 #H @(le_elim … H) -i1 -i2 [ #i2 | #i1 #i2 #IH ]
* #b #f #H lapply (at_fwd_id … H)
#H0 destruct /4 width=1 by at_S1, at_inv_SOS/
qed-.

let corec at_ext: ∀f1,f2. (∀i,i1,i2. @⦃i, f1⦄ ≡ i1 → @⦃i, f2⦄ ≡ i2 → i1 = i2) → f1 ≐ f2 ≝ ?.
* #b1 #f1 * #b2 #f2 #Hi lapply (Hi 0 b1 b2 ? ?) //
#H lapply (at_ext f1 f2 ?) /2 width=1 by eq_seq/ -at_ext
#j #j1 #j2 #H1 #H2 @(injective_plus_r … b2) /4 width=5 by at_S1, injective_S/ (**) (* full auto fails *)
qed-.

theorem at_monotonic: ∀i1,i2. i1 < i2 → ∀f1,f2. f1 ≐ f2 → ∀j1,j2. @⦃i1, f1⦄ ≡ j1 → @⦃i2, f2⦄ ≡ j2 → j1 < j2.
#i1 #i2 #H @(lt_elim … H) -i1 -i2
[ #i2 * #b1 #f1 * #b2 #f2 #H elim (eq_stream_inv_seq ????? H) -H
  #H #Ht #j1 #j2 #H1 #H2 destruct
  >(at_inv_O1 … H1) elim (at_inv_S1 … H2) -H2 -j1 //
| #i1 #i2 #IH * #b1 #f1 * #b2 #f2 #H elim (eq_stream_inv_seq ????? H) -H
  #H #Ht #j1 #j2 #H1 #H2 destruct
  elim (at_inv_S1 … H2) elim (at_inv_S1 … H1) -H1 -H2
  #x1 #Hx1 #H1 #x2 #Hx2 #H2 destruct /4 width=5 by lt_S_S, monotonic_lt_plus_r/
]
qed-.

theorem at_inv_monotonic: ∀f1,i1,j1. @⦃i1, f1⦄ ≡ j1 → ∀f2,i2,j2. @⦃i2, f2⦄ ≡ j2 → f1 ≐ f2 → j2 < j1 → i2 < i1.
#f1 #i1 #j1 #H elim H -f1 -i1 -j1
[ #f1 #f2 #i2 #j2 #_ #_ #H elim (lt_le_false … H) //
| #f1 #i1 #j1 #_ #IH * #b2 #f2 #i2 #j2 #H #Ht #Hj elim (eq_stream_inv_seq ????? Ht) -Ht
  #H0 #Ht destruct elim (at_inv_xOx … H) -H *
  [ #H1 #H2 destruct //
  | #x2 #y2 #Hxy #H1 #H2 destruct /4 width=5 by lt_S_S_to_lt, lt_S_S/
  ]
| #f1 #b1 #i1 #j1 #_ #IH * #b2 #f2 #i2 #j2 #H #Ht #Hj elim (eq_stream_inv_seq ????? Ht) -Ht
  #H0 #Ht destruct elim (at_inv_xSx … H) -H
  #y2 #Hy #H destruct /3 width=5 by eq_seq, lt_S_S_to_lt/
]
qed-.

theorem at_mono: ∀f1,f2. f1 ≐ f2 → ∀i,i1. @⦃i, f1⦄ ≡ i1 → ∀i2. @⦃i, f2⦄ ≡ i2 → i2 = i1.
#f1 #f2 #Ht #i #i1 #H1 #i2 #H2 elim (lt_or_eq_or_gt i2 i1) //
#Hi elim (lt_le_false i i) /3 width=8 by at_inv_monotonic, eq_stream_sym/
qed-.

theorem at_inj: ∀f1,f2. f1 ≐ f2 → ∀i1,i. @⦃i1, f1⦄ ≡ i → ∀i2. @⦃i2, f2⦄ ≡ i → i1 = i2.
#f1 #f2 #Ht #i1 #i #H1 #i2 #H2 elim (lt_or_eq_or_gt i2 i1) //
#Hi elim (lt_le_false i i) /3 width=8 by at_monotonic, eq_stream_sym/
qed-.

lemma at_inv_total: ∀f,i1,i2. @⦃i1, f⦄ ≡ i2 → i2 = f@❴i1❵.
/2 width=6 by at_mono/ qed-.

lemma at_repl_back: ∀i1,i2. eq_stream_repl_back ? (λf. @⦃i1, f⦄ ≡ i2).
#i1 #i2 #f1 #f2 #Ht #H1 lapply (at_total i1 f2)
#H2 <(at_mono … Ht … H1 … H2) -f1 -i2 //
qed-.

lemma at_repl_fwd: ∀i1,i2. eq_stream_repl_fwd ? (λf. @⦃i1, f⦄ ≡ i2).
#i1 #i2 @eq_stream_repl_sym /2 width=3 by at_repl_back/
qed-.

(* Advanced properties on at ************************************************)

(* Note: see also: trace_at/at_dec *)
lemma at_dec: ∀f,i1,i2. Decidable (@⦃i1, f⦄ ≡ i2).
#f #i1 #i2 lapply (at_total i1 f)
#Ht elim (eq_nat_dec i2 (f@❴i1❵))
[ #H destruct /2 width=1 by or_introl/
| /4 width=6 by at_mono, or_intror/
]
qed-.

lemma is_at_dec_le: ∀f,i2,i. (∀i1. i1 + i ≤ i2 → @⦃i1, f⦄ ≡ i2 → ⊥) → Decidable (∃i1. @⦃i1, f⦄ ≡ i2).
#f #i2 #i elim i -i
[ #Ht @or_intror * /3 width=3 by at_increasing/
| #i #IH #Ht elim (at_dec f (i2-i) i2) /3 width=2 by ex_intro, or_introl/
  #Hi2 @IH -IH #i1 #H #Hi elim (le_to_or_lt_eq … H) -H /2 width=3 by/
  #H destruct -Ht /2 width=1 by/
]
qed-.

(* Note: see also: trace_at/is_at_dec *)
lemma is_at_dec: ∀f,i2. Decidable (∃i1. @⦃i1, f⦄ ≡ i2).
#f #i2 @(is_at_dec_le ? ? (⫯i2)) /2 width=4 by lt_le_false/
qed-.

(* Advanced properties on apply *********************************************)

fact apply_inj_aux: ∀f1,f2. f1 ≐ f2 → ∀i,i1,i2. i = f1@❴i1❵ → i = f2@❴i2❵ → i1 = i2.
/2 width=6 by at_inj/ qed-.
