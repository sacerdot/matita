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

include "ground_2/notation/relations/rat_3.ma".
include "ground_2/relocation/trace.ma".

(* RELOCATION TRACE *********************************************************)

inductive at: trace → relation nat ≝
   | at_zero : ∀cs. at (Ⓣ @ cs) 0 0
   | at_succ : ∀cs,i,j. at cs i j → at (Ⓣ @ cs) (⫯i) (⫯j)
   | at_false: ∀cs,i,j. at cs i j → at (Ⓕ @ cs) i (⫯j).

interpretation "relocation (trace)"
   'RAt i1 cs i2 = (at cs i1 i2).

(* Basic inversion lemmas ***************************************************)

fact at_inv_empty_aux: ∀cs,i,j. @⦃i, cs⦄ ≡ j → cs = ◊ → ⊥.
#cs #i #j * -cs -i -j
#cs [2,3: #i #j #_ ] #H destruct
qed-.

lemma at_inv_empty: ∀i,j. @⦃i, ◊⦄ ≡ j → ⊥.
/2 width=5 by at_inv_empty_aux/ qed-.

fact at_inv_true_aux: ∀cs,i,j. @⦃i, cs⦄ ≡ j → ∀tl. cs = Ⓣ @ tl →
                      (i = 0 ∧ j = 0) ∨
                      ∃∃i0,j0. i = ⫯i0 & j = ⫯j0 & @⦃i0, tl⦄ ≡ j0.
#cs #i #j * -cs -i -j
#cs [2,3: #i #j #Hij ] #tl #H destruct
/3 width=5 by ex3_2_intro, or_introl, or_intror, conj/
qed-.

lemma at_inv_true: ∀cs,i,j. @⦃i, Ⓣ @ cs⦄ ≡ j →
                   (i = 0 ∧ j = 0) ∨
                   ∃∃i0,j0. i = ⫯i0 & j = ⫯j0 & @⦃i0, cs⦄ ≡ j0.
/2 width=3 by at_inv_true_aux/ qed-.

lemma at_inv_true_zero_sn: ∀cs,j. @⦃0, Ⓣ @ cs⦄ ≡ j → j = 0.
#cs #j #H elim (at_inv_true … H) -H * //
#i0 #j0 #H destruct
qed-.

lemma at_inv_true_zero_dx: ∀cs,i. @⦃i, Ⓣ @ cs⦄ ≡ 0 → i = 0.
#cs #i #H elim (at_inv_true … H) -H * //
#i0 #j0 #_ #H destruct
qed-.

lemma at_inv_true_succ_sn: ∀cs,i,j. @⦃⫯i, Ⓣ @ cs⦄ ≡ j →
                           ∃∃j0. j = ⫯j0 & @⦃i, cs⦄ ≡ j0.
#cs #i #j #H elim (at_inv_true … H) -H *
[ #H destruct
| #i0 #j0 #H1 #H2 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma at_inv_true_succ_dx: ∀cs,i,j. @⦃i, Ⓣ @ cs⦄ ≡ ⫯j →
                           ∃∃i0. i = ⫯i0 & @⦃i0, cs⦄ ≡ j.
#cs #i #j #H elim (at_inv_true … H) -H *
[ #_ #H destruct
| #i0 #j0 #H1 #H2 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma at_inv_true_succ: ∀cs,i,j. @⦃⫯i, Ⓣ @ cs⦄ ≡ ⫯j →
                        @⦃i, cs⦄ ≡ j.
#cs #i #j #H elim (at_inv_true … H) -H *
[ #H destruct
| #i0 #j0 #H1 #H2 destruct //
]
qed-.

lemma at_inv_true_O_S: ∀cs,j. @⦃0, Ⓣ @ cs⦄ ≡ ⫯j → ⊥.
#cs #j #H elim (at_inv_true … H) -H *
[ #_ #H destruct
| #i0 #j0 #H1 destruct
]
qed-.

lemma at_inv_true_S_O: ∀cs,i. @⦃⫯i, Ⓣ @ cs⦄ ≡ 0 → ⊥.
#cs #i #H elim (at_inv_true … H) -H *
[ #H destruct
| #i0 #j0 #_ #H1 destruct
]
qed-.

fact at_inv_false_aux: ∀cs,i,j. @⦃i, cs⦄ ≡ j → ∀tl. cs = Ⓕ @ tl →
                       ∃∃j0. j = ⫯j0 & @⦃i, tl⦄ ≡ j0.
#cs #i #j * -cs -i -j
#cs [2,3: #i #j #Hij ] #tl #H destruct
/2 width=3 by ex2_intro/
qed-.

lemma at_inv_false: ∀cs,i,j. @⦃i, Ⓕ @ cs⦄ ≡ j →
                    ∃∃j0. j = ⫯j0 & @⦃i, cs⦄ ≡ j0.
/2 width=3 by at_inv_false_aux/ qed-.

lemma at_inv_false_S: ∀cs,i,j. @⦃i, Ⓕ @ cs⦄ ≡ ⫯j → @⦃i, cs⦄ ≡ j.
#cs #i #j #H elim (at_inv_false … H) -H
#j0 #H destruct //
qed-.

lemma at_inv_false_O: ∀cs,i. @⦃i, Ⓕ @ cs⦄ ≡ 0 → ⊥.
#cs #i #H elim (at_inv_false … H) -H
#j0 #H destruct
qed-.

(* Basic properties *********************************************************)

lemma at_monotonic: ∀cs,i2,j2. @⦃i2, cs⦄ ≡ j2 → ∀i1. i1 < i2 →
                    ∃∃j1. @⦃i1, cs⦄ ≡ j1 & j1 < j2.
#cs #i2 #j2 #H elim H -cs -i2 -j2
[ #cs #i1 #H elim (lt_zero_false … H)
| #cs #i #j #Hij #IH * /2 width=3 by ex2_intro, at_zero/
  #i1 #H lapply (lt_S_S_to_lt … H) -H
  #H elim (IH … H) -i
  #j1 #Hij1 #H /3 width=3 by le_S_S, ex2_intro, at_succ/
| #cs #i #j #_ #IH #i1 #H elim (IH … H) -i
  /3 width=3 by le_S_S, ex2_intro, at_false/
]
qed-.

lemma at_at_dec: ∀cs,i,j. Decidable (@⦃i, cs⦄ ≡ j).
#cs elim cs -cs [ | * #cs #IH ]
[ /3 width=3 by at_inv_empty, or_intror/
| * [2: #i ] * [2,4: #j ]
  [ elim (IH i j) -IH
    /4 width=1 by at_inv_true_succ, at_succ, or_introl, or_intror/
  | -IH /3 width=3 by at_inv_true_O_S, or_intror/
  | -IH /3 width=3 by at_inv_true_S_O, or_intror/
  | -IH /2 width=1 by or_introl, at_zero/
  ]
| #i * [2: #j ]
  [ elim (IH i j) -IH
    /4 width=1 by at_inv_false_S, at_false, or_introl, or_intror/
  | -IH /3 width=3 by at_inv_false_O, or_intror/
  ]
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma at_increasing: ∀cs,i,j. @⦃i, cs⦄ ≡ j → i ≤ j.
#cs #i elim i -i //
#i0 #IHi #j #H elim (at_monotonic … H i0) -H
/3 width=3 by le_to_lt_to_lt/
qed-.

lemma at_length_lt: ∀cs,i,j. @⦃i, cs⦄ ≡ j → j < |cs|.
#cs elim cs -cs [ | * #cs #IH ] #i #j #H normalize
[ elim (at_inv_empty … H)
| elim (at_inv_true … H) * -H //
  #i0 #j0 #H1 #H2 #Hij0 destruct /3 width=2 by le_S_S/
| elim (at_inv_false … H) -H
  #j0 #H #H0 destruct /3 width=2 by le_S_S/
]
qed-.

(* Main properties **********************************************************)

theorem at_mono: ∀cs,i,j1. @⦃i, cs⦄ ≡ j1 → ∀j2. @⦃i, cs⦄ ≡ j2 → j1 = j2.
#cs #i #j1 #H elim H -cs -i -j1
#cs [ |2,3: #i #j1 #_ #IH ] #j2 #H
[ lapply (at_inv_true_zero_sn … H) -H //
| elim (at_inv_true_succ_sn … H) -H
  #j0 #H destruct #H >(IH … H) -cs -i -j1 //
| elim (at_inv_false … H) -H
  #j0 #H destruct #H >(IH … H) -cs -i -j1 //
]
qed-.

theorem at_inj: ∀cs,i1,j. @⦃i1, cs⦄ ≡ j → ∀i2. @⦃i2, cs⦄ ≡ j → i1 = i2.
#cs #i1 #j #H elim H -cs -i1 -j
#cs [ |2,3: #i1 #j #_ #IH ] #i2 #H
[ lapply (at_inv_true_zero_dx … H) -H //
| elim (at_inv_true_succ_dx … H) -H
  #i0 #H destruct #H >(IH … H) -cs -i1 -j //
| elim (at_inv_false … H) -H
  #j0 #H destruct #H >(IH … H) -cs -i1 -j0 //
]
qed-.
