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
   | at_empty: at (◊) 0 0
   | at_zero : ∀cs. at (Ⓣ @ cs) 0 0
   | at_succ : ∀cs,i1,i2. at cs i1 i2 → at (Ⓣ @ cs) (⫯i1) (⫯i2)
   | at_false: ∀cs,i1,i2. at cs i1 i2 → at (Ⓕ @ cs) i1 (⫯i2).

interpretation "relocation (trace)"
   'RAt i1 cs i2 = (at cs i1 i2).

(* Basic inversion lemmas ***************************************************)

fact at_inv_empty_aux: ∀cs,i1,i2. @⦃i1, cs⦄ ≡ i2 → cs = ◊ → i1 = 0 ∧ i2 = 0.
#cs #i1 #i2 * -cs -i1 -i2 /2 width=1 by conj/
#cs #i1 #i2 #_ #H destruct
qed-.

lemma at_inv_empty: ∀i1,i2. @⦃i1, ◊⦄ ≡ i2 → i1 = 0 ∧ i2 = 0.
/2 width=5 by at_inv_empty_aux/ qed-.

lemma at_inv_empty_zero_sn: ∀i. @⦃0, ◊⦄ ≡ i → i = 0.
#i #H elim (at_inv_empty … H) -H //
qed-.

lemma at_inv_empty_zero_dx: ∀i. @⦃i, ◊⦄ ≡ 0 → i = 0.
#i #H elim (at_inv_empty … H) -H //
qed-.

lemma at_inv_empty_succ_sn: ∀i1,i2. @⦃⫯i1, ◊⦄ ≡ i2 → ⊥.
#i1 #i2 #H elim (at_inv_empty … H) -H #H1 #H2 destruct
qed-.

lemma at_inv_empty_succ_dx: ∀i1,i2. @⦃i1, ◊⦄ ≡ ⫯i2 → ⊥.
#i1 #i2 #H elim (at_inv_empty … H) -H #H1 #H2 destruct
qed-.

fact at_inv_true_aux: ∀cs,i1,i2. @⦃i1, cs⦄ ≡ i2 → ∀tl. cs = Ⓣ @ tl →
                      (i1 = 0 ∧ i2 = 0) ∨
                      ∃∃j1,j2. i1 = ⫯j1 & i2 = ⫯j2 & @⦃j1, tl⦄ ≡ j2.
#cs #i1 #i2 * -cs -i1 -i2
[2,3,4: #cs [2,3: #i1 #i2 #Hij ] ] #tl #H destruct
/3 width=5 by ex3_2_intro, or_introl, or_intror, conj/
qed-.

lemma at_inv_true: ∀cs,i1,i2. @⦃i1, Ⓣ @ cs⦄ ≡ i2 →
                   (i1 = 0 ∧ i2 = 0) ∨
                   ∃∃j1,j2. i1 = ⫯j1 & i2 = ⫯j2 & @⦃j1, cs⦄ ≡ j2.
/2 width=3 by at_inv_true_aux/ qed-.

lemma at_inv_true_zero_sn: ∀cs,i. @⦃0, Ⓣ @ cs⦄ ≡ i → i = 0.
#cs #i #H elim (at_inv_true … H) -H * //
#j1 #j2 #H destruct
qed-.

lemma at_inv_true_zero_dx: ∀cs,i. @⦃i, Ⓣ @ cs⦄ ≡ 0 → i = 0.
#cs #i #H elim (at_inv_true … H) -H * //
#j1 #j2 #_ #H destruct
qed-.

lemma at_inv_true_succ_sn: ∀cs,i1,i2. @⦃⫯i1, Ⓣ @ cs⦄ ≡ i2 →
                           ∃∃j2. i2 = ⫯j2 & @⦃i1, cs⦄ ≡ j2.
#cs #i1 #i2 #H elim (at_inv_true … H) -H *
[ #H destruct
| #j1 #j2 #H1 #H2 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma at_inv_true_succ_dx: ∀cs,i1,i2. @⦃i1, Ⓣ @ cs⦄ ≡ ⫯i2 →
                           ∃∃j1. i1 = ⫯j1 & @⦃j1, cs⦄ ≡ i2.
#cs #i1 #i2 #H elim (at_inv_true … H) -H *
[ #_ #H destruct
| #j1 #j2 #H1 #H2 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma at_inv_true_succ: ∀cs,i1,i2. @⦃⫯i1, Ⓣ @ cs⦄ ≡ ⫯i2 →
                        @⦃i1, cs⦄ ≡ i2.
#cs #i1 #i2 #H elim (at_inv_true … H) -H *
[ #H destruct
| #j1 #j2 #H1 #H2 destruct //
]
qed-.

lemma at_inv_true_O_S: ∀cs,i. @⦃0, Ⓣ @ cs⦄ ≡ ⫯i → ⊥.
#cs #i #H elim (at_inv_true … H) -H *
[ #_ #H destruct
| #j1 #j2 #H destruct
]
qed-.

lemma at_inv_true_S_O: ∀cs,i. @⦃⫯i, Ⓣ @ cs⦄ ≡ 0 → ⊥.
#cs #i #H elim (at_inv_true … H) -H *
[ #H destruct
| #j1 #j2 #_ #H destruct
]
qed-.

fact at_inv_false_aux: ∀cs,i1,i2. @⦃i1, cs⦄ ≡ i2 → ∀tl. cs = Ⓕ @ tl →
                       ∃∃j2. i2 = ⫯j2 & @⦃i1, tl⦄ ≡ j2.
#cs #i1 #i2 * -cs -i1 -i2
[2,3,4: #cs [2,3: #i1 #i2 #Hij ] ] #tl #H destruct
/2 width=3 by ex2_intro/
qed-.

lemma at_inv_false: ∀cs,i1,i2. @⦃i1, Ⓕ @ cs⦄ ≡ i2 →
                    ∃∃j2. i2 = ⫯j2 & @⦃i1, cs⦄ ≡ j2.
/2 width=3 by at_inv_false_aux/ qed-.

lemma at_inv_false_S: ∀cs,i1,i2. @⦃i1, Ⓕ @ cs⦄ ≡ ⫯i2 → @⦃i1, cs⦄ ≡ i2.
#cs #i1 #i2 #H elim (at_inv_false … H) -H
#j2 #H destruct //
qed-.

lemma at_inv_false_O: ∀cs,i. @⦃i, Ⓕ @ cs⦄ ≡ 0 → ⊥.
#cs #i #H elim (at_inv_false … H) -H
#j2 #H destruct
qed-.

lemma at_inv_le: ∀cs,i1,i2. @⦃i1, cs⦄ ≡ i2 → i1 ≤ ∥cs∥ ∧ i2 ≤ |cs|.
#cs #i1 #i2 #H elim H -cs -i1 -i2 /2 width=1 by conj/
#cs #i1 #i2 #_ * /3 width=1 by le_S_S, conj/ 
qed-.

lemma at_inv_gt1: ∀cs,i1,i2. @⦃i1, cs⦄ ≡ i2 → ∥cs∥ < i1 → ⊥.
#cs #i1 #i2 #H elim (at_inv_le … H) -H /2 width=4 by lt_le_false/
qed-.

lemma at_inv_gt2: ∀cs,i1,i2. @⦃i1, cs⦄ ≡ i2 → |cs| < i2 → ⊥.
#cs #i1 #i2 #H elim (at_inv_le … H) -H /2 width=4 by lt_le_false/
qed-.

(* Basic properties *********************************************************)

(* Note: lemma 250 *)
lemma at_le: ∀cs,i1. i1 ≤ ∥cs∥ →
             ∃∃i2. @⦃i1, cs⦄ ≡ i2 & i2 ≤ |cs|.
#cs elim cs -cs
[ #i1 #H <(le_n_O_to_eq … H) -i1 /2 width=3 by at_empty, ex2_intro/
| * #cs #IH
  [ * /2 width=3 by at_zero, ex2_intro/
    #i1 #H lapply (le_S_S_to_le … H) -H
    #H elim (IH … H) -IH -H /3 width=3 by at_succ, le_S_S, ex2_intro/
  | #i1 #H elim (IH … H) -IH -H /3 width=3 by at_false, le_S_S, ex2_intro/
  ]
]
qed-.

lemma at_top: ∀cs. @⦃∥cs∥, cs⦄ ≡ |cs|.
#cs elim cs -cs // * /2 width=1 by at_succ, at_false/
qed. 

lemma at_monotonic: ∀cs,i1,i2. @⦃i1, cs⦄ ≡ i2 → ∀j1. j1 < i1 →
                    ∃∃j2. @⦃j1, cs⦄ ≡ j2 & j2 < i2.
#cs #i1 #i2 #H elim H -cs -i1 -i2
[ #j1 #H elim (lt_zero_false … H)
| #cs #j1 #H elim (lt_zero_false … H)
| #cs #i1 #i2 #Hij #IH * /2 width=3 by ex2_intro, at_zero/
  #j1 #H lapply (lt_S_S_to_lt … H) -H
  #H elim (IH … H) -i1
  #j2 #Hj12 #H /3 width=3 by le_S_S, ex2_intro, at_succ/
| #cs #i1 #i2 #_ #IH #j1 #H elim (IH … H) -i1
  /3 width=3 by le_S_S, ex2_intro, at_false/
]
qed-.

lemma at_dec: ∀cs,i1,i2. Decidable (@⦃i1, cs⦄ ≡ i2).
#cs elim cs -cs [ | * #cs #IH ]
[ * [2: #i1 ] * [2,4: #i2 ]
  [4: /2 width=1 by at_empty, or_introl/
  |*: @or_intror #H elim (at_inv_empty … H) #H1 #H2 destruct  
  ]
| * [2: #i1 ] * [2,4: #i2 ]
  [ elim (IH i1 i2) -IH
    /4 width=1 by at_inv_true_succ, at_succ, or_introl, or_intror/
  | -IH /3 width=3 by at_inv_true_O_S, or_intror/
  | -IH /3 width=3 by at_inv_true_S_O, or_intror/
  | -IH /2 width=1 by or_introl, at_zero/
  ]
| #i1 * [2: #i2 ]
  [ elim (IH i1 i2) -IH
    /4 width=1 by at_inv_false_S, at_false, or_introl, or_intror/
  | -IH /3 width=3 by at_inv_false_O, or_intror/
  ]
]
qed-.

lemma is_at_dec: ∀cs,i2. Decidable (∃i1. @⦃i1, cs⦄ ≡ i2).
#cs elim cs -cs
[ * /3 width=2 by ex_intro, or_introl/
  #i2 @or_intror * /2 width=3 by at_inv_empty_succ_dx/
| * #cs #IH * [2,4: #i2 ]
  [ elim (IH i2) -IH
    [ * /4 width=2 by at_succ, ex_intro, or_introl/
    | #H @or_intror * #x #Hx
      elim (at_inv_true_succ_dx … Hx) -Hx
      /3 width=2 by ex_intro/
    ]
  | elim (IH i2) -IH
    [ * /4 width=2 by at_false, ex_intro, or_introl/
    | #H @or_intror * /4 width=2 by at_inv_false_S, ex_intro/ 
    ]
  | /3 width=2 by at_zero, ex_intro, or_introl/
  | @or_intror * /2 width=3 by at_inv_false_O/
  ]
]
qed-.

(* Basic forward lemmas *****************************************************)

lemma at_increasing: ∀cs,i1,i2. @⦃i1, cs⦄ ≡ i2 → i1 ≤ i2.
#cs #i1 elim i1 -i1 //
#j1 #IHi #i2 #H elim (at_monotonic … H j1) -H
/3 width=3 by le_to_lt_to_lt/
qed-.

lemma at_increasing_strict: ∀cs,i1,i2. @⦃i1, Ⓕ @ cs⦄ ≡ i2 →
                            i1 < i2 ∧ @⦃i1, cs⦄ ≡ ⫰i2.
#cs #i1 #i2 #H elim (at_inv_false … H) -H
#j2 #H #Hj2 destruct /4 width=2 by conj, at_increasing, le_S_S/
qed-.

(* Main properties **********************************************************)

theorem at_mono: ∀cs,i,i1. @⦃i, cs⦄ ≡ i1 → ∀i2. @⦃i, cs⦄ ≡ i2 → i1 = i2.
#cs #i #i1 #H elim H -cs -i -i1
[2,3,4: #cs [2,3: #i #i1 #_ #IH ] ] #i2 #H
[ elim (at_inv_true_succ_sn … H) -H
  #j2 #H destruct #H >(IH … H) -cs -i -i1 //
| elim (at_inv_false … H) -H
  #j2 #H destruct #H >(IH … H) -cs -i -i1 //
| /2 width=2 by at_inv_true_zero_sn/
| /2 width=1 by at_inv_empty_zero_sn/
]
qed-.

theorem at_inj: ∀cs,i1,i. @⦃i1, cs⦄ ≡ i → ∀i2. @⦃i2, cs⦄ ≡ i → i1 = i2.
#cs #i1 #i #H elim H -cs -i1 -i
[2,3,4: #cs [ |2,3: #i1 #i #_ #IH ] ] #i2 #H
[ /2 width=2 by at_inv_true_zero_dx/
| elim (at_inv_true_succ_dx … H) -H
  #j2 #H destruct #H >(IH … H) -cs -i1 -i //
| elim (at_inv_false … H) -H
  #j #H destruct #H >(IH … H) -cs -i1 -j //
| /2 width=1 by at_inv_empty_zero_dx/
]
qed-.
