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

include "ground_2/notation/relations/rafter_3.ma".
include "ground_2/relocation/trace_at.ma".

(* RELOCATION TRACE *********************************************************)

inductive after: relation3 trace trace trace ≝
   | after_empty: after (◊) (◊) (◊)
   | after_true : ∀cs1,cs2,cs. after cs1 cs2 cs →
                  ∀b. after (Ⓣ @ cs1) (b @ cs2) (b @ cs)
   | after_false: ∀cs1,cs2,cs. after cs1 cs2 cs →
                  after (Ⓕ @ cs1) cs2 (Ⓕ @ cs).

interpretation "composition (trace)"
   'RAfter cs1 cs2 cs = (after cs1 cs2 cs).

(* Basic inversion lemmas ***************************************************)

fact after_inv_empty1_aux: ∀cs1,cs2,cs. cs1 ⊚ cs2 ≡ cs → cs1 = ◊ →
                           cs2 = ◊ ∧ cs = ◊.
#cs1 #cs2 #cs * -cs1 -cs2 -cs
[ /2 width=1 by conj/
| #cs1 #cs2 #cs #_ #b #H destruct
| #cs1 #cs2 #cs #_ #H destruct
]
qed-.

lemma after_inv_empty1: ∀cs2,cs. ◊ ⊚ cs2 ≡ cs → cs2 = ◊ ∧ cs = ◊.
/2 width=3 by after_inv_empty1_aux/ qed-.

fact after_inv_true1_aux: ∀cs1,cs2,cs. cs1 ⊚ cs2 ≡ cs → ∀tl1. cs1 = Ⓣ @ tl1 →
                          ∃∃tl2,tl,b. cs2 = b @ tl2 & cs = b @ tl & tl1 ⊚ tl2 ≡ tl.
#cs1 #cs2 #cs * -cs1 -cs2 -cs
[ #tl1 #H destruct
| #cs1 #cs2 #cs #H12 #b #tl1 #H destruct
  /2 width=6 by ex3_3_intro/
| #cs1 #cs2 #cs #_ #tl1 #H destruct
]
qed-.

lemma after_inv_true1: ∀tl1,cs2,cs. (Ⓣ @ tl1) ⊚ cs2 ≡ cs →
                       ∃∃tl2,tl,b. cs2 = b @ tl2 & cs = b @ tl & tl1 ⊚ tl2 ≡ tl.
/2 width=3 by after_inv_true1_aux/ qed-.

fact after_inv_false1_aux: ∀cs1,cs2,cs. cs1 ⊚ cs2 ≡ cs → ∀tl1. cs1 = Ⓕ @ tl1 →
                           ∃∃tl. cs = Ⓕ @ tl & tl1 ⊚ cs2 ≡ tl.
#cs1 #cs2 #cs * -cs1 -cs2 -cs
[ #tl1 #H destruct
| #cs1 #cs2 #cs #_ #b #tl1 #H destruct
| #cs1 #cs2 #cs #H12 #tl1 #H destruct
  /2 width=3 by ex2_intro/
]
qed-.

lemma after_inv_false1: ∀tl1,cs2,cs. (Ⓕ @ tl1) ⊚ cs2 ≡ cs →
                        ∃∃tl. cs = Ⓕ @ tl & tl1 ⊚ cs2 ≡ tl.
/2 width=3 by after_inv_false1_aux/ qed-.

fact after_inv_empty3_aux: ∀cs1,cs2,cs. cs1 ⊚ cs2 ≡ cs → cs = ◊ →
                           cs1 = ◊ ∧ cs2 = ◊.
#cs1 #cs2 #cs * -cs1 -cs2 -cs
[ /2 width=1 by conj/
| #cs1 #cs2 #cs #_ #b #H destruct
| #cs1 #cs2 #cs #_ #H destruct
]
qed-.

lemma after_inv_empty3: ∀cs1,cs2. cs1 ⊚ cs2 ≡ ◊ → cs1 = ◊ ∧ cs2 = ◊.
/2 width=3 by after_inv_empty3_aux/ qed-.

fact after_inv_inh3_aux: ∀cs1,cs2,cs. cs1 ⊚ cs2 ≡ cs → ∀tl,b. cs = b @ tl →
                         (∃∃tl1,tl2. cs1 = Ⓣ @ tl1 & cs2 = b @ tl2 & tl1 ⊚ tl2 ≡ tl) ∨
                         ∃∃tl1.  cs1 = Ⓕ @ tl1 & b = Ⓕ & tl1 ⊚ cs2 ≡ tl.
#cs1 #cs2 #cs * -cs1 -cs2 -cs
[ #tl #b #H destruct
| #cs1 #cs2 #cs #H12 #b0 #tl #b #H destruct
  /3 width=5 by ex3_2_intro, or_introl/
| #cs1 #cs2 #cs #H12 #tl #b #H destruct
  /3 width=3 by ex3_intro, or_intror/
]
qed-.

lemma after_inv_inh3: ∀cs1,cs2,tl,b. cs1 ⊚ cs2 ≡ b @ tl →
                      (∃∃tl1,tl2. cs1 = Ⓣ @ tl1 & cs2 = b @ tl2 & tl1 ⊚ tl2 ≡ tl) ∨
                      ∃∃tl1.  cs1 = Ⓕ @ tl1 & b = Ⓕ & tl1 ⊚ cs2 ≡ tl.
/2 width=3 by after_inv_inh3_aux/ qed-.

(* Basic forward lemmas *****************************************************)

lemma after_at_fwd: ∀cs1,cs2,cs. cs2 ⊚ cs1 ≡ cs → ∀i1,i. @⦃i1, cs⦄ ≡ i →
                    ∃∃i2. @⦃i1, cs1⦄ ≡ i2 & @⦃i2, cs2⦄ ≡ i.
#cs1 #cs2 #cs #H elim H -cs1 -cs2 -cs
[ #i1 #i #H elim (at_inv_empty … H)
| #cs1 #cs2 #cs #_ * #IH #i1 #i #H
  [ elim (at_inv_true … H) -H *
    [ -IH #H1 #H2 destruct /2 width=3 by at_zero, ex2_intro/
    | #j1 #j #H1 #H2 #Hj1 destruct
      elim (IH … Hj1) -IH -Hj1 /3 width=3 by at_succ, ex2_intro/
    ]
  | elim (at_inv_false … H) -H
    #j #H #Hj destruct
    elim (IH … Hj) -IH -Hj /3 width=3 by at_succ, at_false, ex2_intro/
  ]
| #cs1 #cs2 #cs #_ #IH #i1 #i #H elim (at_inv_false … H) -H
  #j #H #Hj destruct
  elim (IH … Hj) -IH -Hj /3 width=3 by at_false, ex2_intro/
]
qed-.

lemma after_fwd_at: ∀cs1,cs2,cs. cs2 ⊚ cs1 ≡ cs → ∀i1,i2. @⦃i1, cs1⦄ ≡ i2 →
                    ∃∃i. @⦃i2, cs2⦄ ≡ i & @⦃i1, cs⦄ ≡ i.
#cs1 #cs2 #cs #H elim H -cs1 -cs2 -cs
[ #i1 #i2 #H elim (at_inv_empty … H)
| #cs1 #cs2 #cs #_ * #IH #i1 #i2 #H
  [ elim (at_inv_true … H) -H *
    [ -IH #H1 #H2 destruct /2 width=3 by at_zero, ex2_intro/
    | #j1 #j2 #H1 #H2 #Hj12 destruct
      elim (IH … Hj12) -IH -Hj12 /3 width=3 by at_succ, ex2_intro/
    ]
  | elim (at_inv_false … H) -H
    #j2 #H #Hj2 destruct
    elim (IH … Hj2) -IH -Hj2 /3 width=3 by at_succ, at_false, ex2_intro/
  ]
| #cs1 #cs2 #cs #_ #IH #i1 #i2 #H elim (IH … H) -IH -H
  /3 width=3 by at_false, ex2_intro/
]
qed-.

(* Main properties **********************************************************)

theorem after_trans1: ∀cs1,cs2,cs0. cs1 ⊚ cs2 ≡ cs0 →
                      ∀cs3, cs4. cs0 ⊚ cs3 ≡ cs4 →
                      ∃∃cs. cs2 ⊚ cs3 ≡ cs & cs1 ⊚ cs ≡ cs4.
#cs1 #cs2 #cs0 #H elim H -cs1 -cs2 -cs0
[ #cs3 #cs4 #H elim (after_inv_empty1 … H) -H
  #H1 #H2 destruct /2 width=3 by ex2_intro, after_empty/
| #cs1 #cs2 #cs0 #_ * #IH #cs3 #cs4 #H
  [ elim (after_inv_true1 … H) -H
    #tl3 #tl4 #b #H1 #H2 #Htl destruct
    elim (IH … Htl) -cs0
    /3 width=3 by ex2_intro, after_true/
  | elim (after_inv_false1 … H) -H
    #tl4 #H #Htl destruct
    elim (IH … Htl) -cs0
    /3 width=3 by ex2_intro, after_true, after_false/
  ]
| #cs1 #cs2 #cs0 #_ #IH #cs3 #cs4 #H
  elim (after_inv_false1 … H) -H
  #tl4 #H #Htl destruct
  elim (IH … Htl) -cs0
  /3 width=3 by ex2_intro, after_false/
]
qed-.

theorem after_trans2: ∀cs1,cs0,cs4. cs1 ⊚ cs0 ≡ cs4 →
                      ∀cs2, cs3. cs2 ⊚ cs3 ≡ cs0 →
                      ∃∃cs. cs1 ⊚ cs2 ≡ cs & cs ⊚ cs3 ≡ cs4.
#cs1 #cs0 #cs4 #H elim H -cs1 -cs0 -cs4
[ #cs2 #cs3 #H elim (after_inv_empty3 … H) -H
  #H1 #H2 destruct /2 width=3 by ex2_intro, after_empty/
| #cs1 #cs0 #cs4 #_ #b #IH #cs2 #cs3 #H elim (after_inv_inh3 … H) -H *
  [ #tl2 #tl3 #H1 #H2 #Htl destruct
    elim (IH … Htl) -cs0
    /3 width=3 by ex2_intro, after_true/
  | #tl2 #H1 #H2 #Htl destruct
    elim (IH … Htl) -cs0
    /3 width=3 by ex2_intro, after_true, after_false/
  ]
| #cs1 #cs0 #cs4 #_ #IH #cs2 #cs3 #H elim (IH … H) -cs0
  /3 width=3 by ex2_intro, after_false/
]
qed-.

theorem after_mono: ∀cs1,cs2,x. cs1 ⊚ cs2 ≡ x → ∀y. cs1 ⊚ cs2 ≡ y → x = y.
#cs1 #cs2 #x #H elim H -cs1 -cs2 -x
[ #y #H elim (after_inv_empty1 … H) -H //
| #cs1 #cs #x #_ #b #IH #y #H elim (after_inv_true1 … H) -H
  #tl #tly #b0 #H1 #H2 #Htl destruct >(IH … Htl) -tl -cs1 -x //
| #cs1 #cs2 #x #_ #IH #y #H elim (after_inv_false1 … H) -H
  #tly #H #Htl destruct >(IH … Htl) -cs1 -cs2 -x //
]
qed-.

theorem after_inj: ∀cs1,x,cs. cs1 ⊚ x ≡ cs → ∀y. cs1 ⊚ y ≡ cs → x = y.
#cs1 #x #cs #H elim H -cs1 -x -cs
[ #y #H elim (after_inv_empty1 … H) -H //
| #cs1 #x #cs #_ #b #IH #y #H elim (after_inv_true1 … H) -H
  #tly #tl #b0 #H1 #H2 #Htl destruct >(IH … Htl) -tl -cs1 -x //
| #cs1 #x #cs #_ #IH #y #H elim (after_inv_false1 … H) -H
  #tl #H #Htl destruct >(IH … Htl) -tl -cs1 -x //
]
qed-.
