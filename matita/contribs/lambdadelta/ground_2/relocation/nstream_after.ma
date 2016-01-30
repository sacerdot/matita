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
include "ground_2/lib/streams_hdtl.ma".
include "ground_2/relocation/nstream_at.ma".

(* RELOCATION N-STREAM ******************************************************)

let corec compose: rtmap → rtmap → rtmap ≝ ?.
#f1 * #b2 #f2 @(seq … (f1@❴b2❵)) @(compose ? f2) -compose -f2
@(tln … (⫯b2) f1)
qed.

interpretation "functional composition (nstream)"
   'compose f1 f2 = (compose f1 f2).

coinductive after: relation3 rtmap rtmap rtmap ≝
| after_zero: ∀f1,f2,f,b1,b2,b.
              after f1 f2 f →
              b1 = 0 → b2 = 0 → b = 0 →
              after (b1@f1) (b2@f2) (b@f)
| after_skip: ∀f1,f2,f,b1,b2,b,a2,a.
              after f1 (a2@f2) (a@f) →
              b1 = 0 → b2 = ⫯a2 → b = ⫯a →
              after (b1@f1) (b2@f2) (b@f)
| after_drop: ∀f1,f2,f,b1,b,a1,a.
              after (a1@f1) f2 (a@f) →
              b1 = ⫯a1 → b = ⫯a →
              after (b1@f1) f2 (b@f)
.

interpretation "relational composition (nstream)"
   'RAfter f1 f2 f = (after f1 f2 f).

(* Basic properies on compose ***********************************************)

lemma compose_unfold: ∀f1,f2,a2. f1∘(a2@f2) = f1@❴a2❵@tln … (⫯a2) f1∘f2.
#f1 #f2 #a2 >(stream_expand … (f1∘(a2@f2))) normalize //
qed.

lemma compose_drop: ∀f1,f2,f,a1,a. (a1@f1)∘f2 = a@f → (⫯a1@f1)∘f2 = ⫯a@f.
#f1 * #a2 #f2 #f #a1 #a >compose_unfold >compose_unfold
#H destruct normalize //
qed.

(* Basic inversion lemmas on compose ****************************************)

lemma compose_inv_unfold: ∀f1,f2,f,a2,a. f1∘(a2@f2) = a@f →
                          f1@❴a2❵ = a ∧ tln … (⫯a2) f1∘f2 = f.
#f1 #f2 #f #a2 #a >(stream_expand … (f1∘(a2@f2))) normalize
#H destruct /2 width=1 by conj/
qed-.

lemma compose_inv_O2: ∀f1,f2,f,a1,a. (a1@f1)∘(O@f2) = a@f →
                      a = a1 ∧ f1∘f2 = f.
#f1 #f2 #f #a1 #a >compose_unfold
#H destruct /2 width=1 by conj/
qed-.

lemma compose_inv_S2: ∀f1,f2,f,a1,a2,a. (a1@f1)∘(⫯a2@f2) = a@f →
                      a = ⫯(a1+f1@❴a2❵) ∧ f1∘(a2@f2) = f1@❴a2❵@f.
#f1 #f2 #f #a1 #a2 #a >compose_unfold
#H destruct /2 width=1 by conj/
qed-.

lemma compose_inv_S1: ∀f1,f2,f,a1,a2,a. (⫯a1@f1)∘(a2@f2) = a@f →
                      a = ⫯((a1@f1)@❴a2❵) ∧ (a1@f1)∘(a2@f2) = (a1@f1)@❴a2❵@f.
#f1 #f2 #f #a1 #a2 #a >compose_unfold
#H destruct /2 width=1 by conj/
qed-.

(* Basic properties on after ************************************************)

lemma after_O2: ∀f1,f2,f. f1 ⊚ f2 ≡ f →
                ∀b. b@f1 ⊚ O@f2 ≡ b@f.
#f1 #f2 #f #Ht #b elim b -b /2 width=5 by after_drop, after_zero/
qed.

lemma after_S2: ∀f1,f2,f,b2,b. f1 ⊚ b2@f2 ≡ b@f →
                ∀b1. b1@f1 ⊚ ⫯b2@f2 ≡ ⫯(b1+b)@f.
#f1 #f2 #f #b2 #b #Ht #b1 elim b1 -b1 /2 width=5 by after_drop, after_skip/
qed.

lemma after_apply: ∀b2,f1,f2,f. (tln … (⫯b2) f1) ⊚ f2 ≡ f → f1 ⊚ b2@f2 ≡ f1@❴b2❵@f.
#b2 elim b2 -b2
[ * /2 width=1 by after_O2/
| #b2 #IH * /3 width=1 by after_S2/
]
qed-.

let corec after_total_aux: ∀f1,f2,f. f1 ∘ f2 = f → f1 ⊚ f2 ≡ f ≝ ?.
* #a1 #f1 * #a2 #f2 * #a #f cases a1 -a1
[ cases a2 -a2
  [ #H cases (compose_inv_O2 … H) -H
    /3 width=1 by after_zero/
  | #a2 #H cases (compose_inv_S2 … H) -H
    /3 width=5 by after_skip, eq_f/
  ]
| #a1 #H cases (compose_inv_S1 … H) -H
  /3 width=5 by after_drop, eq_f/
]
qed-.

theorem after_total: ∀f2,f1. f1 ⊚ f2 ≡ f1 ∘ f2.
/2 width=1 by after_total_aux/ qed.

(* Basic inversion lemmas on after ******************************************)

fact after_inv_O1_aux: ∀f1,f2,f. f1 ⊚ f2 ≡ f → ∀g1. f1 = 0@g1 →
                       (∃∃g2,g. g1 ⊚ g2 ≡ g & f2 = 0@g2 & f = 0@g) ∨
                       ∃∃g2,g,b2,b. g1 ⊚ b2@g2 ≡ b@g & f2 = ⫯b2@g2 & f = ⫯b@g.
#f1 #f2 #f * -f1 -f2 -f #f1 #f2 #f #b1
[ #b2 #b #Ht #H1 #H2 #H3 #g1 #H destruct /3 width=5 by ex3_2_intro, or_introl/
| #b2 #b #a2 #a #Ht #H1 #H2 #H3 #g1 #H destruct /3 width=7 by ex3_4_intro, or_intror/
| #b #a1 #a #_ #H1 #H3 #g1 #H destruct
]
qed-.

fact after_inv_O1_aux2: ∀f1,f2,f,b1,b2,b. b1@f1 ⊚ b2@f2 ≡ b@f → b1 = 0 →
                        (∧∧ f1 ⊚ f2 ≡ f & b2 = 0 & b = 0) ∨
                        ∃∃a2,a. f1 ⊚ a2@f2 ≡ a@f & b2 = ⫯a2 & b = ⫯a.
#f1 #f2 #f #b1 #b2 #b #Ht #H elim (after_inv_O1_aux … Ht) -Ht [4: // |2: skip ] *
[ #g2 #g #Hu #H1 #H2 destruct /3 width=1 by and3_intro, or_introl/
| #g2 #g #a2 #a #Hu #H1 #H2 destruct /3 width=5 by ex3_2_intro, or_intror/
]
qed-.

lemma after_inv_O1: ∀g1,f2,f. 0@g1 ⊚ f2 ≡ f →
                    (∃∃g2,g. g1 ⊚ g2 ≡ g & f2 = 0@g2 & f = 0@g) ∨
                    ∃∃g2,g,b2,b. g1 ⊚ b2@g2 ≡ b@g & f2 = ⫯b2@g2 & f = ⫯b@g.
/2 width=3 by after_inv_O1_aux/ qed-.

fact after_inv_zero_aux2: ∀f1,f2,f,b1,b2,b. b1@f1 ⊚ b2@f2 ≡ b@f → b1 = 0 → b2 = 0 →
                          f1 ⊚ f2 ≡ f ∧ b = 0.
#f1 #f2 #f #b1 #b2 #b #Ht #H1 #H2 elim (after_inv_O1_aux2 … Ht H1) -Ht -H1 *
[ /2 width=1 by conj/
| #a1 #a2 #_ #H0 destruct
]
qed-.

lemma after_inv_zero: ∀g1,g2,f. 0@g1 ⊚ 0@g2 ≡ f →
                      ∃∃g. g1 ⊚ g2 ≡ g & f = 0@g.
#g1 #g2 #f #H elim (after_inv_O1 … H) -H *
[ #x2 #g #Hu #H1 #H2 destruct /2 width=3 by ex2_intro/
| #x2 #g #a2 #a #Hu #H destruct
]
qed-.

fact after_inv_skip_aux2: ∀f1,f2,f,b1,b2,b. b1@f1 ⊚ b2@f2 ≡ b@f → b1 = 0 → ∀a2. b2 = ⫯a2 →
                          ∃∃a. f1 ⊚ a2@f2 ≡ a@f & b = ⫯a.
#f1 #f2 #f #b1 #b2 #b #Ht #H1 #a2 #H2 elim (after_inv_O1_aux2 … Ht H1) -Ht -H1 *
[ #_ #H0 destruct
| #x2 #x #H #H0 #H1 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma after_inv_skip: ∀g1,g2,f,b2. 0@g1 ⊚ ⫯b2@g2 ≡ f →
                      ∃∃g,b. g1 ⊚ b2@g2 ≡ b@g & f = ⫯b@g.
#g1 #g2 * #b #f #b2 #Ht elim (after_inv_skip_aux2 … Ht) [2,4: // |3: skip ] -Ht
#a #Ht #H destruct /2 width=4 by ex2_2_intro/
qed-.

fact after_inv_S1_aux: ∀f1,f2,f. f1 ⊚ f2 ≡ f → ∀g1,b1. f1 = ⫯b1@g1 →
                       ∃∃g,b. b1@g1 ⊚ f2 ≡ b@g & f = ⫯b@g.
#f1 #f2 #f * -f1 -f2 -f #f1 #f2 #f #b1
[ #b2 #b #_ #H1 #H2 #H3 #g1 #a1 #H destruct
| #b2 #b #a2 #a #_ #H1 #H2 #H3 #g1 #a1 #H destruct
| #b #a1 #a #Ht #H1 #H3 #g1 #x1 #H destruct /2 width=4 by ex2_2_intro/
]
qed-.

fact after_inv_S1_aux2: ∀f1,f2,f,b1,b. b1@f1 ⊚ f2 ≡ b@f → ∀a1. b1 = ⫯a1 →
                        ∃∃a. a1@f1 ⊚ f2 ≡ a@f & b = ⫯a.
#f1 #f2 #f #b1 #b #Ht #a #H elim (after_inv_S1_aux … Ht) -Ht [4: // |2,3: skip ]
#g #x #Hu #H0 destruct /2 width=3 by ex2_intro/ 
qed-.

lemma after_inv_S1: ∀g1,f2,f,b1. ⫯b1@g1 ⊚ f2 ≡ f →
                    ∃∃g,b. b1@g1 ⊚ f2 ≡ b@g & f = ⫯b@g.
/2 width=3 by after_inv_S1_aux/ qed-.

fact after_inv_drop_aux2: ∀f1,f2,f,a1,a. a1@f1 ⊚ f2 ≡ a@f → ∀b1,b. a1 = ⫯b1 → a = ⫯b →
                          b1@f1 ⊚ f2 ≡ b@f.
#f1 #f2 #f #a1 #a #Ht #b1 #b #H1 #H elim (after_inv_S1_aux2 … Ht … H1) -a1
#x #Ht #Hx destruct //
qed-.

lemma after_inv_drop: ∀f1,f2,f,b1,b. ⫯b1@f1 ⊚ f2 ≡ ⫯b@f → b1@f1 ⊚ f2 ≡ b@f.
/2 width=5 by after_inv_drop_aux2/ qed-.

fact after_inv_O3_aux1: ∀f1,f2,f. f1 ⊚ f2 ≡ f → ∀g. f = 0@g →
                        ∃∃g1,g2. g1 ⊚ g2 ≡ g & f1 = 0@g1 & f2 = 0@g2.
#f1 #f2 #f * -f1 -f2 -f #f1 #f2 #f #b1
[ #b2 #b #Ht #H1 #H2 #H3 #g #H destruct /2 width=5 by ex3_2_intro/
| #b2 #b #a2 #a #_ #H1 #H2 #H3 #g #H destruct
| #b #a1 #a #_ #H1 #H3 #g #H destruct
]
qed-.

fact after_inv_O3_aux2: ∀f1,f2,f,b1,b2,b. b1@f1 ⊚ b2@f2 ≡ b@f → b = 0 →
                        ∧∧ f1 ⊚ f2 ≡ f & b1 = 0 & b2 = 0.
#f1 #f2 #f #b1 #b2 #b #Ht #H1 elim (after_inv_O3_aux1 … Ht) [2: // |3: skip ] -b
#g1 #g2 #Ht #H1 #H2 destruct /2 width=1 by and3_intro/
qed-.

lemma after_inv_O3: ∀f1,f2,g. f1 ⊚ f2 ≡ 0@g →
                    ∃∃g1,g2. g1 ⊚ g2 ≡ g & f1 = 0@g1 & f2 = 0@g2.
/2 width=3 by after_inv_O3_aux1/ qed-.

fact after_inv_S3_aux1: ∀f1,f2,f. f1 ⊚ f2 ≡ f → ∀g,b. f = ⫯b@g →
                        (∃∃g1,g2,b2. g1 ⊚ b2@g2 ≡ b@g & f1 = 0@g1 & f2 = ⫯b2@g2) ∨
                        ∃∃g1,b1. b1@g1 ⊚ f2 ≡ b@g & f1 = ⫯b1@g1.
#f1 #f2 #f * -f1 -f2 -f #f1 #f2 #f #b1
[ #b2 #b #_ #H1 #H2 #H3 #g #a #H destruct
| #b2 #b #a2 #a #HT #H1 #H2 #H3 #g #x #H destruct /3 width=6 by ex3_3_intro, or_introl/
| #b #a1 #a #HT #H1 #H3 #g #x #H destruct /3 width=4 by ex2_2_intro, or_intror/
]
qed-.

fact after_inv_S3_aux2: ∀f1,f2,f,a1,a2,a. a1@f1 ⊚ a2@f2 ≡ a@f → ∀b. a = ⫯b →
                        (∃∃b2. f1 ⊚ b2@f2 ≡ b@f & a1 = 0 & a2 = ⫯b2) ∨
                        ∃∃b1. b1@f1 ⊚ a2@f2 ≡ b@f & a1 = ⫯b1.
#f1 #f2 #f #a1 #a2 #a #Ht #b #H elim (after_inv_S3_aux1 … Ht) [3: // |4,5: skip ] -a *
[ #g1 #g2 #b2 #Ht #H1 #H2 destruct /3 width=3 by ex3_intro, or_introl/
| #g1 #b1 #Ht #H1 destruct /3 width=3 by ex2_intro, or_intror/
]
qed-.

lemma after_inv_S3: ∀f1,f2,g,b. f1 ⊚ f2 ≡ ⫯b@g →
                    (∃∃g1,g2,b2. g1 ⊚ b2@g2 ≡ b@g & f1 = 0@g1 & f2 = ⫯b2@g2) ∨
                    ∃∃g1,b1. b1@g1 ⊚ f2 ≡ b@g & f1 = ⫯b1@g1.
/2 width=3 by after_inv_S3_aux1/ qed-.

(* Advanced inversion lemmas on after ***************************************)

fact after_inv_O2_aux2: ∀f1,f2,f,a1,a2,a. a1@f1 ⊚ a2@f2 ≡ a@f → a2 = 0 →
                         a1 = a ∧ f1 ⊚ f2 ≡ f.
#f1 #f2 #f #a1 #a2 elim a1 -a1
[ #a #H #H2 elim (after_inv_zero_aux2 … H … H2) -a2 /2 width=1 by conj/
| #a1 #IH #a #H #H2 elim (after_inv_S1_aux2 … H) -H [3: // |2: skip ]
  #b #H #H1 elim (IH … H) // -a2
  #H2 destruct /2 width=1 by conj/
]
qed-.

lemma after_inv_O2: ∀f1,g2,f. f1 ⊚ 0@g2 ≡ f →
                    ∃∃g1,g,a. f1 = a@g1 & f = a@g & g1 ⊚ g2 ≡ g.
* #a1 #f1 #f2 * #a #f #H elim (after_inv_O2_aux2 … H) -H //
/2 width=6 by ex3_3_intro/
qed-.

lemma after_inv_const: ∀a,f1,b2,g2,f. a@f1 ⊚ b2@g2 ≡ a@f → b2 = 0.
#a elim a -a
[ #f1 #b2 #g2 #f #H elim (after_inv_O3 … H) -H
  #g1 #x2 #_ #_ #H destruct //
| #a #IH #f1 #b2 #g2 #f #H elim (after_inv_S1 … H) -H
  #x #b #Hx #H destruct >(IH … Hx) -f1 -g2 -x -b2 -b //
]
qed-.

lemma after_inv_S2: ∀f1,f2,f,a1,a2,a. a1@f1 ⊚ ⫯a2@f2 ≡ a@f → ∀b. a = ⫯(a1+b) →
                    f1 ⊚ a2@f2 ≡ b@f.
#f1 #f2 #f #a1 elim a1 -a1
[ #a2 #a #Ht #b #Hb
  elim (after_inv_skip_aux2 … Ht) -Ht [3,4: // |2: skip ]
  #c #Ht #Hc destruct //
| #a1 #IH #a2 #a #Ht #b #Hb
  lapply (after_inv_drop_aux2 … Ht … Hb) -a [ // | skip ]
  /2 width=3 by/
]
qed-.

(* Forward lemmas on application ********************************************)

lemma after_at_fwd: ∀f,i1,i. @⦃i1, f⦄ ≡ i → ∀f2,f1. f2 ⊚ f1 ≡ f →
                    ∃∃i2. @⦃i1, f1⦄ ≡ i2 & @⦃i2, f2⦄ ≡ i.
#f #i1 #i #H elim H -f -i1 -i
[ #f #f2 #f1 #H elim (after_inv_O3 … H) -H
  /2 width=3 by at_zero, ex2_intro/
| #f #i1 #i #_ #IH #f2 #f1 #H elim (after_inv_O3 … H) -H
  #g2 #g1 #Hu #H1 #H2 destruct elim (IH … Hu) -f
  /3 width=3 by at_S1, ex2_intro/
| #f #b #i1 #i #_ #IH #f2 #f1 #H elim (after_inv_S3 … H) -H *
  [ #g2 #g1 #b2 #Hu #H1 #H2 destruct elim (IH … Hu) -f -b
    /3 width=3 by at_S1, at_lift, ex2_intro/
  | #g1 #b1 #Hu #H destruct elim (IH … Hu) -f -b
    /3 width=3 by at_lift, ex2_intro/
  ]
]
qed-.

lemma after_at1_fwd: ∀f1,i1,i2. @⦃i1, f1⦄ ≡ i2 → ∀f2,f. f2 ⊚ f1 ≡ f →
                     ∃∃i. @⦃i2, f2⦄ ≡ i & @⦃i1, f⦄ ≡ i.
#f1 #i1 #i2 #H elim H -f1 -i1 -i2
[ #f1 #f2 #f #H elim (after_inv_O2 … H) -H /2 width=3 by ex2_intro/
| #f1 #i1 #i2 #_ #IH * #b2 elim b2 -b2
  [ #f2 #f #H elim (after_inv_zero … H) -H
    #g #Hu #H destruct elim (IH … Hu) -f1
    /3 width=3 by at_S1, at_skip, ex2_intro/
  | -IH #b2 #IH #f2 #f #H elim (after_inv_S1 … H) -H
    #g #b #Hu #H destruct elim (IH … Hu) -f1
    /3 width=3 by at_lift, ex2_intro/
  ]
| #f1 #b1 #i1 #i2 #_ #IH * #b2 elim b2 -b2
  [ #f2 #f #H elim (after_inv_skip … H) -H
    #g #a #Hu #H destruct elim (IH … Hu) -f1 -b1
    /3 width=3 by at_S1, at_lift, ex2_intro/
  | -IH #b2 #IH #f2 #f #H elim (after_inv_S1 … H) -H
    #g #b #Hu #H destruct elim (IH … Hu) -f1 -b1
    /3 width=3 by at_lift, ex2_intro/
  ]
]
qed-.

lemma after_fwd_at: ∀f1,f2,i1,i2,i. @⦃i1, f1⦄ ≡ i2 → @⦃i2, f2⦄ ≡ i →
                    ∀f. f2 ⊚ f1 ≡ f → @⦃i1, f⦄ ≡ i.
#f1 #f2 #i1 #i2 #i #Hi1 #Hi2 #f #Ht elim (after_at1_fwd … Hi1 … Ht) -f1
#j #H #Hj >(at_mono … H … Hi2) -i2 //
qed-.

lemma after_fwd_at1: ∀f2,f,i1,i2,i. @⦃i1, f⦄ ≡ i → @⦃i2, f2⦄ ≡ i →
                     ∀f1. f2 ⊚ f1 ≡ f → @⦃i1, f1⦄ ≡ i2.
#f2 #f #i1 #i2 #i #Hi1 #Hi2 #f1 #Ht elim (after_at_fwd … Hi1 … Ht) -f
#j1 #Hij1 #H >(at_inj … Hi2 … H) -i //
qed-.

lemma after_fwd_at2: ∀f,i1,i. @⦃i1, f⦄ ≡ i → ∀f1,i2. @⦃i1, f1⦄ ≡ i2 →
                     ∀f2. f2 ⊚ f1 ≡ f → @⦃i2, f2⦄ ≡ i.
#f #i1 #i #H elim H -f -i1 -i
[ #f #f1 #i2 #Ht1 #f2 #H elim (after_inv_O3 … H) -H
  #g2 #g1 #_ #H1 #H2 destruct >(at_inv_OOx … Ht1) -f -g1 -i2 //
| #f #i1 #i #_ #IH #f1 #i2 #Ht1 #f2 #H elim (after_inv_O3 … H) -H
  #g2 #g1 #Hu #H1 #H2 destruct elim (at_inv_SOx … Ht1) -Ht1
  /3 width=3 by at_skip/
| #f #b #i1 #i #_ #IH #f1 #i2 #Ht1 #f2 #H elim (after_inv_S3 … H) -H *
  [ #g2 #g1 #a1 #Hu #H1 #H2 destruct elim (at_inv_xSx … Ht1) -Ht1
    /3 width=3 by at_skip/
  | #g2 #a2 #Hu #H destruct /3 width=3 by at_lift/
  ]
]
qed-.

(* Advanced forward lemmas on after *****************************************)

lemma after_fwd_hd: ∀f1,f2,f,a2,a. f1 ⊚ a2@f2 ≡ a@f → a = f1@❴a2❵.
#f1 #f2 #f #a2 #a #Ht lapply (after_fwd_at … 0 … Ht) -Ht [4: // | // |2,3: skip ]
/3 width=2 by at_inv_O1, sym_eq/
qed-.

lemma after_fwd_tl: ∀f,f2,a2,f1,a1,a. a1@f1 ⊚ a2@f2 ≡ a@f →
                    tln … a2 f1 ⊚ f2 ≡ f.
#f #f2 #a2 elim a2 -a2
[ #f1 #a1 #a #Ht elim (after_inv_O2_aux2 … Ht) -Ht //
| #a2 #IH * #b1 #f1 #a1 #a #Ht
  lapply (after_fwd_hd … Ht) #Ha
  lapply (after_inv_S2 … Ht … Ha) -a
  /2 width=3 by/
]
qed-.

lemma after_inv_apply: ∀f1,f2,f,a1,a2,a. a1@f1 ⊚ a2@f2 ≡ a@f →
                       a = (a1@f1)@❴a2❵ ∧ tln … a2 f1 ⊚ f2 ≡ f.
/3 width=3 by  after_fwd_tl, after_fwd_hd, conj/ qed-.

(* Main properties on after *************************************************)

let corec after_trans1: ∀f1,f2,f0. f1 ⊚ f2 ≡ f0 →
                        ∀f3,f4. f0 ⊚ f3 ≡ f4 →
                        ∀f. f2 ⊚ f3 ≡ f → f1 ⊚ f ≡ f4 ≝ ?.
#f1 #f2 #f0 * -f1 -f2 -f0 #f1 #f2 #f0 #b1 [1,2: #b2 ] #b0
[ #Ht0 #H1 #H2 #H0 * #b3 #f3 * #b4 #f4 #Ht4 * #b #f #Ht
  cases (after_inv_O1_aux2 … Ht4 H0) -Ht4 -H0 *
  [ #Ht4 #H3 #H4 cases (after_inv_zero_aux2 … Ht H2 H3) -Ht -H2 -H3
    #Ht #H /3 width=6 by after_zero/
  | #a0 #a4 #Ht4 #H3 #H4 cases (after_inv_skip_aux2 … Ht H2 … H3) -Ht -H2 -H3
    #a #Ht3 #H /3 width=6 by after_skip/
  ]
| #a2 #a0 #Ht0 #H1 #H2 #H0 #f3 * #b4 #f4 #Ht4 cases (after_inv_S1_aux2 … Ht4 … H0) -Ht4 -H0
  #a4 #Ht4 #H4 * #b #f #H cases (after_inv_S1_aux2 … H … H2) -H -H2
  #a #Ht3 #H /3 width=6 by after_skip/
| #a1 #a0 #Ht0 #H1 #H0 #f3 * #b4 #f4 #Ht4 cases (after_inv_S1_aux2 … Ht4 … H0) -Ht4 -H0
  #a4 #Ht4 #H4 * #b #f #Ht /3 width=6 by after_drop/
]
qed-.

let corec after_trans2: ∀f1,f0,f4. f1 ⊚ f0 ≡ f4 →
                        ∀f2, f3. f2 ⊚ f3 ≡ f0 →
                        ∀f. f1 ⊚ f2 ≡ f → f ⊚ f3 ≡ f4 ≝ ?.
#f1 #f0 #f4 * -f1 -f0 -f4 #f1 #f0 #f4 #b1 [1,2: #b0 ] #b4
[ #Ht4 #H1 #H0 #H4 * #b2 #f2 * #b3 #f3 #Ht0 * #b #f #Ht
  cases (after_inv_O3_aux2 … Ht0 H0) -b0
  #Ht0 #H2 #H3 cases (after_inv_zero_aux2 … Ht H1 H2) -b1 -b2
  #Ht #H /3 width=6 by after_zero/
| #a0 #a4 #Ht4 #H1 #H0 #H4 * #b2 #f2 * #b3 #f3 #Ht0 * #b #f #Ht
  cases (after_inv_S3_aux2 … Ht0 … H0) -b0 *
  [ #a3 #Ht0 #H2 #H3 cases (after_inv_zero_aux2 … Ht H1 H2) -b1 -b2
    #Ht #H /3 width=6 by after_skip/
  | #a2 #Ht0 #H2 cases (after_inv_skip_aux2 … Ht H1 … H2) -b1 -b2
    #a #Ht #H /3 width=6 by after_drop/
  ]
| #a1 #a4 #Ht4 #H1 #H4 * #b2 #f2 * #b3 #f3 #Ht0 * #b #f #Ht
  cases (after_inv_S1_aux2 … Ht … H1) -b1
  #a #Ht #H /3 width=6 by after_drop/
]
qed-.

let corec after_mono: ∀f1,f2,x. f1 ⊚ f2 ≡ x → ∀y. f1 ⊚ f2 ≡ y → x ≐ y ≝ ?.
* #a1 #f1 * #a2 #f2 * #c #x #Hx * #d #y #Hy
cases (after_inv_apply … Hx) -Hx #Hc #Hx
cases (after_inv_apply … Hy) -Hy #Hd #Hy
/3 width=4 by eq_seq/
qed-.

let corec after_inj: ∀f1,x,f. f1 ⊚ x ≡ f → ∀y. f1 ⊚ y ≡ f → x ≐ y ≝ ?.
* #a1 #f1 * #c #x * #a #f #Hx * #d #y #Hy
cases (after_inv_apply … Hx) -Hx #Hc #Hx
cases (after_inv_apply … Hy) -Hy #Hd
cases (apply_inj_aux … Hc Hd) //
#Hy -a -d /3 width=4 by eq_seq/
qed-.

(* Main inversion lemmas on after *******************************************)

theorem after_inv_total: ∀f1,f2,f. f1 ⊚ f2 ≡ f → f1 ∘ f2 ≐ f.
/2 width=4 by after_mono/ qed-.
