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

let corec compose: nstream → nstream → nstream ≝ ?.
#t1 * #b2 #t2 @(seq … (t1@❴b2❵)) @(compose ? t2) -compose -t2
@(tln … (⫯b2) t1)
qed.

interpretation "functional composition (nstream)"
   'compose t1 t2 = (compose t1 t2).

coinductive after: relation3 nstream nstream nstream ≝
| after_zero: ∀t1,t2,t,b1,b2,b.
              after t1 t2 t →
              b1 = 0 → b2 = 0 → b = 0 →
              after (b1@t1) (b2@t2) (b@t)
| after_skip: ∀t1,t2,t,b1,b2,b,a2,a.
              after t1 (a2@t2) (a@t) →
              b1 = 0 → b2 = ⫯a2 → b = ⫯a →
              after (b1@t1) (b2@t2) (b@t)
| after_drop: ∀t1,t2,t,b1,b,a1,a.
              after (a1@t1) t2 (a@t) →
              b1 = ⫯a1 → b = ⫯a →
              after (b1@t1) t2 (b@t)
.

interpretation "relational composition (nstream)"
   'RAfter t1 t2 t = (after t1 t2 t).

(* Basic properies on compose ***********************************************)

lemma compose_unfold: ∀t1,t2,a2. t1∘(a2@t2) = t1@❴a2❵@tln … (⫯a2) t1∘t2.
#t1 #t2 #a2 >(stream_expand … (t1∘(a2@t2))) normalize //
qed.

lemma compose_drop: ∀t1,t2,t,a1,a. (a1@t1)∘t2 = a@t → (⫯a1@t1)∘t2 = ⫯a@t.
#t1 * #a2 #t2 #t #a1 #a >compose_unfold >compose_unfold
#H destruct normalize //
qed.

(* Basic inversion lemmas on compose ****************************************)

lemma compose_inv_unfold: ∀t1,t2,t,a2,a. t1∘(a2@t2) = a@t →
                          t1@❴a2❵ = a ∧ tln … (⫯a2) t1∘t2 = t.
#t1 #t2 #t #a2 #a >(stream_expand … (t1∘(a2@t2))) normalize
#H destruct /2 width=1 by conj/
qed-.

lemma compose_inv_O2: ∀t1,t2,t,a1,a. (a1@t1)∘(O@t2) = a@t →
                      a = a1 ∧ t1∘t2 = t.
#t1 #t2 #t #a1 #a >compose_unfold
#H destruct /2 width=1 by conj/
qed-.

lemma compose_inv_S2: ∀t1,t2,t,a1,a2,a. (a1@t1)∘(⫯a2@t2) = a@t →
                      a = ⫯(a1+t1@❴a2❵) ∧ t1∘(a2@t2) = t1@❴a2❵@t.
#t1 #t2 #t #a1 #a2 #a >compose_unfold
#H destruct /2 width=1 by conj/
qed-.

lemma compose_inv_S1: ∀t1,t2,t,a1,a2,a. (⫯a1@t1)∘(a2@t2) = a@t →
                      a = ⫯((a1@t1)@❴a2❵) ∧ (a1@t1)∘(a2@t2) = (a1@t1)@❴a2❵@t.
#t1 #t2 #t #a1 #a2 #a >compose_unfold
#H destruct /2 width=1 by conj/
qed-.

(* Basic properties on after ************************************************)

lemma after_O2: ∀t1,t2,t. t1 ⊚ t2 ≡ t →
                ∀b. b@t1 ⊚ O@t2 ≡ b@t.
#t1 #t2 #t #Ht #b elim b -b /2 width=5 by after_drop, after_zero/
qed.

lemma after_S2: ∀t1,t2,t,b2,b. t1 ⊚ b2@t2 ≡ b@t →
                ∀b1. b1@t1 ⊚ ⫯b2@t2 ≡ ⫯(b1+b)@t.
#t1 #t2 #t #b2 #b #Ht #b1 elim b1 -b1 /2 width=5 by after_drop, after_skip/
qed.

lemma after_apply: ∀b2,t1,t2,t. (tln … (⫯b2) t1) ⊚ t2 ≡ t → t1 ⊚ b2@t2 ≡ t1@❴b2❵@t.
#b2 elim b2 -b2
[ * /2 width=1 by after_O2/
| #b2 #IH * /3 width=1 by after_S2/
]
qed-.

let corec after_total_aux: ∀t1,t2,t. t1 ∘ t2 = t → t1 ⊚ t2 ≡ t ≝ ?.
* #a1 #t1 * #a2 #t2 * #a #t cases a1 -a1
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

theorem after_total: ∀t2,t1. t1 ⊚ t2 ≡ t1 ∘ t2.
/2 width=1 by after_total_aux/ qed.

(* Basic inversion lemmas on after ******************************************)

fact after_inv_O1_aux: ∀t1,t2,t. t1 ⊚ t2 ≡ t → ∀u1. t1 = 0@u1 →
                       (∃∃u2,u. u1 ⊚ u2 ≡ u & t2 = 0@u2 & t = 0@u) ∨
                       ∃∃u2,u,b2,b. u1 ⊚ b2@u2 ≡ b@u & t2 = ⫯b2@u2 & t = ⫯b@u.
#t1 #t2 #t * -t1 -t2 -t #t1 #t2 #t #b1
[ #b2 #b #Ht #H1 #H2 #H3 #u1 #H destruct /3 width=5 by ex3_2_intro, or_introl/
| #b2 #b #a2 #a #Ht #H1 #H2 #H3 #u1 #H destruct /3 width=7 by ex3_4_intro, or_intror/
| #b #a1 #a #_ #H1 #H3 #u1 #H destruct
]
qed-.

fact after_inv_O1_aux2: ∀t1,t2,t,b1,b2,b. b1@t1 ⊚ b2@t2 ≡ b@t → b1 = 0 →
                        (∧∧ t1 ⊚ t2 ≡ t & b2 = 0 & b = 0) ∨
                        ∃∃a2,a. t1 ⊚ a2@t2 ≡ a@t & b2 = ⫯a2 & b = ⫯a.
#t1 #t2 #t #b1 #b2 #b #Ht #H elim (after_inv_O1_aux … Ht) -Ht [4: // |2: skip ] *
[ #u2 #u #Hu #H1 #H2 destruct /3 width=1 by and3_intro, or_introl/
| #u2 #u #a2 #a #Hu #H1 #H2 destruct /3 width=5 by ex3_2_intro, or_intror/
]
qed-.

lemma after_inv_O1: ∀u1,t2,t. 0@u1 ⊚ t2 ≡ t →
                    (∃∃u2,u. u1 ⊚ u2 ≡ u & t2 = 0@u2 & t = 0@u) ∨
                    ∃∃u2,u,b2,b. u1 ⊚ b2@u2 ≡ b@u & t2 = ⫯b2@u2 & t = ⫯b@u.
/2 width=3 by after_inv_O1_aux/ qed-.

fact after_inv_zero_aux2: ∀t1,t2,t,b1,b2,b. b1@t1 ⊚ b2@t2 ≡ b@t → b1 = 0 → b2 = 0 →
                          t1 ⊚ t2 ≡ t ∧ b = 0.
#t1 #t2 #t #b1 #b2 #b #Ht #H1 #H2 elim (after_inv_O1_aux2 … Ht H1) -Ht -H1 *
[ /2 width=1 by conj/
| #a1 #a2 #_ #H0 destruct
]
qed-.

lemma after_inv_zero: ∀u1,u2,t. 0@u1 ⊚ 0@u2 ≡ t →
                      ∃∃u. u1 ⊚ u2 ≡ u & t = 0@u.
#u1 #u2 #t #H elim (after_inv_O1 … H) -H *
[ #x2 #u #Hu #H1 #H2 destruct /2 width=3 by ex2_intro/
| #x2 #u #a2 #a #Hu #H destruct
]
qed-.

fact after_inv_skip_aux2: ∀t1,t2,t,b1,b2,b. b1@t1 ⊚ b2@t2 ≡ b@t → b1 = 0 → ∀a2. b2 = ⫯a2 →
                          ∃∃a. t1 ⊚ a2@t2 ≡ a@t & b = ⫯a.
#t1 #t2 #t #b1 #b2 #b #Ht #H1 #a2 #H2 elim (after_inv_O1_aux2 … Ht H1) -Ht -H1 *
[ #_ #H0 destruct
| #x2 #x #H #H0 #H1 destruct /2 width=3 by ex2_intro/
]
qed-.

lemma after_inv_skip: ∀u1,u2,t,b2. 0@u1 ⊚ ⫯b2@u2 ≡ t →
                      ∃∃u,b. u1 ⊚ b2@u2 ≡ b@u & t = ⫯b@u.
#u1 #u2 * #b #t #b2 #Ht elim (after_inv_skip_aux2 … Ht) [2,4: // |3: skip ] -Ht
#a #Ht #H destruct /2 width=4 by ex2_2_intro/
qed-.

fact after_inv_S1_aux: ∀t1,t2,t. t1 ⊚ t2 ≡ t → ∀u1,b1. t1 = ⫯b1@u1 →
                       ∃∃u,b. b1@u1 ⊚ t2 ≡ b@u & t = ⫯b@u.
#t1 #t2 #t * -t1 -t2 -t #t1 #t2 #t #b1
[ #b2 #b #_ #H1 #H2 #H3 #u1 #a1 #H destruct
| #b2 #b #a2 #a #_ #H1 #H2 #H3 #u1 #a1 #H destruct
| #b #a1 #a #Ht #H1 #H3 #u1 #x1 #H destruct /2 width=4 by ex2_2_intro/
]
qed-.

fact after_inv_S1_aux2: ∀t1,t2,t,b1,b. b1@t1 ⊚ t2 ≡ b@t → ∀a1. b1 = ⫯a1 →
                        ∃∃a. a1@t1 ⊚ t2 ≡ a@t & b = ⫯a.
#t1 #t2 #t #b1 #b #Ht #a #H elim (after_inv_S1_aux … Ht) -Ht [4: // |2,3: skip ]
#u #x #Hu #H0 destruct /2 width=3 by ex2_intro/ 
qed-.

lemma after_inv_S1: ∀u1,t2,t,b1. ⫯b1@u1 ⊚ t2 ≡ t →
                    ∃∃u,b. b1@u1 ⊚ t2 ≡ b@u & t = ⫯b@u.
/2 width=3 by after_inv_S1_aux/ qed-.

fact after_inv_drop_aux2: ∀t1,t2,t,a1,a. a1@t1 ⊚ t2 ≡ a@t → ∀b1,b. a1 = ⫯b1 → a = ⫯b →
                          b1@t1 ⊚ t2 ≡ b@t.
#t1 #t2 #t #a1 #a #Ht #b1 #b #H1 #H elim (after_inv_S1_aux2 … Ht … H1) -a1
#x #Ht #Hx destruct //
qed-.

lemma after_inv_drop: ∀t1,t2,t,b1,b. ⫯b1@t1 ⊚ t2 ≡ ⫯b@t → b1@t1 ⊚ t2 ≡ b@t.
/2 width=5 by after_inv_drop_aux2/ qed-.

fact after_inv_O3_aux1: ∀t1,t2,t. t1 ⊚ t2 ≡ t → ∀u. t = 0@u →
                        ∃∃u1,u2. u1 ⊚ u2 ≡ u & t1 = 0@u1 & t2 = 0@u2.
#t1 #t2 #t * -t1 -t2 -t #t1 #t2 #t #b1
[ #b2 #b #Ht #H1 #H2 #H3 #u #H destruct /2 width=5 by ex3_2_intro/
| #b2 #b #a2 #a #_ #H1 #H2 #H3 #u #H destruct
| #b #a1 #a #_ #H1 #H3 #u #H destruct
]
qed-.

fact after_inv_O3_aux2: ∀t1,t2,t,b1,b2,b. b1@t1 ⊚ b2@t2 ≡ b@t → b = 0 →
                        ∧∧ t1 ⊚ t2 ≡ t & b1 = 0 & b2 = 0.
#t1 #t2 #t #b1 #b2 #b #Ht #H1 elim (after_inv_O3_aux1 … Ht) [2: // |3: skip ] -b
#u1 #u2 #Ht #H1 #H2 destruct /2 width=1 by and3_intro/
qed-.

lemma after_inv_O3: ∀t1,t2,u. t1 ⊚ t2 ≡ 0@u →
                    ∃∃u1,u2. u1 ⊚ u2 ≡ u & t1 = 0@u1 & t2 = 0@u2.
/2 width=3 by after_inv_O3_aux1/ qed-.

fact after_inv_S3_aux1: ∀t1,t2,t. t1 ⊚ t2 ≡ t → ∀u,b. t = ⫯b@u →
                        (∃∃u1,u2,b2. u1 ⊚ b2@u2 ≡ b@u & t1 = 0@u1 & t2 = ⫯b2@u2) ∨
                        ∃∃u1,b1. b1@u1 ⊚ t2 ≡ b@u & t1 = ⫯b1@u1.
#t1 #t2 #t * -t1 -t2 -t #t1 #t2 #t #b1
[ #b2 #b #_ #H1 #H2 #H3 #u #a #H destruct
| #b2 #b #a2 #a #HT #H1 #H2 #H3 #u #x #H destruct /3 width=6 by ex3_3_intro, or_introl/
| #b #a1 #a #HT #H1 #H3 #u #x #H destruct /3 width=4 by ex2_2_intro, or_intror/
]
qed-.

fact after_inv_S3_aux2: ∀t1,t2,t,a1,a2,a. a1@t1 ⊚ a2@t2 ≡ a@t → ∀b. a = ⫯b →
                        (∃∃b2. t1 ⊚ b2@t2 ≡ b@t & a1 = 0 & a2 = ⫯b2) ∨
                        ∃∃b1. b1@t1 ⊚ a2@t2 ≡ b@t & a1 = ⫯b1.
#t1 #t2 #t #a1 #a2 #a #Ht #b #H elim (after_inv_S3_aux1 … Ht) [3: // |4,5: skip ] -a *
[ #u1 #u2 #b2 #Ht #H1 #H2 destruct /3 width=3 by ex3_intro, or_introl/
| #u1 #b1 #Ht #H1 destruct /3 width=3 by ex2_intro, or_intror/
]
qed-.

lemma after_inv_S3: ∀t1,t2,u,b. t1 ⊚ t2 ≡ ⫯b@u →
                    (∃∃u1,u2,b2. u1 ⊚ b2@u2 ≡ b@u & t1 = 0@u1 & t2 = ⫯b2@u2) ∨
                    ∃∃u1,b1. b1@u1 ⊚ t2 ≡ b@u & t1 = ⫯b1@u1.
/2 width=3 by after_inv_S3_aux1/ qed-.

(* Advanced inversion lemmas on after ***************************************)

fact after_inv_O2_aux2: ∀t1,t2,t,a1,a2,a. a1@t1 ⊚ a2@t2 ≡ a@t → a2 = 0 →
                         a1 = a ∧ t1 ⊚ t2 ≡ t.
#t1 #t2 #t #a1 #a2 elim a1 -a1
[ #a #H #H2 elim (after_inv_zero_aux2 … H … H2) -a2 /2 width=1 by conj/
| #a1 #IH #a #H #H2 elim (after_inv_S1_aux2 … H) -H [3: // |2: skip ]
  #b #H #H1 elim (IH … H) // -a2
  #H2 destruct /2 width=1 by conj/
]
qed-.

lemma after_inv_O2: ∀t1,u2,t. t1 ⊚ 0@u2 ≡ t →
                    ∃∃u1,u,a. t1 = a@u1 & t = a@u & u1 ⊚ u2 ≡ u.
* #a1 #t1 #t2 * #a #t #H elim (after_inv_O2_aux2 … H) -H //
/2 width=6 by ex3_3_intro/
qed-.

lemma after_inv_const: ∀a,t1,b2,u2,t. a@t1 ⊚ b2@u2 ≡ a@t → b2 = 0.
#a elim a -a
[ #t1 #b2 #u2 #t #H elim (after_inv_O3 … H) -H
  #u1 #x2 #_ #_ #H destruct //
| #a #IH #t1 #b2 #u2 #t #H elim (after_inv_S1 … H) -H
  #x #b #Hx #H destruct >(IH … Hx) -t1 -u2 -x -b2 -b //
]
qed-.

lemma after_inv_S2: ∀t1,t2,t,a1,a2,a. a1@t1 ⊚ ⫯a2@t2 ≡ a@t → ∀b. a = ⫯(a1+b) →
                    t1 ⊚ a2@t2 ≡ b@t.
#t1 #t2 #t #a1 elim a1 -a1
[ #a2 #a #Ht #b #Hb
  elim (after_inv_skip_aux2 … Ht) -Ht [3,4: // |2: skip ]
  #c #Ht #Hc destruct //
| #a1 #IH #a2 #a #Ht #b #Hb
  lapply (after_inv_drop_aux2 … Ht … Hb) -a [ // | skip ]
  /2 width=3 by/
]
qed-.

(* Forward lemmas on application ********************************************)

lemma after_at_fwd: ∀t,i1,i. @⦃i1, t⦄ ≡ i → ∀t2,t1. t2 ⊚ t1 ≡ t →
                    ∃∃i2. @⦃i1, t1⦄ ≡ i2 & @⦃i2, t2⦄ ≡ i.
#t #i1 #i #H elim H -t -i1 -i
[ #t #t2 #t1 #H elim (after_inv_O3 … H) -H
  /2 width=3 by at_zero, ex2_intro/
| #t #i1 #i #_ #IH #t2 #t1 #H elim (after_inv_O3 … H) -H
  #u2 #u1 #Hu #H1 #H2 destruct elim (IH … Hu) -t
  /3 width=3 by at_S1, ex2_intro/
| #t #b #i1 #i #_ #IH #t2 #t1 #H elim (after_inv_S3 … H) -H *
  [ #u2 #u1 #b2 #Hu #H1 #H2 destruct elim (IH … Hu) -t -b
    /3 width=3 by at_S1, at_lift, ex2_intro/
  | #u1 #b1 #Hu #H destruct elim (IH … Hu) -t -b
    /3 width=3 by at_lift, ex2_intro/
  ]
]
qed-.

lemma after_at1_fwd: ∀t1,i1,i2. @⦃i1, t1⦄ ≡ i2 → ∀t2,t. t2 ⊚ t1 ≡ t →
                     ∃∃i. @⦃i2, t2⦄ ≡ i & @⦃i1, t⦄ ≡ i.
#t1 #i1 #i2 #H elim H -t1 -i1 -i2
[ #t1 #t2 #t #H elim (after_inv_O2 … H) -H /2 width=3 by ex2_intro/
| #t1 #i1 #i2 #_ #IH * #b2 elim b2 -b2
  [ #t2 #t #H elim (after_inv_zero … H) -H
    #u #Hu #H destruct elim (IH … Hu) -t1
    /3 width=3 by at_S1, at_skip, ex2_intro/
  | -IH #b2 #IH #t2 #t #H elim (after_inv_S1 … H) -H
    #u #b #Hu #H destruct elim (IH … Hu) -t1
    /3 width=3 by at_lift, ex2_intro/
  ]
| #t1 #b1 #i1 #i2 #_ #IH * #b2 elim b2 -b2
  [ #t2 #t #H elim (after_inv_skip … H) -H
    #u #a #Hu #H destruct elim (IH … Hu) -t1 -b1
    /3 width=3 by at_S1, at_lift, ex2_intro/
  | -IH #b2 #IH #t2 #t #H elim (after_inv_S1 … H) -H
    #u #b #Hu #H destruct elim (IH … Hu) -t1 -b1
    /3 width=3 by at_lift, ex2_intro/
  ]
]
qed-.

lemma after_fwd_at: ∀t1,t2,i1,i2,i. @⦃i1, t1⦄ ≡ i2 → @⦃i2, t2⦄ ≡ i →
                    ∀t. t2 ⊚ t1 ≡ t → @⦃i1, t⦄ ≡ i.
#t1 #t2 #i1 #i2 #i #Hi1 #Hi2 #t #Ht elim (after_at1_fwd … Hi1 … Ht) -t1
#j #H #Hj >(at_mono … H … Hi2) -i2 //
qed-.

lemma after_fwd_at1: ∀t2,t,i1,i2,i. @⦃i1, t⦄ ≡ i → @⦃i2, t2⦄ ≡ i →
                     ∀t1. t2 ⊚ t1 ≡ t → @⦃i1, t1⦄ ≡ i2.
#t2 #t #i1 #i2 #i #Hi1 #Hi2 #t1 #Ht elim (after_at_fwd … Hi1 … Ht) -t
#j1 #Hij1 #H >(at_inj … Hi2 … H) -i //
qed-.

lemma after_fwd_at2: ∀t,i1,i. @⦃i1, t⦄ ≡ i → ∀t1,i2. @⦃i1, t1⦄ ≡ i2 →
                     ∀t2. t2 ⊚ t1 ≡ t → @⦃i2, t2⦄ ≡ i.
#t #i1 #i #H elim H -t -i1 -i
[ #t #t1 #i2 #Ht1 #t2 #H elim (after_inv_O3 … H) -H
  #u2 #u1 #_ #H1 #H2 destruct >(at_inv_OOx … Ht1) -t -u1 -i2 //
| #t #i1 #i #_ #IH #t1 #i2 #Ht1 #t2 #H elim (after_inv_O3 … H) -H
  #u2 #u1 #Hu #H1 #H2 destruct elim (at_inv_SOx … Ht1) -Ht1
  /3 width=3 by at_skip/
| #t #b #i1 #i #_ #IH #t1 #i2 #Ht1 #t2 #H elim (after_inv_S3 … H) -H *
  [ #u2 #u1 #a1 #Hu #H1 #H2 destruct elim (at_inv_xSx … Ht1) -Ht1
    /3 width=3 by at_skip/
  | #u2 #a2 #Hu #H destruct /3 width=3 by at_lift/
  ]
]
qed-.

(* Advanced forward lemmas on after *****************************************)

lemma after_fwd_hd: ∀t1,t2,t,a2,a. t1 ⊚ a2@t2 ≡ a@t → a = t1@❴a2❵.
#t1 #t2 #t #a2 #a #Ht lapply (after_fwd_at … 0 … Ht) -Ht [4: // | // |2,3: skip ]
/3 width=2 by at_inv_O1, sym_eq/
qed-.

lemma after_fwd_tl: ∀t,t2,a2,t1,a1,a. a1@t1 ⊚ a2@t2 ≡ a@t →
                    tln … a2 t1 ⊚ t2 ≡ t.
#t #t2 #a2 elim a2 -a2
[ #t1 #a1 #a #Ht elim (after_inv_O2_aux2 … Ht) -Ht //
| #a2 #IH * #b1 #t1 #a1 #a #Ht
  lapply (after_fwd_hd … Ht) #Ha
  lapply (after_inv_S2 … Ht … Ha) -a
  /2 width=3 by/
]
qed-.

lemma after_inv_apply: ∀t1,t2,t,a1,a2,a. a1@t1 ⊚ a2@t2 ≡ a@t →
                       a = (a1@t1)@❴a2❵ ∧ tln … a2 t1 ⊚ t2 ≡ t.
/3 width=3 by  after_fwd_tl, after_fwd_hd, conj/ qed-.

(* Main properties on after *************************************************)

let corec after_trans1: ∀t1,t2,t0. t1 ⊚ t2 ≡ t0 →
                        ∀t3,t4. t0 ⊚ t3 ≡ t4 →
                        ∀t. t2 ⊚ t3 ≡ t → t1 ⊚ t ≡ t4 ≝ ?.
#t1 #t2 #t0 * -t1 -t2 -t0 #t1 #t2 #t0 #b1 [1,2: #b2 ] #b0
[ #Ht0 #H1 #H2 #H0 * #b3 #t3 * #b4 #t4 #Ht4 * #b #t #Ht
  cases (after_inv_O1_aux2 … Ht4 H0) -Ht4 -H0 *
  [ #Ht4 #H3 #H4 cases (after_inv_zero_aux2 … Ht H2 H3) -Ht -H2 -H3
    #Ht #H /3 width=6 by after_zero/
  | #a0 #a4 #Ht4 #H3 #H4 cases (after_inv_skip_aux2 … Ht H2 … H3) -Ht -H2 -H3
    #a #Ht3 #H /3 width=6 by after_skip/
  ]
| #a2 #a0 #Ht0 #H1 #H2 #H0 #t3 * #b4 #t4 #Ht4 cases (after_inv_S1_aux2 … Ht4 … H0) -Ht4 -H0
  #a4 #Ht4 #H4 * #b #t #H cases (after_inv_S1_aux2 … H … H2) -H -H2
  #a #Ht3 #H /3 width=6 by after_skip/
| #a1 #a0 #Ht0 #H1 #H0 #t3 * #b4 #t4 #Ht4 cases (after_inv_S1_aux2 … Ht4 … H0) -Ht4 -H0
  #a4 #Ht4 #H4 * #b #t #Ht /3 width=6 by after_drop/
]
qed-.

let corec after_trans2: ∀t1,t0,t4. t1 ⊚ t0 ≡ t4 →
                        ∀t2, t3. t2 ⊚ t3 ≡ t0 →
                        ∀t. t1 ⊚ t2 ≡ t → t ⊚ t3 ≡ t4 ≝ ?.
#t1 #t0 #t4 * -t1 -t0 -t4 #t1 #t0 #t4 #b1 [1,2: #b0 ] #b4
[ #Ht4 #H1 #H0 #H4 * #b2 #t2 * #b3 #t3 #Ht0 * #b #t #Ht
  cases (after_inv_O3_aux2 … Ht0 H0) -b0
  #Ht0 #H2 #H3 cases (after_inv_zero_aux2 … Ht H1 H2) -b1 -b2
  #Ht #H /3 width=6 by after_zero/
| #a0 #a4 #Ht4 #H1 #H0 #H4 * #b2 #t2 * #b3 #t3 #Ht0 * #b #t #Ht
  cases (after_inv_S3_aux2 … Ht0 … H0) -b0 *
  [ #a3 #Ht0 #H2 #H3 cases (after_inv_zero_aux2 … Ht H1 H2) -b1 -b2
    #Ht #H /3 width=6 by after_skip/
  | #a2 #Ht0 #H2 cases (after_inv_skip_aux2 … Ht H1 … H2) -b1 -b2
    #a #Ht #H /3 width=6 by after_drop/
  ]
| #a1 #a4 #Ht4 #H1 #H4 * #b2 #t2 * #b3 #t3 #Ht0 * #b #t #Ht
  cases (after_inv_S1_aux2 … Ht … H1) -b1
  #a #Ht #H /3 width=6 by after_drop/
]
qed-.

let corec after_mono: ∀t1,t2,x. t1 ⊚ t2 ≡ x → ∀y. t1 ⊚ t2 ≡ y → x ≐ y ≝ ?.
* #a1 #t1 * #a2 #t2 * #c #x #Hx * #d #y #Hy
cases (after_inv_apply … Hx) -Hx #Hc #Hx
cases (after_inv_apply … Hy) -Hy #Hd #Hy
/3 width=4 by eq_seq/
qed-.

let corec after_inj: ∀t1,x,t. t1 ⊚ x ≡ t → ∀y. t1 ⊚ y ≡ t → x ≐ y ≝ ?.
* #a1 #t1 * #c #x * #a #t #Hx * #d #y #Hy
cases (after_inv_apply … Hx) -Hx #Hc #Hx
cases (after_inv_apply … Hy) -Hy #Hd
cases (apply_inj_aux … Hc Hd) //
#Hy -a -d /3 width=4 by eq_seq/
qed-.

(* Main inversion lemmas on after *******************************************)

theorem after_inv_total: ∀t1,t2,t. t1 ⊚ t2 ≡ t → t1 ∘ t2 ≐ t.
/2 width=4 by after_mono/ qed-.
