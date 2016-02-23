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
#f1 * #n2 #f2 @(seq … (f1@❴n2❵)) @(compose ? f2) -compose -f2
@(tln … (⫯n2) f1)
defined.

interpretation "functional composition (nstream)"
   'compose f1 f2 = (compose f1 f2).

coinductive after: relation3 rtmap rtmap rtmap ≝
| after_refl: ∀f1,f2,f,g1,g2,g.
              after f1 f2 f → g1 = ↑f1 → g2 = ↑f2 → g = ↑f → after g1 g2 g
| after_push: ∀f1,f2,f,g1,g2,g.
              after f1 f2 f → g1 = ↑f1 → g2 = ⫯f2 → g = ⫯f → after g1 g2 g
| after_next: ∀f1,f2,f,g1,g.
              after f1 f2 f → g1 = ⫯f1 → g = ⫯f → after g1 f2 g
.

interpretation "relational composition (nstream)"
   'RAfter f1 f2 f = (after f1 f2 f).

(* Basic properies on compose ***********************************************)

lemma compose_unfold: ∀f1,f2,n2. f1∘(n2@f2) = f1@❴n2❵@tln … (⫯n2) f1∘f2.
#f1 #f2 #n2 >(stream_expand … (f1∘(n2@f2))) normalize //
qed.

lemma compose_next: ∀f1,f2,f. f1∘f2 = f → (⫯f1)∘f2 = ⫯f.
* #n1 #f1 * #n2 #f2 #f >compose_unfold >compose_unfold
#H destruct normalize //
qed.

(* Basic inversion lemmas on compose ****************************************)

lemma compose_inv_unfold: ∀f1,f2,f,n2,n. f1∘(n2@f2) = n@f →
                          f1@❴n2❵ = n ∧ tln … (⫯n2) f1∘f2 = f.
#f1 #f2 #f #n2 #n >(stream_expand … (f1∘(n2@f2))) normalize
#H destruct /2 width=1 by conj/
qed-.

lemma compose_inv_O2: ∀f1,f2,f,n1,n. (n1@f1)∘(↑f2) = n@f →
                      n = n1 ∧ f1∘f2 = f.
#f1 #f2 #f #n1 #n >compose_unfold
#H destruct /2 width=1 by conj/
qed-.

lemma compose_inv_S2: ∀f1,f2,f,n1,n2,n. (n1@f1)∘(⫯n2@f2) = n@f →
                      n = ⫯(n1+f1@❴n2❵) ∧ f1∘(n2@f2) = f1@❴n2❵@f.
#f1 #f2 #f #n1 #n2 #n >compose_unfold
#H destruct /2 width=1 by conj/
qed-.

lemma compose_inv_S1: ∀f1,f2,f,n1,n2,n. (⫯n1@f1)∘(n2@f2) = n@f →
                      n = ⫯((n1@f1)@❴n2❵) ∧ (n1@f1)∘(n2@f2) = (n1@f1)@❴n2❵@f.
#f1 #f2 #f #n1 #n2 #n >compose_unfold
#H destruct /2 width=1 by conj/
qed-.

(* Basic properties on after ************************************************)

lemma after_O2: ∀f1,f2,f. f1 ⊚ f2 ≡ f →
                ∀n. n@f1 ⊚ ↑f2 ≡ n@f.
#f1 #f2 #f #Ht #n elim n -n /2 width=7 by after_refl, after_next/
qed.

lemma after_S2: ∀f1,f2,f,n2,n. f1 ⊚ n2@f2 ≡ n@f →
                ∀n1. n1@f1 ⊚ ⫯n2@f2 ≡ ⫯(n1+n)@f.
#f1 #f2 #f #n2 #n #Ht #n1 elim n1 -n1 /2 width=7 by after_next, after_push/
qed.

lemma after_apply: ∀n2,f1,f2,f. (tln … (⫯n2) f1) ⊚ f2 ≡ f → f1 ⊚ n2@f2 ≡ f1@❴n2❵@f.
#n2 elim n2 -n2
[ * /2 width=1 by after_O2/
| #n2 #IH * /3 width=1 by after_S2/
]
qed-.

let corec after_total_aux: ∀f1,f2,f. f1 ∘ f2 = f → f1 ⊚ f2 ≡ f ≝ ?.
* #n1 #f1 * #n2 #f2 * #n #f cases n1 -n1
[ cases n2 -n2
  [ #H cases (compose_inv_O2 … H) -H
    /3 width=7 by after_refl, eq_f2/
  | #n2 #H cases (compose_inv_S2 … H) -H
    /3 width=7 by after_push/
  ]
| #n1 #H cases (compose_inv_S1 … H) -H
  /4 width=7 by after_next, next_rew_sn/
]
qed-.

theorem after_total: ∀f2,f1. f1 ⊚ f2 ≡ f1 ∘ f2.
/2 width=1 by after_total_aux/ qed.

(* Basic inversion lemmas on after ******************************************)

fact after_inv_OOx_aux: ∀g1,g2,g. g1 ⊚ g2 ≡ g → ∀f1,f2. g1 = ↑f1 → g2 = ↑f2 →
                        ∃∃f. f1 ⊚ f2 ≡ f & g = ↑f.
#g1 #g2 #g * -g1 -g2 -g #f1 #f2 #f #g1
[ #g2 #g #Hf #H1 #H2 #H #x1 #x2 #Hx1 #Hx2 destruct
  <(injective_push … Hx1) <(injective_push … Hx2) -x2 -x1
  /2 width=3 by ex2_intro/
| #g2 #g #_ #_ #H2 #_ #x1 #x2 #_ #Hx2 destruct
  elim (discr_next_push … Hx2)
| #g #_ #H1 #_ #x1 #x2 #Hx1 #_ destruct
  elim (discr_next_push … Hx1)
]
qed-.

lemma after_inv_OOx: ∀f1,f2,g. ↑f1 ⊚ ↑f2 ≡ g → ∃∃f. f1 ⊚ f2 ≡ f & g = ↑f.
/2 width=5 by after_inv_OOx_aux/ qed-.

fact after_inv_OSx_aux: ∀g1,g2,g. g1 ⊚ g2 ≡ g → ∀f1,f2. g1 = ↑f1 → g2 = ⫯f2 →
                        ∃∃f. f1 ⊚ f2 ≡ f & g = ⫯f.
#g1 #g2 #g * -g1 -g2 -g #f1 #f2 #f #g1
[ #g2 #g #_ #_ #H2 #_ #x1 #x2 #_ #Hx2 destruct
  elim (discr_push_next … Hx2)
| #g2 #g #Hf #H1 #H2 #H3 #x1 #x2 #Hx1 #Hx2 destruct
  <(injective_push … Hx1) <(injective_next … Hx2) -x2 -x1
  /2 width=3 by ex2_intro/
| #g #_ #H1 #_ #x1 #x2 #Hx1 #_ destruct
  elim (discr_next_push … Hx1)
]
qed-.

lemma after_inv_OSx: ∀f1,f2,g. ↑f1 ⊚ ⫯f2 ≡ g → ∃∃f. f1 ⊚ f2 ≡ f & g = ⫯f.
/2 width=5 by after_inv_OSx_aux/ qed-.

fact after_inv_Sxx_aux: ∀g1,f2,g. g1 ⊚ f2 ≡ g → ∀f1. g1 = ⫯f1 →
                        ∃∃f. f1 ⊚ f2 ≡ f & g = ⫯f.
#g1 #f2 #g * -g1 -f2 -g #f1 #f2 #f #g1
[ #g2 #g #_ #H1 #_ #_ #x1 #Hx1 destruct
  elim (discr_push_next … Hx1)
| #g2 #g #_ #H1 #_ #_ #x1 #Hx1 destruct
  elim (discr_push_next … Hx1)
| #g #Hf #H1 #H #x1 #Hx1 destruct
  <(injective_next … Hx1) -x1
  /2 width=3 by ex2_intro/
]
qed-.

lemma after_inv_Sxx: ∀f1,f2,g. ⫯f1 ⊚ f2 ≡ g → ∃∃f. f1 ⊚ f2 ≡ f & g = ⫯f.
/2 width=5 by after_inv_Sxx_aux/ qed-.

(* Advanced inversion lemmas on after ***************************************)

fact after_inv_OOO_aux: ∀g1,g2,g. g1 ⊚ g2 ≡ g →
                        ∀f1,f2,f. g1 = ↑f1 → g2 = ↑f2 → g = ↑f → f1 ⊚ f2 ≡ f.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H elim (after_inv_OOx_aux … Hg … H1 H2) -g1 -g2
#x #Hf #Hx destruct >(injective_push … Hx) -f //
qed-.

fact after_inv_OOS_aux: ∀g1,g2,g. g1 ⊚ g2 ≡ g →
                        ∀f1,f2,f. g1 = ↑f1 → g2 = ↑f2 → g = ⫯f → ⊥.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H elim (after_inv_OOx_aux … Hg … H1 H2) -g1 -g2
#x #Hf #Hx destruct elim (discr_next_push … Hx)
qed-.

fact after_inv_OSS_aux: ∀g1,g2,g. g1 ⊚ g2 ≡ g →
                        ∀f1,f2,f. g1 = ↑f1 → g2 = ⫯f2 → g = ⫯f → f1 ⊚ f2 ≡ f.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H elim (after_inv_OSx_aux … Hg … H1 H2) -g1 -g2
#x #Hf #Hx destruct >(injective_next … Hx) -f //
qed-.

fact after_inv_OSO_aux: ∀g1,g2,g. g1 ⊚ g2 ≡ g →
                        ∀f1,f2,f. g1 = ↑f1 → g2 = ⫯f2 → g = ↑f → ⊥.
#g1 #g2 #g #Hg #f1 #f2 #f #H1 #H2 #H elim (after_inv_OSx_aux … Hg … H1 H2) -g1 -g2
#x #Hf #Hx destruct elim (discr_push_next … Hx)
qed-.

fact after_inv_SxS_aux: ∀g1,f2,g. g1 ⊚ f2 ≡ g →
                        ∀f1,f. g1 = ⫯f1 → g = ⫯f → f1 ⊚ f2 ≡ f.
#g1 #f2 #g #Hg #f1 #f #H1 #H elim (after_inv_Sxx_aux … Hg … H1) -g1
#x #Hf #Hx destruct >(injective_next … Hx) -f //
qed-.

fact after_inv_SxO_aux: ∀g1,f2,g. g1 ⊚ f2 ≡ g →
                        ∀f1,f. g1 = ⫯f1 → g = ↑f → ⊥.
#g1 #f2 #g #Hg #f1 #f #H1 #H elim (after_inv_Sxx_aux … Hg … H1) -g1
#x #Hf #Hx destruct elim (discr_push_next … Hx)
qed-.

fact after_inv_OxO_aux: ∀g1,g2,g. g1 ⊚ g2 ≡ g →
                        ∀f1,f. g1 = ↑f1 → g = ↑f →
                        ∃∃f2. f1 ⊚ f2 ≡ f & g2 = ↑f2.
#g1 * * [2: #m2] #g2 #g #Hg #f1 #f #H1 #H
[ elim (after_inv_OSO_aux … Hg … H1 … H) -g1 -g -f1 -f //
| lapply (after_inv_OOO_aux … Hg … H1 … H) -g1 -g /2 width=3 by ex2_intro/
]
qed-.

lemma after_inv_OxO: ∀f1,g2,f. ↑f1 ⊚ g2 ≡ ↑f →
                     ∃∃f2. f1 ⊚ f2 ≡ f & g2 = ↑f2.
/2 width=5 by after_inv_OxO_aux/ qed-.

fact after_inv_OxS_aux: ∀g1,g2,g. g1 ⊚ g2 ≡ g →
                        ∀f1,f. g1 = ↑f1 → g = ⫯f →
                        ∃∃f2. f1 ⊚ f2 ≡ f & g2 = ⫯f2.
#g1 * * [2: #m2] #g2 #g #Hg #f1 #f #H1 #H
[ lapply (after_inv_OSS_aux … Hg … H1 … H) -g1 -g /2 width=3 by ex2_intro/
| elim (after_inv_OOS_aux … Hg … H1 … H) -g1 -g -f1 -f // 
]
qed-.

fact after_inv_xxO_aux: ∀g1,g2,g. g1 ⊚ g2 ≡ g → ∀f. g = ↑f →
                        ∃∃f1,f2. f1 ⊚ f2 ≡ f & g1 = ↑f1 & g2 = ↑f2.
* * [2: #m1 ] #g1 #g2 #g #Hg #f #H
[ elim (after_inv_SxO_aux … Hg … H) -g2 -g -f //
| elim (after_inv_OxO_aux … Hg … H) -g /2 width=5 by ex3_2_intro/
]
qed-.

lemma after_inv_xxO: ∀g1,g2,f. g1 ⊚ g2 ≡ ↑f →
                     ∃∃f1,f2. f1 ⊚ f2 ≡ f & g1 = ↑f1 & g2 = ↑f2.
/2 width=3 by after_inv_xxO_aux/ qed-.

fact after_inv_xxS_aux: ∀g1,g2,g. g1 ⊚ g2 ≡ g → ∀f. g = ⫯f →
                        (∃∃f1,f2. f1 ⊚ f2 ≡ f & g1 = ↑f1 & g2 = ⫯f2) ∨
                        ∃∃f1. f1 ⊚ g2 ≡ f & g1 = ⫯f1.
* * [2: #m1 ] #g1 #g2 #g #Hg #f #H
[ /4 width=5 by after_inv_SxS_aux, or_intror, ex2_intro/
| elim (after_inv_OxS_aux … Hg … H) -g
  /3 width=5 by or_introl, ex3_2_intro/
]
qed-.

lemma after_inv_xxS: ∀g1,g2,f. g1 ⊚ g2 ≡ ⫯f →
                     (∃∃f1,f2. f1 ⊚ f2 ≡ f & g1 = ↑f1 & g2 = ⫯f2) ∨
                     ∃∃f1. f1 ⊚ g2 ≡ f & g1 = ⫯f1.
/2 width=3 by after_inv_xxS_aux/ qed-.

fact after_inv_Oxx_aux: ∀g1,g2,g. g1 ⊚ g2 ≡ g → ∀f1. g1 = ↑f1 →
                        (∃∃f2,f. f1 ⊚ f2 ≡ f & g2 = ↑f2 & g = ↑f) ∨
                        (∃∃f2,f. f1 ⊚ f2 ≡ f & g2 = ⫯f2 & g = ⫯f).
#g1 * * [2: #m2 ] #g2 #g #Hg #f1 #H
[  elim (after_inv_OSx_aux … Hg … H) -g1
  /3 width=5 by or_intror, ex3_2_intro/
| elim (after_inv_OOx_aux … Hg … H) -g1
  /3 width=5 by or_introl, ex3_2_intro/
]
qed-.

lemma after_inv_Oxx: ∀f1,g2,g. ↑f1 ⊚ g2 ≡ g →
                     (∃∃f2,f. f1 ⊚ f2 ≡ f & g2 = ↑f2 & g = ↑f) ∨
                     (∃∃f2,f. f1 ⊚ f2 ≡ f & g2 = ⫯f2 & g = ⫯f).
/2 width=3 by after_inv_Oxx_aux/ qed-.

fact after_inv_xOx_aux: ∀f1,g2,f,n1,n. n1@f1 ⊚ g2 ≡ n@f → ∀f2. g2 = ↑f2 →
                        f1 ⊚ f2 ≡ f ∧ n1 = n.
#f1 #g2 #f #n1 elim n1 -n1
[ #n #Hf #f2 #H2 elim (after_inv_OOx_aux … Hf … H2) -g2 [3: // |2: skip ]
  #g #Hf #H elim (push_inv_seq_sn … H) -H destruct /2 width=1 by conj/
| #n1 #IH #n #Hf #f2 #H2 elim (after_inv_Sxx_aux … Hf) -Hf [3: // |2: skip ]
  #g1 #Hg #H1 elim (next_inv_seq_sn … H1) -H1
  #x #Hx #H destruct elim (IH … Hg) [2: // |3: skip ] -IH -Hg
  #H destruct /2 width=1 by conj/
]
qed-.

lemma after_inv_xOx: ∀f1,f2,f,n1,n. n1@f1 ⊚ ↑f2 ≡ n@f →
                     f1 ⊚ f2 ≡ f ∧ n1 = n.
/2 width=3 by after_inv_xOx_aux/ qed-.

fact after_inv_xSx_aux: ∀f1,g2,f,n1,n. n1@f1 ⊚ g2 ≡ n@f → ∀f2. g2 = ⫯f2 →
                        ∃∃m. f1 ⊚ f2 ≡ m@f & n = ⫯(n1+m).
#f1 #g2 #f #n1 elim n1 -n1
[ #n #Hf #f2 #H2 elim (after_inv_OSx_aux … Hf … H2) -g2 [3: // |2: skip ]
  #g #Hf #H elim (next_inv_seq_sn … H) -H
  #x #Hx #Hg destruct /2 width=3 by ex2_intro/
| #n1 #IH #n #Hf #f2 #H2 elim (after_inv_Sxx_aux … Hf) -Hf [3: // |2: skip ]
  #g #Hg #H elim (next_inv_seq_sn … H) -H
  #x #Hx #H destruct elim (IH … Hg) -IH -Hg [3: // |2: skip ]
  #m #Hf #Hm destruct /2 width=3 by ex2_intro/
]
qed-.

lemma after_inv_xSx: ∀f1,f2,f,n1,n. n1@f1 ⊚ ⫯f2 ≡ n@f →
                     ∃∃m. f1 ⊚ f2 ≡ m@f & n = ⫯(n1+m).
/2 width=3 by after_inv_xSx_aux/ qed-.

lemma after_inv_const: ∀f1,f2,f,n2,n. n@f1 ⊚ n2@f2 ≡ n@f → f1 ⊚ f2 ≡ f ∧ n2 = 0.
#f1 #f2 #f #n2 #n elim n -n
[ #H elim (after_inv_OxO … H) -H
  #g2 #Hf #H elim (push_inv_seq_sn … H) -H /2 width=1 by conj/
| #n #IH #H lapply (after_inv_SxS_aux … H ????) -H /2 width=5 by/
]
qed-.

(* Forward lemmas on application ********************************************)

lemma after_at_fwd: ∀f,i1,i. @⦃i1, f⦄ ≡ i → ∀f2,f1. f2 ⊚ f1 ≡ f →
                    ∃∃i2. @⦃i1, f1⦄ ≡ i2 & @⦃i2, f2⦄ ≡ i.
#f #i1 #i #H elim H -f -i1 -i
[ #f #f2 #f1 #H elim (after_inv_xxO … H) -H
  /2 width=3 by at_refl, ex2_intro/
| #f #i1 #i #_ #IH #f2 #f1 #H elim (after_inv_xxO … H) -H
  #g2 #g1 #Hg #H1 #H2 destruct elim (IH … Hg) -f
  /3 width=3 by at_S1, ex2_intro/
| #f #i1 #i #_ #IH #f2 #f1 #H elim (after_inv_xxS … H) -H *
  [ #g2 #g1 #Hg #H2 #H1 destruct elim (IH … Hg) -f
    /3 width=3 by at_S1, at_next, ex2_intro/
  | #g1 #Hg #H destruct elim (IH … Hg) -f
    /3 width=3 by at_next, ex2_intro/
  ]
]
qed-.

lemma after_at1_fwd: ∀f1,i1,i2. @⦃i1, f1⦄ ≡ i2 → ∀f2,f. f2 ⊚ f1 ≡ f →
                     ∃∃i. @⦃i2, f2⦄ ≡ i & @⦃i1, f⦄ ≡ i.
#f1 #i1 #i2 #H elim H -f1 -i1 -i2
[ #f1 * #n2 #f2 * #n #f #H elim (after_inv_xOx … H) -H /2 width=3 by ex2_intro/
| #f1 #i1 #i2 #_ #IH * #n2 #f2 * #n #f #H elim (after_inv_xOx … H) -H
  #Hf #H destruct elim (IH … Hf) -f1 /3 width=3 by at_S1, ex2_intro/
| #f1 #i1 #i2 #_ #IH * #n2 #f2 * #n #f #H elim (after_inv_xSx … H) -H
  #m #Hf #Hm destruct elim (IH … Hf) -f1
  /4 width=3 by at_plus2, at_S1, at_next, ex2_intro/
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
[ #f #f1 #i2 #Ht1 #f2 #H elim (after_inv_xxO … H) -H
  #g2 #g1 #_ #H1 #H2 destruct >(at_inv_OOx … Ht1) -f -g1 -i2 //
| #f #i1 #i #_ #IH #f1 #i2 #Ht1 #f2 #H elim (after_inv_xxO … H) -H
  #g2 #g1 #Hu #H1 #H2 destruct elim (at_inv_SOx … Ht1) -Ht1
  /3 width=3 by at_push/
| #f #i1 #i #_ #IH #f1 #i2 #Hf1 #f2 #H elim (after_inv_xxS … H) -H *
  [ #g2 #g1 #Hg #H2 #H1 destruct elim (at_inv_xSx … Hf1) -Hf1
    /3 width=3 by at_push/
  | #g2 #Hg #H destruct /3 width=3 by at_next/
  ]
]
qed-.

(* Advanced forward lemmas on after *****************************************)

lemma after_fwd_hd: ∀f1,f2,f,n2,n. f1 ⊚ n2@f2 ≡ n@f → n = f1@❴n2❵.
#f1 #f2 #f #n2 #n #H lapply (after_fwd_at … 0 … H) -H [1,4: // |2,3: skip ]
/3 width=2 by at_inv_O1, sym_eq/
qed-.

lemma after_fwd_tl: ∀f,f2,n2,f1,n1,n. n1@f1 ⊚ n2@f2 ≡ n@f →
                    tln … n2 f1 ⊚ f2 ≡ f.
#f #f2 #n2 elim n2 -n2
[ #f1 #n1 #n #H elim (after_inv_xOx … H) -H //
| #n2 #IH * #m1 #f1 #n1 #n #H elim (after_inv_xSx_aux … H ??) -H [3: // |2: skip ]
  #m #Hm #H destruct /2 width=3 by/
]
qed-.

lemma after_inv_apply: ∀f1,f2,f,a1,a2,a. a1@f1 ⊚ a2@f2 ≡ a@f →
                       a = (a1@f1)@❴a2❵ ∧ tln … a2 f1 ⊚ f2 ≡ f.
/3 width=3 by after_fwd_tl, after_fwd_hd, conj/ qed-.

(* Main properties on after *************************************************)

let corec after_trans1: ∀f0,f3,f4. f0 ⊚ f3 ≡ f4 →
                        ∀f1,f2. f1 ⊚ f2 ≡ f0 →
                        ∀f. f2 ⊚ f3 ≡ f → f1 ⊚ f ≡ f4 ≝ ?.
#f0 #f3 #f4 * -f0 -f3 -f4 #f0 #f3 #f4 #g0 [1,2: #g3 ] #g4
[ #Hf4 #H0 #H3 #H4 #g1 #g2 #Hg0 #g #Hg
  cases (after_inv_xxO_aux … Hg0 … H0) -g0
  #f1 #f2 #Hf0 #H1 #H2
  cases (after_inv_OOx_aux … Hg … H2 H3) -g2 -g3
  #f #Hf #H /3 width=7 by after_refl/
| #Hf4 #H0 #H3 #H4 #g1 #g2 #Hg0 #g #Hg
  cases (after_inv_xxO_aux … Hg0 … H0) -g0
  #f1 #f2 #Hf0 #H1 #H2
  cases (after_inv_OSx_aux … Hg … H2 H3) -g2 -g3
  #f #Hf #H /3 width=7 by after_push/
| #Hf4 #H0 #H4 #g1 #g2 #Hg0 #g #Hg
  cases (after_inv_xxS_aux … Hg0 … H0) -g0 *
  [ #f1 #f2 #Hf0 #H1 #H2
    cases (after_inv_Sxx_aux … Hg … H2) -g2
    #f #Hf #H /3 width=7 by after_push/
  | #f1 #Hf0 #H1 /3 width=6 by after_next/
  ]
]
qed-.

let corec after_trans2: ∀f1,f0,f4. f1 ⊚ f0 ≡ f4 →
                        ∀f2, f3. f2 ⊚ f3 ≡ f0 →
                        ∀f. f1 ⊚ f2 ≡ f → f ⊚ f3 ≡ f4 ≝ ?.
#f1 #f0 #f4 * -f1 -f0 -f4 #f1 #f0 #f4 #g1 [1,2: #g0 ] #g4
[ #Hf4 #H1 #H0 #H4 #g2 #g3 #Hg0 #g #Hg
  cases (after_inv_xxO_aux … Hg0 … H0) -g0
  #f2 #f3 #Hf0 #H2 #H3
  cases (after_inv_OOx_aux … Hg … H1 H2) -g1 -g2
  #f #Hf #H /3 width=7 by after_refl/
| #Hf4 #H1 #H0 #H4 #g2 #g3 #Hg0 #g #Hg
  cases (after_inv_xxS_aux … Hg0 … H0) -g0 *
  [ #f2 #f3 #Hf0 #H2 #H3
    cases (after_inv_OOx_aux … Hg … H1 H2) -g1 -g2
    #f #Hf #H /3 width=7 by after_push/
  | #f2 #Hf0 #H2
    cases (after_inv_OSx_aux … Hg … H1 H2) -g1 -g2
    #f #Hf #H /3 width=6 by after_next/
  ]
| #Hf4 #H1 #H4 #f2 #f3 #Hf0 #g #Hg
  cases (after_inv_Sxx_aux … Hg … H1) -g1
  #f #Hg #H /3 width=6 by after_next/
]
qed-.

(* Main inversion lemmas on after *******************************************)

let corec after_mono: ∀f1,f2,f,g1,g2,g. f1 ⊚ f2 ≡ f → g1 ⊚ g2 ≡ g →
                      f1 ≐ g1 → f2 ≐ g2 → f ≐ g ≝ ?.
* #n1 #f1 * #n2 #f2 * #n #f * #m1 #g1 * #m2 #g2 * #m #g #Hf #Hg #H1 #H2
cases (after_inv_apply … Hf) -Hf #Hn #Hf
cases (after_inv_apply … Hg) -Hg #Hm #Hg
cases (eq_stream_inv_seq ????? H1) -H1
cases (eq_stream_inv_seq ????? H2) -H2
/4 width=8 by apply_eq_repl, tln_eq_repl, eq_seq/
qed-.

let corec after_inj: ∀f1,f2,f,g1,g2,g. f1 ⊚ f2 ≡ f → g1 ⊚ g2 ≡ g →
                     f1 ≐ g1 → f ≐ g → f2 ≐ g2 ≝ ?.
* #n1 #f1 * #n2 #f2 * #n #f * #m1 #g1 * #m2 #g2 * #m #g #Hf #Hg #H1 #H2
cases (after_inv_apply … Hf) -Hf #Hn #Hf
cases (after_inv_apply … Hg) -Hg #Hm #Hg
cases (eq_stream_inv_seq ????? H1) -H1 #Hnm1 #Hfg1
cases (eq_stream_inv_seq ????? H2) -H2 #Hnm #Hfg
lapply (apply_inj_aux … Hn Hm Hnm ?) -n -m
/4 width=8 by tln_eq_repl, eq_seq/
qed-.

theorem after_inv_total: ∀f1,f2,f. f1 ⊚ f2 ≡ f → f1 ∘ f2 ≐ f.
/2 width=8 by after_mono/ qed-.

(* Properties on after ******************************************************)

lemma after_isid_dx: ∀f2,f1,f. f2 ⊚ f1 ≡ f → f2 ≐ f → 𝐈⦃f1⦄.
#f2 #f1 #f #Ht #H2 @isid_at_total
#i1 #i2 #Hi12 elim (after_at1_fwd … Hi12 … Ht) -f1
/3 width=6 by at_inj, eq_stream_sym/
qed.

lemma after_isid_sn: ∀f2,f1,f. f2 ⊚ f1 ≡ f → f1 ≐ f → 𝐈⦃f2⦄.
#f2 #f1 #f #Ht #H1 @isid_at_total
#i2 #i #Hi2 lapply (at_total i2 f1)
#H0 lapply (at_increasing … H0)
#Ht1 lapply (after_fwd_at2 … (f1@❴i2❵) … H0 … Ht)
/3 width=7 by at_eq_repl_back, at_mono, at_id_le/
qed.

(* Inversion lemmas on after ************************************************)

let corec isid_after_sn: ∀f1,f2. 𝐈⦃f1⦄ → f1 ⊚ f2 ≡ f2 ≝ ?.
* #n1 #f1 * * [ | #n2 ] #f2 #H cases (isid_inv_seq … H) -H
/3 width=7 by after_push, after_refl/
qed-.

let corec isid_after_dx: ∀f2,f1. 𝐈⦃f2⦄ → f1 ⊚ f2 ≡ f1 ≝ ?.
* #n2 #f2 * *
[ #f1 #H cases (isid_inv_seq … H) -H
  /3 width=7 by after_refl/
| #n1 #f1 #H @after_next [4,5: // |1,2: skip ] /2 width=1 by/
]
qed-.

lemma after_isid_inv_sn: ∀f1,f2,f. f1 ⊚ f2 ≡ f →  𝐈⦃f1⦄ → f2 ≐ f.
/3 width=8 by isid_after_sn, after_mono/
qed-.

lemma after_isid_inv_dx: ∀f1,f2,f. f1 ⊚ f2 ≡ f →  𝐈⦃f2⦄ → f1 ≐ f.
/3 width=8 by isid_after_dx, after_mono/
qed-.

axiom after_inv_isid3: ∀f1,f2,f. f1 ⊚ f2 ≡ f → 𝐈⦃f⦄ → 𝐈⦃f1⦄ ∧ 𝐈⦃f2⦄.
