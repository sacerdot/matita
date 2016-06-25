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

include "ground_2/relocation/nstream_istot.ma".
include "ground_2/relocation/rtmap_after.ma".

(* RELOCATION N-STREAM ******************************************************)

corec definition compose: rtmap → rtmap → rtmap.
#f2 * #n1 #f1 @(seq … (f2@❴n1❵)) @(compose ? f1) -compose -f1
@(↓*[⫯n1] f2)
defined.

interpretation "functional composition (nstream)"
   'compose f2 f1 = (compose f2 f1).

(* Basic properies on compose ***********************************************)

lemma compose_rew: ∀f2,f1,n1. f2@❴n1❵@(↓*[⫯n1]f2)∘f1 = f2∘(n1@f1).
#f2 #f1 #n1 <(stream_rew … (f2∘(n1@f1))) normalize //
qed.

lemma compose_next: ∀f2,f1,f. f2∘f1 = f → (⫯f2)∘f1 = ⫯f.
#f2 * #n1 #f1 #f <compose_rew <compose_rew
* -f <tls_S1 /2 width=1 by eq_f2/
qed.

(* Basic inversion lemmas on compose ****************************************)

lemma compose_inv_rew: ∀f2,f1,f,n1,n. f2∘(n1@f1) = n@f →
                       f2@❴n1❵ = n ∧ (↓*[⫯n1]f2)∘f1 = f.
#f2 #f1 #f #n1 #n <(stream_rew … (f2∘(n1@f1))) normalize
#H destruct /2 width=1 by conj/
qed-.

lemma compose_inv_O2: ∀f2,f1,f,n2,n. (n2@f2)∘(↑f1) = n@f →
                      n2 = n ∧ f2∘f1 = f.
#f2 #f1 #f #n2 #n <compose_rew
#H destruct /2 width=1 by conj/
qed-.

lemma compose_inv_S2: ∀f2,f1,f,n2,n1,n. (n2@f2)∘(⫯n1@f1) = n@f →
                      ⫯(n2+f2@❴n1❵) = n ∧ f2∘(n1@f1) = f2@❴n1❵@f.
#f2 #f1 #f #n2 #n1 #n <compose_rew
#H destruct <tls_S1 /2 width=1 by conj/
qed-.

lemma compose_inv_S1: ∀f2,f1,f,n1,n. (⫯f2)∘(n1@f1) = n@f →
                      ⫯(f2@❴n1❵) = n ∧ f2∘(n1@f1) = f2@❴n1❵@f.
#f2 #f1 #f #n1 #n <compose_rew
#H destruct <tls_S1 /2 width=1 by conj/
qed-.

(* Specific properties on after *********************************************)

lemma after_O2: ∀f2,f1,f. f2 ⊚ f1 ≡ f →
                ∀n. n@f2 ⊚ ↑f1 ≡ n@f.
#f2 #f1 #f #Hf #n elim n -n /2 width=7 by after_refl, after_next/
qed.

lemma after_S2: ∀f2,f1,f,n1,n. f2 ⊚ n1@f1 ≡ n@f →
                ∀n2. n2@f2 ⊚ ⫯n1@f1 ≡ ⫯(n2+n)@f.
#f2 #f1 #f #n1 #n #Hf #n2 elim n2 -n2 /2 width=7 by after_next, after_push/
qed.

lemma after_apply: ∀n1,f2,f1,f. (↓*[⫯n1] f2) ⊚ f1 ≡ f → f2 ⊚ n1@f1 ≡ f2@❴n1❵@f.
#n1 elim n1 -n1
[ * /2 width=1 by after_O2/
| #n1 #IH * /3 width=1 by after_S2/
]
qed-.

corec lemma after_total_aux: ∀f2,f1,f. f2 ∘ f1 = f → f2 ⊚ f1 ≡ f.
* #n2 #f2 * #n1 #f1 * #n #f cases n2 -n2
[ cases n1 -n1
  [ #H cases (compose_inv_O2 … H) -H /3 width=7 by after_refl, eq_f2/
  | #n1 #H cases (compose_inv_S2 … H) -H * -n /3 width=7 by after_push/
  ]
| #n2 >next_rew #H cases (compose_inv_S1 … H) -H * -n /3 width=5 by after_next/
]
qed-.

theorem after_total: ∀f1,f2. f2 ⊚ f1 ≡ f2 ∘ f1.
/2 width=1 by after_total_aux/ qed.

(* Specific inversion lemmas on after ***************************************)

lemma after_inv_xpx: ∀f2,g2,f,n2,n. n2@f2 ⊚ g2 ≡ n@f → ∀f1. ↑f1 = g2 →
                     f2 ⊚ f1 ≡ f ∧ n2 = n.
#f2 #g2 #f #n2 elim n2 -n2
[ #n #Hf #f1 #H2 elim (after_inv_ppx … Hf … H2) -g2 [2,3: // ]
  #g #Hf #H elim (push_inv_seq_dx … H) -H destruct /2 width=1 by conj/
| #n2 #IH #n #Hf #f1 #H2 elim (after_inv_nxx … Hf) -Hf [2,3: // ]
  #g1 #Hg #H1 elim (next_inv_seq_dx … H1) -H1
  #x #Hx #H destruct elim (IH … Hg) [2,3: // ] -IH -Hg
  #H destruct /2 width=1 by conj/
]
qed-.

lemma after_inv_xnx: ∀f2,g2,f,n2,n. n2@f2 ⊚ g2 ≡ n@f → ∀f1. ⫯f1 = g2 →
                     ∃∃m. f2 ⊚ f1 ≡ m@f & ⫯(n2+m) = n.
#f2 #g2 #f #n2 elim n2 -n2
[ #n #Hf #f1 #H2 elim (after_inv_pnx … Hf … H2) -g2 [2,3: // ]
  #g #Hf #H elim (next_inv_seq_dx … H) -H
  #x #Hx #Hg destruct /2 width=3 by ex2_intro/
| #n2 #IH #n #Hf #f1 #H2 elim (after_inv_nxx … Hf) -Hf [2,3: // ]
  #g #Hg #H elim (next_inv_seq_dx … H) -H
  #x #Hx #H destruct elim (IH … Hg) -IH -Hg [2,3: // ]
  #m #Hf #Hm destruct /2 width=3 by ex2_intro/
]
qed-.

lemma after_inv_const: ∀f2,f1,f,n1,n. n@f2 ⊚ n1@f1 ≡ n@f → f2 ⊚ f1 ≡ f ∧ 0 = n1.
#f2 #f1 #f #n1 #n elim n -n
[ #H elim (after_inv_pxp … H) -H [ |*: // ]
  #g2 #Hf #H elim (push_inv_seq_dx … H) -H /2 width=1 by conj/
| #n #IH #H lapply (after_inv_nxn … H ????) -H /2 width=5 by/
]
qed-.

lemma after_inv_total: ∀f2,f1,f. f2 ⊚ f1 ≡ f → f2 ∘ f1 ≗ f.
/2 width=4 by after_mono/ qed-.

(* Specific forward lemmas on after *****************************************)

lemma after_fwd_hd: ∀f2,f1,f,n1,n. f2 ⊚ n1@f1 ≡ n@f → f2@❴n1❵ = n.
#f2 #f1 #f #n1 #n #H lapply (after_fwd_at ? n1 0 … H) -H [1,2,3: // ]
/3 width=2 by at_inv_O1, sym_eq/
qed-.

lemma after_fwd_tls: ∀f,f1,n1,f2,n2,n. n2@f2 ⊚ n1@f1 ≡ n@f →
                     (↓*[n1]f2) ⊚ f1 ≡ f.
#f #f1 #n1 elim n1 -n1
[ #f2 #n2 #n #H elim (after_inv_xpx … H) -H //
| #n1 #IH * #m1 #f2 #n2 #n #H elim (after_inv_xnx … H) -H [2,3: // ]
  #m #Hm #H destruct /2 width=3 by/
]
qed-.

lemma after_inv_apply: ∀f2,f1,f,n2,n1,n. n2@f2 ⊚ n1@f1 ≡ n@f →
                       (n2@f2)@❴n1❵ = n ∧ (↓*[n1]f2) ⊚ f1 ≡ f.
/3 width=3 by after_fwd_tls, after_fwd_hd, conj/ qed-.
