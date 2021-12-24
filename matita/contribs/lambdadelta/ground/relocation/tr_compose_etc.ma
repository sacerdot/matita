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

include "ground/relocation/pstream_tls.ma".
include "ground/relocation/pstream_istot.ma".
include "ground/relocation/rtmap_after.ma".

(* Properties on after (specific) *********************************************)

lemma after_O2: ∀f2,f1,f. f2 ⊚ f1 ≘ f →
                ∀p. p⨮f2 ⊚ ⫯f1 ≘ p⨮f.
#f2 #f1 #f #Hf #p elim p -p
/2 width=7 by gr_after_refl, gr_after_next/
qed.

lemma after_S2: ∀f2,f1,f,p1,p. f2 ⊚ p1⨮f1 ≘ p⨮f →
                ∀p2. p2⨮f2 ⊚ ↑p1⨮f1 ≘ (p+p2)⨮f.
#f2 #f1 #f #p1 #p #Hf #p2 elim p2 -p2
/2 width=7 by gr_after_next, gr_after_push/
qed.

lemma after_apply: ∀p1,f2,f1,f.
      (⫰*[ninj p1] f2) ⊚ f1 ≘ f → f2 ⊚ p1⨮f1 ≘ f2@❨p1❩⨮f.
#p1 elim p1 -p1
[ * /2 width=1 by after_O2/
| #p1 #IH * #p2 #f2 >nsucc_inj <stream_tls_swap
  /3 width=1 by after_S2/
]
qed-.

corec lemma after_total_aux: ∀f2,f1,f. f2 ∘ f1 = f → f2 ⊚ f1 ≘ f.
* #p2 #f2 * #p1 #f1 * #p #f cases p2 -p2
[ cases p1 -p1
  [ #H cases (compose_inv_O2 … H) -H /3 width=7 by gr_after_refl, eq_f2/
  | #p1 #H cases (compose_inv_S2 … H) -H * -p /3 width=7 by gr_after_push/
  ]
| #p2 >gr_next_unfold #H cases (compose_inv_S1 … H) -H * -p >gr_next_unfold
  /3 width=5 by gr_after_next/
]
qed-.

theorem after_total: ∀f1,f2. f2 ⊚ f1 ≘ f2 ∘ f1.
/2 width=1 by after_total_aux/ qed.

(* Inversion lemmas on after (specific) ***************************************)

lemma after_inv_xpx: ∀f2,g2,f,p2,p. p2⨮f2 ⊚ g2 ≘ p⨮f → ∀f1. ⫯f1 = g2 →
                     f2 ⊚ f1 ≘ f ∧ p2 = p.
#f2 #g2 #f #p2 elim p2 -p2
[ #p #Hf #f1 #H2 elim (gr_after_inv_push_bi … Hf … H2) -g2 [|*: // ]
  #g #Hf #H elim (push_inv_seq_dx … H) -H destruct /2 width=1 by conj/
| #p2 #IH #p #Hf #f1 #H2 elim (gr_after_inv_next_sn … Hf) -Hf [|*: // ]
  #g1 #Hg #H1 elim (next_inv_seq_dx … H1) -H1
  #x #Hx #H destruct elim (IH … Hg) [|*: // ] -IH -Hg
  #H destruct /2 width=1 by conj/
]
qed-.

lemma after_inv_xnx: ∀f2,g2,f,p2,p. p2⨮f2 ⊚ g2 ≘ p⨮f → ∀f1. ↑f1 = g2 →
                     ∃∃q. f2 ⊚ f1 ≘ q⨮f & q+p2 = p.
#f2 #g2 #f #p2 elim p2 -p2
[ #p #Hf #f1 #H2 elim (gr_after_inv_push_next … Hf … H2) -g2 [|*: // ]
  #g #Hf #H elim (next_inv_seq_dx … H) -H
  #x #Hx #Hg destruct /2 width=3 by ex2_intro/
| #p2 #IH #p #Hf #f1 #H2 elim (gr_after_inv_next_sn … Hf) -Hf [|*: // ]
  #g #Hg #H elim (next_inv_seq_dx … H) -H
  #x #Hx #H destruct elim (IH … Hg) -IH -Hg [|*: // ]
  #m #Hf #Hm destruct /2 width=3 by ex2_intro/
]
qed-.

lemma after_inv_const: ∀f2,f1,f,p1,p.
      p⨮f2 ⊚ p1⨮f1 ≘ p⨮f → f2 ⊚ f1 ≘ f ∧ 𝟏 = p1.
#f2 #f1 #f #p1 #p elim p -p
[ #H elim (gr_after_inv_push_sn_push … H) -H [|*: // ]
  #g2 #Hf #H elim (push_inv_seq_dx … H) -H /2 width=1 by conj/
| #p #IH #H lapply (gr_after_inv_next_sn_next … H ????) -H /2 width=5 by/
]
qed-.

lemma after_inv_total: ∀f2,f1,f. f2 ⊚ f1 ≘ f → f2 ∘ f1 ≡ f.
/2 width=4 by gr_after_mono/ qed-.

(* Forward lemmas on after (specific) *****************************************)

lemma after_fwd_hd: ∀f2,f1,f,p1,p. f2 ⊚ p1⨮f1 ≘ p⨮f → f2@❨p1❩ = p.
#f2 #f1 #f #p1 #p #H lapply (gr_after_des_pat ? p1 (𝟏) … H) -H [4:|*: // ]
/3 width=2 by at_inv_O1, sym_eq/
qed-.

lemma after_fwd_tls: ∀f,f1,p1,f2,p2,p. p2⨮f2 ⊚ p1⨮f1 ≘ p⨮f →
                     (⫰*[↓p1]f2) ⊚ f1 ≘ f.
#f #f1 #p1 elim p1 -p1
[ #f2 #p2 #p #H elim (after_inv_xpx … H) -H //
| #p1 #IH * #q2 #f2 #p2 #p #H elim (after_inv_xnx … H) -H [|*: // ]
  #x #Hx #H destruct /2 width=3 by/
]
qed-.

lemma after_inv_apply: ∀f2,f1,f,p2,p1,p. p2⨮f2 ⊚ p1⨮f1 ≘ p⨮f →
                       (p2⨮f2)@❨p1❩ = p ∧ (⫰*[↓p1]f2) ⊚ f1 ≘ f.
/3 width=3 by after_fwd_tls, after_fwd_hd, conj/ qed-.

(* Properties on apply ******************************************************)

lemma compose_apply (f2) (f1) (i): f2@❨f1@❨i❩❩ = (f2∘f1)@❨i❩.
/4 width=6 by gr_after_des_pat, at_inv_total, sym_eq/ qed.