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

include "ground/notation/relations/ist_1.ma".
include "ground/relocation/rtmap_at.ma".

(* RELOCATION MAP ***********************************************************)

definition istot: predicate rtmap ≝ λf. ∀i. ∃j. @❪i,f❫ ≘ j.

interpretation "test for totality (rtmap)"
   'IsT f = (istot f).

(* Basic inversion lemmas ***************************************************)

lemma istot_inv_push: ∀g. 𝐓❪g❫ → ∀f. ⫯f = g → 𝐓❪f❫.
#g #Hg #f #H #i elim (Hg (↑i)) -Hg
#j #Hg elim (at_inv_npx … Hg … H) -Hg -H /2 width=3 by ex_intro/
qed-.

lemma istot_inv_next: ∀g. 𝐓❪g❫ → ∀f. ↑f = g → 𝐓❪f❫.
#g #Hg #f #H #i elim (Hg i) -Hg
#j #Hg elim (at_inv_xnx … Hg … H) -Hg -H /2 width=2 by ex_intro/
qed-.

(* Properties on tl *********************************************************)

lemma istot_tl: ∀f. 𝐓❪f❫ → 𝐓❪⫱f❫.
#f cases (pn_split f) *
#g * -f /2 width=3 by istot_inv_next, istot_inv_push/
qed.

(* Properties on tls ********************************************************)

lemma istot_tls: ∀n,f. 𝐓❪f❫ → 𝐓❪⫱*[n]f❫.
#n @(nat_ind_succ … n) -n //
#n #IH #f #Hf <tls_S
/3 width=1 by istot_tl/
qed.

(* Main forward lemmas on at ************************************************)

corec theorem at_ext: ∀f1,f2. 𝐓❪f1❫ → 𝐓❪f2❫ →
                      (∀i,i1,i2. @❪i,f1❫ ≘ i1 → @❪i,f2❫ ≘ i2 → i1 = i2) →
                      f1 ≡ f2.
#f1 cases (pn_split f1) * #g1 #H1
#f2 cases (pn_split f2) * #g2 #H2
#Hf1 #Hf2 #Hi
[ @(eq_push … H1 H2) @at_ext -at_ext /2 width=3 by istot_inv_push/ -Hf1 -Hf2
  #i #i1 #i2 #Hg1 #Hg2 lapply (Hi (↑i) (↑i1) (↑i2) ??) /2 width=7 by at_push/
| cases (Hf2 (𝟏)) -Hf1 -Hf2 -at_ext
  #j2 #Hf2 cases (at_increasing_strict … Hf2 … H2) -H2
  lapply (Hi (𝟏) (𝟏) j2 … Hf2) /2 width=2 by at_refl/ -Hi -Hf2 -H1
  #H2 #H cases (plt_ge_false … H) -H //
| cases (Hf1 (𝟏)) -Hf1 -Hf2 -at_ext
  #j1 #Hf1 cases (at_increasing_strict … Hf1 … H1) -H1
  lapply (Hi (𝟏) j1 (𝟏) Hf1 ?) /2 width=2 by at_refl/ -Hi -Hf1 -H2
  #H1 #H cases (plt_ge_false … H) -H //
| @(eq_next … H1 H2) @at_ext -at_ext /2 width=3 by istot_inv_next/ -Hf1 -Hf2
  #i #i1 #i2 #Hg1 #Hg2 lapply (Hi i (↑i1) (↑i2) ??) /2 width=5 by at_next/
]
qed-.

(* Advanced properties on at ************************************************)

lemma at_dec: ∀f,i1,i2. 𝐓❪f❫ → Decidable (@❪i1,f❫ ≘ i2).
#f #i1 #i2 #Hf lapply (Hf i1) -Hf *
#j2 #Hf elim (eq_pnat_dec i2 j2)
[ #H destruct /2 width=1 by or_introl/
| /4 width=6 by at_mono, or_intror/
]
qed-.

lemma is_at_dec: ∀f,i2. 𝐓❪f❫ → Decidable (∃i1. @❪i1,f❫ ≘ i2).
#f #i2 #Hf
lapply (dec_plt (λi1.@❪i1,f❫ ≘ i2) … (↑i2)) [| * ]
[ /2 width=1 by at_dec/
| * /3 width=2 by ex_intro, or_introl/
| #H @or_intror * #i1 #Hi12
  /5 width=3 by at_increasing, plt_succ_dx, ex2_intro/
]
qed-.

(* Advanced properties on isid **********************************************)

lemma isid_at_total: ∀f. 𝐓❪f❫ → (∀i1,i2. @❪i1,f❫ ≘ i2 → i1 = i2) → 𝐈❪f❫.
#f #H1f #H2f @isid_at
#i lapply (H1f i) -H1f *
#j #Hf >(H2f … Hf) in ⊢ (???%); -H2f //
qed.
