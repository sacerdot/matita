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

include "ground_2/notation/functions/identity_0.ma".
include "ground_2/notation/relations/isidentity_1.ma".
include "ground_2/relocation/nstream_after.ma".

(* RELOCATION N-STREAM ******************************************************)

let corec id: rtmap ≝ ↑id.

interpretation "identity (nstream)"
   'Identity = (id).

definition isid: predicate rtmap ≝ λf. f ≐ 𝐈𝐝.

interpretation "test for identity (trace)"
   'IsIdentity f = (isid f).

(* Basic properties on id ***************************************************)

lemma id_unfold: 𝐈𝐝 = ↑𝐈𝐝.
>(stream_expand … (𝐈𝐝)) in ⊢ (??%?); normalize //
qed.

(* Basic properties on isid *************************************************)

lemma isid_eq_repl_back: eq_stream_repl_back … isid.
/2 width=3 by eq_stream_canc_sn/ qed-.

lemma isid_eq_repl_fwd: eq_stream_repl_fwd … isid.
/3 width=3 by isid_eq_repl_back, eq_stream_repl_sym/ qed-.

lemma isid_id: 𝐈⦃𝐈𝐝⦄.
// qed.

lemma isid_push: ∀f. 𝐈⦃f⦄ → 𝐈⦃↑f⦄.
#f #H normalize >id_unfold /2 width=1 by eq_seq/
qed.

(* Basic inversion lemmas on isid *******************************************)

lemma isid_inv_seq: ∀f,n.  𝐈⦃n@f⦄ → 𝐈⦃f⦄ ∧ n = 0.
#f #n normalize >id_unfold in ⊢ (???%→?);
#H elim (eq_stream_inv_seq ????? H) -H /2 width=1 by conj/
qed-.

lemma isid_inv_push: ∀f. 𝐈⦃↑f⦄ → 𝐈⦃f⦄.
* #n #f #H elim (isid_inv_seq … H) -H //
qed-.

lemma isid_inv_next: ∀f. 𝐈⦃⫯f⦄ → ⊥.
* #n #f #H elim (isid_inv_seq … H) -H
#_ #H destruct
qed-.

lemma isid_inv_gen: ∀f. 𝐈⦃f⦄ → ∃∃g. 𝐈⦃g⦄ & f = ↑g.
* #n #f #H elim (isid_inv_seq … H) -H
#Hf #H destruct /2 width=3 by ex2_intro/
qed-.

lemma isid_inv_eq_repl: ∀f1,f2. 𝐈⦃f1⦄ → 𝐈⦃f2⦄ → f1 ≐ f2.
/2 width=3 by eq_stream_canc_dx/ qed-.

(* inversion lemmas on at ***************************************************)

let corec id_inv_at: ∀f. (∀i. @⦃i, f⦄ ≡ i) → f ≐ 𝐈𝐝 ≝ ?.
* #n #f #Ht lapply (Ht 0)
#H lapply (at_inv_O1 … H) -H
#H0 >id_unfold @eq_seq
[ cases H0 -n //
| @id_inv_at -id_inv_at
  #i lapply (Ht (⫯i)) -Ht cases H0 -n
  #H elim (at_inv_SOx … H) -H //
]
qed-.

lemma isid_inv_at: ∀i,f. 𝐈⦃f⦄ → @⦃i, f⦄ ≡ i.
#i elim i -i
[ * #n #f #H elim (isid_inv_seq … H) -H //
| #i #IH * #n #f #H elim (isid_inv_seq … H) -H
  /3 width=1 by at_S1/
]
qed-.

lemma isid_inv_at_mono: ∀f,i1,i2. 𝐈⦃f⦄ → @⦃i1, f⦄ ≡ i2 → i1 = i2.
/3 width=6 by isid_inv_at, at_mono/ qed-.

(* Properties on at *********************************************************)

lemma id_at: ∀i. @⦃i, 𝐈𝐝⦄ ≡ i.
/2 width=1 by isid_inv_at/ qed.

lemma isid_at: ∀f. (∀i. @⦃i, f⦄ ≡ i) → 𝐈⦃f⦄.
/2 width=1 by id_inv_at/ qed.

lemma isid_at_total: ∀f. (∀i1,i2. @⦃i1, f⦄ ≡ i2 → i1 = i2) → 𝐈⦃f⦄.
#f #Ht @isid_at
#i lapply (at_total i f)
#H >(Ht … H) in ⊢ (???%); -Ht //
qed.

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
(*
lemma after_inv_isid3: ∀f1,f2,f. f1 ⊚ f2 ≡ f → 𝐈⦃t⦄ → 𝐈⦃t1⦄ ∧ 𝐈⦃t2⦄.
qed-.
*)
