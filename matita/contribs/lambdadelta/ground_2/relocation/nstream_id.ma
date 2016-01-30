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
include "ground_2/relocation/nstream_lift.ma".
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

lemma isid_id: 𝐈⦃𝐈𝐝⦄.
// qed.

lemma isid_push: ∀f. 𝐈⦃f⦄ → 𝐈⦃↑f⦄.
#f #H normalize >id_unfold /2 width=1 by eq_seq/
qed.

(* Basic inversion lemmas on isid *******************************************)

lemma isid_inv_seq: ∀f,a.  𝐈⦃a@f⦄ → 𝐈⦃f⦄ ∧ a = 0.
#f #a normalize >id_unfold in ⊢ (???%→?);
#H elim (eq_stream_inv_seq ????? H) -H /2 width=1 by conj/
qed-.

lemma isid_inv_push: ∀f. 𝐈⦃↑f⦄ → 𝐈⦃f⦄.
* #a #f #H elim (isid_inv_seq … H) -H //
qed-.

lemma isid_inv_next: ∀f. 𝐈⦃⫯f⦄ → ⊥.
* #a #f #H elim (isid_inv_seq … H) -H
#_ #H destruct
qed-.

(* inversion lemmas on at ***************************************************)

let corec id_inv_at: ∀f. (∀i. @⦃i, f⦄ ≡ i) → f ≐ 𝐈𝐝 ≝ ?.
* #a #f #Ht lapply (Ht 0)
#H lapply (at_inv_O1 … H) -H
#H0 >id_unfold @eq_seq
[ cases H0 -a //
| @id_inv_at -id_inv_at
  #i lapply (Ht (⫯i)) -Ht cases H0 -a
  #H elim (at_inv_SOx … H) -H //
]
qed-.

lemma isid_inv_at: ∀i,f. 𝐈⦃f⦄ → @⦃i, f⦄ ≡ i.
#i elim i -i
[ * #a #f #H elim (isid_inv_seq … H) -H //
| #i #IH * #a #f #H elim (isid_inv_seq … H) -H
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
/3 width=7 by at_repl_back, at_mono, at_id_le/
qed.

(* Inversion lemmas on after ************************************************)

let corec isid_after_sn: ∀f1,f2. 𝐈⦃f1⦄ → f1 ⊚ f2 ≡ f2 ≝ ?.
* #a1 #f1 * * [ | #a2 ] #f2 #H cases (isid_inv_seq … H) -H
#Ht1 #H1
[ @(after_zero … H1) -H1 /2 width=1 by/
| @(after_skip … H1) -H1 /2 width=5 by/
]
qed-.

let corec isid_after_dx: ∀f2,f1. 𝐈⦃f2⦄ → f1 ⊚ f2 ≡ f1 ≝ ?.
* #a2 #f2 * *
[ #f1 #H cases (isid_inv_seq … H) -H
  #Ht2 #H2 @(after_zero … H2) -H2 /2 width=1 by/
| #a1 #f1 #H @(after_drop … a1 a1) /2 width=5 by/
]
qed-.

lemma after_isid_inv_sn: ∀f1,f2,f. f1 ⊚ f2 ≡ f →  𝐈⦃f1⦄ → f2 ≐ f.
/3 width=4 by isid_after_sn, after_mono/
qed-.

lemma after_isid_inv_dx: ∀f1,f2,f. f1 ⊚ f2 ≡ f →  𝐈⦃f2⦄ → f1 ≐ f.
/3 width=4 by isid_after_dx, after_mono/
qed-.
(*
lemma after_inv_isid3: ∀f1,f2,f. f1 ⊚ f2 ≡ f → 𝐈⦃t⦄ → 𝐈⦃t1⦄ ∧ 𝐈⦃t2⦄.
qed-.
*)
