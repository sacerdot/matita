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

include "ground_2/notation/functions/uniform_1.ma".
include "ground_2/relocation/rtmap_id.ma".
include "ground_2/relocation/rtmap_isuni.ma".

(* RELOCATION MAP ***********************************************************)

rec definition uni (n:nat) on n: rtmap  ≝ match n with
[ O   ⇒ 𝐈𝐝
| S n ⇒ ⫯(uni n)
].

interpretation "uniform relocation (rtmap)"
   'Uniform n = (uni n).

(* Basic properties *********************************************************)

lemma uni_zero: 𝐈𝐝 = 𝐔❴0❵.
// qed.

lemma uni_succ: ∀n. ⫯𝐔❴n❵ = 𝐔❴⫯n❵.
// qed.

(* Basic inversion lemmas ***************************************************)

lemma uni_inv_push_dx: ∀f,n. 𝐔❴n❵ ≗ ↑f → 0 = n ∧ 𝐈𝐝 ≗ f.
#f * /3 width=5 by eq_inv_pp, conj/
#n <uni_succ #H elim (eq_inv_np … H) -H //
qed-.

lemma uni_inv_push_sn: ∀f,n. ↑f ≗ 𝐔❴n❵ → 0 = n ∧ 𝐈𝐝 ≗ f.
/3 width=1 by uni_inv_push_dx, eq_sym/ qed-.

lemma uni_inv_id_dx: ∀n. 𝐔❴n❵ ≗ 𝐈𝐝 → 0 = n.
#n <id_rew #H elim (uni_inv_push_dx … H) -H //
qed-.

lemma uni_inv_id_sn: ∀n.  𝐈𝐝 ≗ 𝐔❴n❵ → 0 = n.
/3 width=1 by uni_inv_id_dx, eq_sym/ qed-.

lemma uni_inv_next_dx: ∀f,n. 𝐔❴n❵ ≗ ⫯f → ∃∃m. 𝐔❴m❵ ≗ f & ⫯m = n.
#f *
[ <uni_zero <id_rew #H elim (eq_inv_pn … H) -H //
| #n <uni_succ /3 width=5 by eq_inv_nn, ex2_intro/
]
qed-.

lemma uni_inv_next_sn: ∀f,n. ⫯f ≗ 𝐔❴n❵ → ∃∃m. 𝐔❴m❵ ≗ f & ⫯m = n.
/3 width=1 by uni_inv_next_dx, eq_sym/ qed-.

(* Properties with test for identity ****************************************)

lemma uni_isid: ∀f. 𝐈⦃f⦄ → 𝐔❴0❵ ≗ f.
/2 width=1 by eq_id_inv_isid/ qed-.

(* Inversion lemmas with test for identity **********************************)

lemma uni_inv_isid: ∀f. 𝐔❴0❵ ≗ f → 𝐈⦃f⦄.
/2 width=1 by eq_id_isid/ qed-.

(* Properties with finite colength assignment ***************************)

lemma fcla_uni: ∀n. 𝐂⦃𝐔❴n❵⦄ ≘ n.
#n elim n -n /2 width=1 by fcla_isid, fcla_next/
qed.

(* Properties with test for finite colength ***************************)

lemma isfin_uni: ∀n. 𝐅⦃𝐔❴n❵⦄.
/3 width=2 by ex_intro/ qed.

(* Properties with test for uniformity **************************************)

lemma isuni_uni: ∀n. 𝐔⦃𝐔❴n❵⦄.
#n elim n -n /3 width=3 by isuni_isid, isuni_next/
qed.

lemma uni_isuni: ∀f. 𝐔⦃f⦄ → ∃n. 𝐔❴n❵ ≗ f.
#f #H elim H -f /3 width=2 by uni_isid, ex_intro/
#f #_ #g #H * /3 width=6 by eq_next, ex_intro/
qed-.

(* Inversion lemmas with test for uniformity ********************************)

lemma uni_inv_isuni: ∀n,f. 𝐔❴n❵ ≗ f →  𝐔⦃f⦄.
#n elim n -n /3 width=1 by uni_inv_isid, isuni_isid/
#n #IH #x <uni_succ #H elim (eq_inv_nx … H) -H /3 width=3 by isuni_next/
qed-.
