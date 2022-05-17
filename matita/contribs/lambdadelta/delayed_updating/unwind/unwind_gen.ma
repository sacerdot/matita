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

include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/black_diamond_2.ma".
include "ground/relocation/tr_pap.ma".

(* GENERIC UNWIND FOR PATH **************************************************)

rec definition unwind_gen (f) (p) on p ≝
match p with
[ list_empty     ⇒ 𝐞
| list_lcons l q ⇒
  match l with
  [ label_d n ⇒
    match q with
    [ list_empty     ⇒ 𝗱((f n)@❨n❩)◗(unwind_gen f q)
    | list_lcons _ _ ⇒ unwind_gen f q
    ]
  | label_m   ⇒ unwind_gen f q
  | label_L   ⇒ l◗(unwind_gen f q)
  | label_A   ⇒ l◗(unwind_gen f q)
  | label_S   ⇒ l◗(unwind_gen f q)
  ]
].

interpretation
  "generic unwind (path)"
  'BlackDiamond f p = (unwind_gen f p).

(* Basic constructions ******************************************************)

lemma unwind_gen_empty (f):
      (𝐞) = ◆[f]𝐞.
// qed.

lemma unwind_gen_d_empty (f) (n):
      𝗱((f n)@❨n❩)◗𝐞 = ◆[f](𝗱n◗𝐞).
// qed.

lemma unwind_gen_d_lcons (f) (p) (l) (n):
      ◆[f](l◗p) = ◆[f](𝗱n◗l◗p).
// qed.

lemma unwind_gen_m_sn (f) (p):
      ◆[f]p = ◆[f](𝗺◗p).
// qed.

lemma unwind_gen_L_sn (f) (p):
      (𝗟◗◆[f]p) = ◆[f](𝗟◗p).
// qed.

lemma unwind_gen_A_sn (f) (p):
      (𝗔◗◆[f]p) = ◆[f](𝗔◗p).
// qed.

lemma unwind_gen_S_sn (f) (p):
      (𝗦◗◆[f]p) = ◆[f](𝗦◗p).
// qed.

(* Advanced eliminations with path ******************************************)

lemma path_ind_unwind (Q:predicate …):
      Q (𝐞) →
      (∀n. Q (𝐞) → Q (𝗱n◗𝐞)) →
      (∀n,l,p. Q (l◗p) → Q (𝗱n◗l◗p)) →
      (∀p. Q p → Q (𝗺◗p)) →
      (∀p. Q p → Q (𝗟◗p)) →
      (∀p. Q p → Q (𝗔◗p)) →
      (∀p. Q p → Q (𝗦◗p)) →
      ∀p. Q p.
#Q #IH1 #IH2 #IH3 #IH4 #IH5 #IH6 #IH7 #p
elim p -p [| * [ #n * ] ]
/2 width=1 by/
qed-.
