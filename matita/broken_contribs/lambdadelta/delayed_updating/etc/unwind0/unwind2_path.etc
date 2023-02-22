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

include "delayed_updating/unwind0/unwind1_path.ma".
include "delayed_updating/notation/functions/black_downtriangle_2.ma".

(* EXTENDED UNWIND FOR PATH *************************************************)

definition unwind2_path (f) (p) ≝
           ▼↑[f]p.

interpretation
  "extended unwind (path)"
  'BlackDownTriangle f p = (unwind2_path f p).

(* Basic constructions ******************************************************)

lemma unwind2_path_unfold (f) (p):
      ▼↑[f]p = ▼[f]p.
// qed.

lemma unwind2_path_id (p):
      ▼p = ▼[𝐢]p.
// qed.

lemma unwind2_path_empty (f):
      (𝐞) = ▼[f]𝐞.
// qed.

lemma unwind2_path_d_empty (f) (n):
      (𝗱(f@❨n❩)◗𝐞) = ▼[f](𝗱n◗𝐞).
// qed.

lemma unwind2_path_d_lcons (f) (p) (l) (n:pnat):
      ▼[𝐮❨f@❨n❩❩](l◗p) = ▼[f](𝗱n◗l◗p).
#f #p #l #n
<unwind2_path_unfold in ⊢ (???%);
<lift_path_d_sn <lift_path_id <unwind1_path_d_lcons //
qed.

lemma unwind2_path_m_sn (f) (p):
      ▼[f]p = ▼[f](𝗺◗p).
#f #p
<unwind2_path_unfold in ⊢ (???%);
<lift_path_m_sn //
qed.

lemma unwind2_path_L_sn (f) (p):
      (𝗟◗▼[⫯f]p) = ▼[f](𝗟◗p).
#f #p
<unwind2_path_unfold in ⊢ (???%);
<lift_path_L_sn //
qed.

lemma unwind2_path_A_sn (f) (p):
      (𝗔◗▼[f]p) = ▼[f](𝗔◗p).
#f #p
<unwind2_path_unfold in ⊢ (???%);
<lift_path_A_sn //
qed.

lemma unwind2_path_S_sn (f) (p):
      (𝗦◗▼[f]p) = ▼[f](𝗦◗p).
#f #p
<unwind2_path_unfold in ⊢ (???%);
<lift_path_S_sn //
qed.

(* Main constructions *******************************************************)

theorem unwind2_path_after_id_sn (p) (f):
        ▼[f]p = ▼▼[f]p.
// qed.

(* Constructions with stream_eq *********************************************)

lemma unwind2_path_eq_repl (p):
      stream_eq_repl … (λf1,f2. ▼[f1]p = ▼[f2]p).
#p #f1 #f2 #Hf
<unwind2_path_unfold <unwind2_path_unfold
<(lift_path_eq_repl … Hf) -Hf //
qed.

(* Advanced eliminations with path ******************************************)

lemma path_ind_unwind2 (Q:predicate …):
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
