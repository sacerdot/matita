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

include "ground/relocation/tr_compose_pap.ma".
include "ground/relocation/tr_uni_pap.ma".
include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/black_downtriangle_4.ma".
include "delayed_updating/notation/functions/black_downtriangle_2.ma".

(* UNWIND FOR PATH **********************************************************)

definition unwind_continuation (A:Type[0]) ≝
tr_map → path → A.

rec definition unwind_gen (A:Type[0]) (k:unwind_continuation A) (f) (p) on p ≝
match p with
[ list_empty     ⇒ k f (𝐞)
| list_lcons l q ⇒
  match l with
  [ label_d n ⇒
    match q with
    [ list_empty     ⇒ unwind_gen (A) (λg,p. k g (𝗱(f@❨n❩)◗p)) (f∘𝐮❨n❩) q
    | list_lcons _ _ ⇒ unwind_gen (A) k (f∘𝐮❨n❩) q
    ]
  | label_m   ⇒ unwind_gen (A) k f q
  | label_L   ⇒ unwind_gen (A) (λg,p. k g (𝗟◗p)) (⫯f) q
  | label_A   ⇒ unwind_gen (A) (λg,p. k g (𝗔◗p)) f q
  | label_S   ⇒ unwind_gen (A) (λg,p. k g (𝗦◗p)) f q
  ]
].

interpretation
  "unwind (gneric)"
  'BlackDownTriangle A k f p = (unwind_gen A k f p).

definition proj_path: unwind_continuation … ≝
           λf,p.p.

definition proj_rmap: unwind_continuation … ≝
           λf,p.f.

interpretation
  "unwind (path)"
  'BlackDownTriangle f p = (unwind_gen ? proj_path f p).

interpretation
  "unwind (relocation map)"
  'BlackDownTriangle p f = (unwind_gen ? proj_rmap f p).

(* Basic constructions ******************************************************)

lemma unwind_empty (A) (k) (f):
      k f (𝐞) = ▼{A}❨k, f, 𝐞❩.
// qed.

lemma unwind_d_empty_sn (A) (k) (n) (f):
      ▼❨(λg,p. k g (𝗱(f@❨n❩)◗p)), f∘𝐮❨ninj n❩, 𝐞❩ = ▼{A}❨k, f,
𝗱n◗𝐞❩.
// qed.

lemma unwind_d_lcons_sn (A) (k) (p) (l) (n) (f):
      ▼❨k, f∘𝐮❨ninj n❩, l◗p❩ = ▼{A}❨k, f, 𝗱n◗l◗p❩.
// qed.

lemma unwind_m_sn (A) (k) (p) (f):
      ▼❨k, f, p❩ = ▼{A}❨k, f, 𝗺◗p❩.
// qed.

lemma unwind_L_sn (A) (k) (p) (f):
      ▼❨(λg,p. k g (𝗟◗p)), ⫯f, p❩ = ▼{A}❨k, f, 𝗟◗p❩.
// qed.

lemma unwind_A_sn (A) (k) (p) (f):
      ▼❨(λg,p. k g (𝗔◗p)), f, p❩ = ▼{A}❨k, f, 𝗔◗p❩.
// qed.

lemma unwind_S_sn (A) (k) (p) (f):
      ▼❨(λg,p. k g (𝗦◗p)), f, p❩ = ▼{A}❨k, f, 𝗦◗p❩.
// qed.

(* Basic constructions with proj_path ***************************************)

lemma unwind_path_empty (f):
      (𝐞) = ▼[f]𝐞.
// qed.

lemma unwind_path_d_empty_sn (f) (n):
      𝗱(f@❨n❩)◗𝐞 = ▼[f](𝗱n◗𝐞).
// qed.

lemma unwind_path_d_lcons_sn (f) (p) (l) (n):
      ▼[f∘𝐮❨ninj n❩](l◗p) = ▼[f](𝗱n◗l◗p).
// qed.

lemma unwind_path_m_sn (f) (p):
      ▼[f]p = ▼[f](𝗺◗p).
// qed.

(* Basic constructions with proj_rmap ***************************************)

lemma unwind_rmap_empty (f):
      f = ▼[𝐞]f.
// qed.

lemma unwind_rmap_d_sn (f) (p) (n):
      ▼[p](f∘𝐮❨ninj n❩) = ▼[𝗱n◗p]f.
#f * // qed.

lemma unwind_rmap_m_sn (f) (p):
      ▼[p]f = ▼[𝗺◗p]f.
// qed.

lemma unwind_rmap_L_sn (f) (p):
      ▼[p](⫯f) = ▼[𝗟◗p]f.
// qed.

lemma unwind_rmap_A_sn (f) (p):
      ▼[p]f = ▼[𝗔◗p]f.
// qed.

lemma unwind_rmap_S_sn (f) (p):
      ▼[p]f = ▼[𝗦◗p]f.
// qed.

(* Advanced constructions with proj_rmap and path_append ********************)

lemma unwind_rmap_append (p2) (p1) (f):
      ▼[p2]▼[p1]f = ▼[p1●p2]f.
#p2 #p1 elim p1 -p1 // * [ #n ] #p1 #IH #f //
[ <unwind_rmap_m_sn <unwind_rmap_m_sn //
| <unwind_rmap_A_sn <unwind_rmap_A_sn //
| <unwind_rmap_S_sn <unwind_rmap_S_sn //
]
qed.

(* Advanced constructions with proj_rmap and path_rcons *********************)

lemma unwind_rmap_d_dx (f) (p) (n):
      (▼[p]f)∘𝐮❨ninj n❩ = ▼[p◖𝗱n]f.
// qed.

lemma unwind_rmap_m_dx (f) (p):
      ▼[p]f = ▼[p◖𝗺]f.
// qed.

lemma unwind_rmap_L_dx (f) (p):
      (⫯▼[p]f) = ▼[p◖𝗟]f.
// qed.

lemma unwind_rmap_A_dx (f) (p):
      ▼[p]f = ▼[p◖𝗔]f.
// qed.

lemma unwind_rmap_S_dx (f) (p):
▼[p]f = ▼[p◖𝗦]f.
// qed.

lemma unwind_rmap_pap_d_dx (f) (p) (n) (m):
      ▼[p]f@❨m+n❩ = ▼[p◖𝗱n]f@❨m❩.
#f #p #n #m
<unwind_rmap_d_dx <tr_compose_pap <tr_uni_pap //
qed.

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
