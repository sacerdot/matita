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

include "ground/relocation/tr_compose.ma".
include "ground/relocation/tr_uni.ma".
include "delayed_updating/syntax/path.ma".
include "delayed_updating/notation/functions/uparrow_4.ma".
include "delayed_updating/notation/functions/uparrow_2.ma".

(* LIFT FOR PATH ***********************************************************)

definition lift_continuation (A:Type[0]) ≝
           path → tr_map → A.

(* Note: inner numeric labels are not liftable, so they are removed *)
rec definition lift_gen (A:Type[0]) (k:lift_continuation A) (p) (f) on p ≝
match p with
[ list_empty     ⇒ k (𝐞) f
| list_lcons l q ⇒
  match l with
  [ label_node_d n ⇒
    match q with
    [ list_empty     ⇒ lift_gen (A) (λp. k (𝗱❨f@❨n❩❩◗p)) q (f∘𝐮❨n❩)
    | list_lcons _ _ ⇒ lift_gen (A) k q (f∘𝐮❨n❩)
    ]
  | label_edge_L   ⇒ lift_gen (A) (λp. k (𝗟◗p)) q (⫯f)
  | label_edge_A   ⇒ lift_gen (A) (λp. k (𝗔◗p)) q f
  | label_edge_S   ⇒ lift_gen (A) (λp. k (𝗦◗p)) q f
  ]
].

interpretation
  "lift (gneric)"
  'UpArrow A k p f = (lift_gen A k p f).

definition proj_path (p:path) (f:tr_map) ≝ p.

definition proj_rmap (p:path) (f:tr_map) ≝ f.

interpretation
  "lift (path)"
  'UpArrow f p = (lift_gen ? proj_path p f).

interpretation
  "lift (relocation map)"
  'UpArrow p f = (lift_gen ? proj_rmap p f).

(* Basic constructions ******************************************************)

lemma lift_empty (A) (k) (f):
      k (𝐞) f = ↑{A}❨k, 𝐞, f❩.
// qed.

lemma lift_d_empty_sn (A) (k) (n) (f):
      ↑❨(λp. k (𝗱❨f@❨n❩❩◗p)), 𝐞, f∘𝐮❨ninj n❩❩ = ↑{A}❨k, 𝗱❨n❩◗𝐞, f❩.
// qed.

lemma lift_d_lcons_sn (A) (k) (p) (l) (n) (f):
      ↑❨k, l◗p, f∘𝐮❨ninj n❩❩ = ↑{A}❨k, 𝗱❨n❩◗l◗p, f❩.
// qed.

lemma lift_L_sn (A) (k) (p) (f):
      ↑❨(λp. k (𝗟◗p)), p, ⫯f❩ = ↑{A}❨k, 𝗟◗p, f❩.
// qed.

lemma lift_A_sn (A) (k) (p) (f):
      ↑❨(λp. k (𝗔◗p)), p, f❩ = ↑{A}❨k, 𝗔◗p, f❩.
// qed.

lemma lift_S_sn (A) (k) (p) (f):
      ↑❨(λp. k (𝗦◗p)), p, f❩ = ↑{A}❨k, 𝗦◗p, f❩.
// qed.

(* Basic constructions with proj_path ***************************************)

lemma lift_path_d_empty_sn (f) (n):
      𝗱❨f@❨n❩❩◗𝐞 = ↑[f](𝗱❨n❩◗𝐞).
// qed.

lemma lift_path_d_lcons_sn (f) (p) (l) (n):
      ↑[f∘𝐮❨ninj n❩](l◗p) = ↑[f](𝗱❨n❩◗l◗p).
// qed.

(* Basic constructions with proj_rmap ***************************************)

lemma lift_rmap_d_sn (f) (p) (n):
      ↑[p](f∘𝐮❨ninj n❩) = ↑[𝗱❨n❩◗p]f.
#f * // qed.

lemma lift_rmap_L_sn (f) (p):
      ↑[p](⫯f) = ↑[𝗟◗p]f.
// qed.

lemma lift_rmap_A_sn (f) (p):
      ↑[p]f = ↑[𝗔◗p]f.
// qed.

lemma lift_rmap_S_sn (f) (p):
      ↑[p]f = ↑[𝗦◗p]f.
// qed.

(* Advanced constructions with proj_rmap and path_append ********************)

lemma lift_rmap_append (p2) (p1) (f):
      ↑[p2]↑[p1]f = ↑[p1●p2]f.
#p2 #p1 elim p1 -p1 // * [ #n ] #p1 #IH #f //
[ <lift_rmap_A_sn <lift_rmap_A_sn //
| <lift_rmap_S_sn <lift_rmap_S_sn //
]
qed.

(* Advanced eliminations with path ******************************************)

lemma path_ind_lift (Q:predicate …):
      Q (𝐞) →
      (∀n. Q (𝐞) → Q (𝗱❨n❩◗𝐞)) →
      (∀n,l,p. Q (l◗p) → Q (𝗱❨n❩◗l◗p)) →
      (∀p. Q p → Q (𝗟◗p)) →
      (∀p. Q p → Q (𝗔◗p)) →
      (∀p. Q p → Q (𝗦◗p)) →
      ∀p. Q p.
#Q #IH1 #IH2 #IH3 #IH4 #IH5 #IH6 #p
elim p -p [| * [ #n * ] ]
/2 width=1 by/
qed-.
