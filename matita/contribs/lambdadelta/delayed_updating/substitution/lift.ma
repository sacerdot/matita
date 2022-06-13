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

include "delayed_updating/notation/functions/uparrow_4.ma".
include "delayed_updating/notation/functions/uparrow_2.ma".
include "delayed_updating/syntax/path.ma".
include "ground/relocation/tr_uni.ma".
include "ground/relocation/tr_pap_tls.ma".

(* LIFT FOR PATH ************************************************************)

definition lift_continuation (A:Type[0]) ≝
           tr_map → path → A.

rec definition lift_gen (A:Type[0]) (k:lift_continuation A) (f) (p) on p ≝
match p with
[ list_empty     ⇒ k f (𝐞)
| list_lcons l q ⇒
  match l with
  [ label_d n ⇒ lift_gen (A) (λg,p. k g (𝗱(f＠⧣❨n❩)◗p)) (⇂*[n]f) q
  | label_m   ⇒ lift_gen (A) (λg,p. k g (𝗺◗p)) f q
  | label_L   ⇒ lift_gen (A) (λg,p. k g (𝗟◗p)) (⫯f) q
  | label_A   ⇒ lift_gen (A) (λg,p. k g (𝗔◗p)) f q
  | label_S   ⇒ lift_gen (A) (λg,p. k g (𝗦◗p)) f q
  ]
].

interpretation
  "lift (gneric)"
  'UpArrow A k f p = (lift_gen A k f p).

definition proj_path: lift_continuation … ≝
           λf,p.p.

definition proj_rmap: lift_continuation … ≝
           λf,p.f.

interpretation
  "lift (path)"
  'UpArrow f p = (lift_gen ? proj_path f p).

interpretation
  "lift (relocation map)"
  'UpArrow p f = (lift_gen ? proj_rmap f p).

(* Basic constructions ******************************************************)

lemma lift_empty (A) (k) (f):
      k f (𝐞) = ↑{A}❨k, f, 𝐞❩.
// qed.

lemma lift_d_sn (A) (k) (p) (n) (f):
      ↑❨(λg,p. k g (𝗱(f＠⧣❨n❩)◗p)), ⇂*[n]f, p❩ = ↑{A}❨k, f, 𝗱n◗p❩.
// qed.

lemma lift_m_sn (A) (k) (p) (f):
      ↑❨(λg,p. k g (𝗺◗p)), f, p❩ = ↑{A}❨k, f, 𝗺◗p❩.
// qed.

lemma lift_L_sn (A) (k) (p) (f):
      ↑❨(λg,p. k g (𝗟◗p)), ⫯f, p❩ = ↑{A}❨k, f, 𝗟◗p❩.
// qed.

lemma lift_A_sn (A) (k) (p) (f):
      ↑❨(λg,p. k g (𝗔◗p)), f, p❩ = ↑{A}❨k, f, 𝗔◗p❩.
// qed.

lemma lift_S_sn (A) (k) (p) (f):
      ↑❨(λg,p. k g (𝗦◗p)), f, p❩ = ↑{A}❨k, f, 𝗦◗p❩.
// qed.

(* Basic constructions with proj_path ***************************************)

lemma lift_path_empty (f):
      (𝐞) = ↑[f]𝐞.
// qed.

(* Basic constructions with proj_rmap ***************************************)

lemma lift_rmap_empty (f):
      f = ↑[𝐞]f.
// qed.

lemma lift_rmap_d_sn (f) (p) (n):
      ↑[p](⇂*[ninj n]f) = ↑[𝗱n◗p]f.
// qed.

lemma lift_rmap_m_sn (f) (p):
      ↑[p]f = ↑[𝗺◗p]f.
// qed.

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
[ <lift_rmap_m_sn <lift_rmap_m_sn //
| <lift_rmap_A_sn <lift_rmap_A_sn //
| <lift_rmap_S_sn <lift_rmap_S_sn //
]
qed.

(* Advanced constructions with proj_rmap and path_rcons *********************)

lemma lift_rmap_d_dx (f) (p) (n):
      ⇂*[ninj n](↑[p]f) = ↑[p◖𝗱n]f.
// qed.

lemma lift_rmap_m_dx (f) (p):
      ↑[p]f = ↑[p◖𝗺]f.
// qed.

lemma lift_rmap_L_dx (f) (p):
      (⫯↑[p]f) = ↑[p◖𝗟]f.
// qed.

lemma lift_rmap_A_dx (f) (p):
      ↑[p]f = ↑[p◖𝗔]f.
// qed.

lemma lift_rmap_S_dx (f) (p):
      ↑[p]f = ↑[p◖𝗦]f.
// qed.

lemma lift_rmap_pap_d_dx (f) (p) (n) (m):
      ↑[p]f＠⧣❨m+n❩ = ↑[p◖𝗱n]f＠⧣❨m❩+↑[p]f＠⧣❨n❩.
// qed.
