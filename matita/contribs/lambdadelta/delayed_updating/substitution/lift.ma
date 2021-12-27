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

(* Note: inner numeric labels are not liftable, so they are removed *)
rec definition lift_gen (A:Type[0]) (k:?→?→A) (p) (f) on p ≝
match p with
[ list_empty     ⇒ k 𝐞 f
| list_lcons l q ⇒
  match l with
  [ label_node_d n ⇒
    match q with
    [ list_empty     ⇒ lift_gen (A) (λp. k (𝗱❨f@❨n❩❩◗p)) q f
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

lemma lift_L (A) (k) (p) (f):
      ↑❨(λp. k (𝗟◗p)), p, ⫯f❩ = ↑{A}❨k, 𝗟◗p, f❩.
// qed.

(* Basic constructions with proj_path ***************************************)

lemma lift_append (p) (f) (q):
      q●↑[f]p = ↑❨(λp. proj_path (q●p)), p, f❩.
#p elim p -p
[ //
| #l #p #IH #f #q cases l
  [
  | <lift_L in ⊢ (???%);
    >(list_append_rcons_sn ? q) in ⊢ (???(??(λ_.%)??));
    
     <IH 
  normalize >IH
  | //   

(* Constructions with append ************************************************)

theorem lift_append_A (p2) (p1) (f):
        (↑[f]p1)●𝗔◗↑[↑[p1]f]p2 = ↑[f](p1●𝗔◗p2).
#p2 #p1 elim p1 -p1
[ #f normalize 
