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

include "ground/lib/list_rcons.ma".

(* MAP FOR LISTS ************************************************************)

rec definition list_map A B (f:A→B) l on l ≝ match l with
[ list_empty       ⇒ (ⓔ)
| list_lcons hd tl ⇒ f hd ⨮ (list_map A B f tl)
].

(* Basic constructions ******************************************************)

lemma list_map_empty (A) (B) (f):
      (ⓔ) = list_map A B f (ⓔ).
//
qed.

lemma list_map_lcons (A) (B) (f) (hd) (tl):
      (f hd) ⨮ list_map … tl = list_map A B f (hd ⨮ tl).
//
qed.

(* Constructions with list_append *******************************************)

lemma list_map_lappend (A) (B) (f) (l1) (l2):
      list_map … f l1 ⨁ list_map … f l2 = list_map A B f (l1 ⨁ l2).
#A #B #f #l1 elim l1 -l1 //
#hd #tl #IH #l2
<list_map_lcons <list_append_lcons_sx <list_map_lcons <IH //
qed.

(* Constructions with list_rcons ********************************************)

lemma list_map_rcons (A) (B) (f) (hd) (tl):
      list_map … hd ⨭ f tl = list_map A B f (hd ⨭ tl).
//
qed.
