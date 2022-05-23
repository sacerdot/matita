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
include "delayed_updating/notation/functions/nec_r_1.ma".

(* REVERSE FOR PATH *********************************************************)

rec definition reverse (p) on p: path ≝
match p with
[ list_empty     ⇒ 𝐞
| list_lcons l q ⇒ (reverse q)◖l
].

interpretation
  "reverse (path)"
  'NEcR p = (reverse p).

(* Basic constructions ******************************************************)

lemma reverse_empty: 𝐞 = 𝐞ᴿ.
// qed.

lemma reverse_lcons (p) (l): pᴿ◖l = (l◗p)ᴿ.
// qed.

(* Main constructions *******************************************************)

theorem reverse_append (p1) (p2):
        (p2ᴿ)●(p1ᴿ) = (p1●p2)ᴿ.
#p1 elim p1 -p1 //
#l1 #p1 #IH #p2
<list_append_lcons_sn <reverse_lcons <reverse_lcons //
qed.

(* Constructions with list_rcons ********************************************)

lemma reverse_rcons (p) (l):
      l◗(pᴿ) = (p◖l)ᴿ.
#p #l
<reverse_append //
qed.

(* Main constructions *******************************************************)

theorem reverse_revrse (p):
        p = pᴿᴿ.
#p elim p -p //
#l #p #IH
<reverse_lcons <reverse_rcons //
qed.
