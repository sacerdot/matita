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

include "delayed_updating/unwind_k/preunwind2_rmap.ma".
include "delayed_updating/syntax/path.ma".

(* TAILED UNWIND FOR RELOCATION MAP *****************************************)

rec definition unwind2_rmap (f) (p) on p: tr_map ≝
match p with
[ list_empty     ⇒ f
| list_lcons l q ⇒ ▶[unwind2_rmap f q]l
].

interpretation
  "tailed unwind (relocation map)"
  'BlackRightTriangle f p = (unwind2_rmap f p).

(* Basic constructions ******************************************************)

lemma unwind2_rmap_empty (f):
      f = ▶[f]𝐞.
// qed.

lemma unwind2_rmap_rcons (f) (p) (l):
      ▶[▶[f]p]l = ▶[f](p◖l).
// qed.

lemma unwind2_rmap_d_dx (f) (p) (k:ℤ⁺):
      ▶[f]p∘𝐮❨k❩ = ▶[f](p◖𝗱k).
// qed.

lemma unwind2_rmap_m_dx (f) (p):
      ▶[f]p = ▶[f](p◖𝗺).
// qed.

lemma unwind2_rmap_L_dx (f) (p):
      (⫯▶[f]p) = ▶[f](p◖𝗟).
// qed.

lemma unwind2_rmap_A_dx (f) (p):
      ▶[f]p = ▶[f](p◖𝗔).
// qed.

lemma unwind2_rmap_S_dx (f) (p):
      ▶[f]p = ▶[f](p◖𝗦).
// qed.

(* Constructions with path_append *******************************************)

lemma unwind2_rmap_append (f) (p) (q):
      ▶[▶[f]p]q = ▶[f](p●q).
#f #p #q elim q -q // #l #q #IH
<unwind2_rmap_rcons <unwind2_rmap_rcons //
qed.

(* Constructions with path_lcons ********************************************)

lemma unwind2_rmap_lcons (f) (p) (l):
      ▶[▶[f]l]p = ▶[f](l◗p).
// qed.

lemma unwind2_rmap_d_sn (f) (p) (k:ℤ⁺):
      ▶[f∘𝐮❨k❩]p = ▶[f](𝗱k◗p).
// qed.

lemma unwind2_rmap_m_sn (f) (p):
      ▶[f]p = ▶[f](𝗺◗p).
// qed.

lemma unwind2_rmap_L_sn (f) (p):
      ▶[⫯f]p = ▶[f](𝗟◗p).
// qed.

lemma unwind2_rmap_A_sn (f) (p):
      ▶[f]p = ▶[f](𝗔◗p).
// qed.

lemma unwind2_rmap_S_sn (f) (p):
      ▶[f]p = ▶[f](𝗦◗p).
// qed.
