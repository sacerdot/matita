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

include "delayed_updating/unwind0/unwind1_rmap.ma".
include "delayed_updating/notation/functions/black_righttriangle_2.ma".

(* EXTENDED UNWIND FOR RELOCATION MAP ***************************************)

definition unwind2_rmap (f) (p): tr_map ≝
           (▶↑[f]p)∘(↑[p]f).

interpretation
  "extended unwind (relocation map)"
  'BlackRightTriangle f p = (unwind2_rmap f p).

(* Basic constructions ******************************************************)

lemma unwind2_rmap_unfold (f) (p):
      (▶↑[f]p)∘(↑[p]f) = ▶[f]p.
// qed.

lemma unwind2_rmap_m_sn (f) (p):
      ▶[f]p = ▶[f](𝗺◗p).
#f #p
<unwind2_rmap_unfold in ⊢ (???%);
<lift_rmap_m_sn <lift_path_m_sn //
qed.

lemma unwind2_rmap_L_sn (f) (p):
      ▶[⫯f]p = ▶[f](𝗟◗p).
#f #p
<unwind2_rmap_unfold in ⊢ (???%);
<lift_rmap_L_sn <lift_path_L_sn //
qed.

lemma unwind2_rmap_A_sn (f) (p):
      ▶[f]p = ▶[f](𝗔◗p).
#f #p
<unwind2_rmap_unfold in ⊢ (???%);
<lift_rmap_A_sn <lift_path_A_sn //
qed.

lemma unwind2_rmap_S_sn (f) (p):
      ▶[f]p = ▶[f](𝗦◗p).
#f #p
<unwind2_rmap_unfold in ⊢ (???%);
<lift_rmap_S_sn <lift_path_S_sn //
qed.
