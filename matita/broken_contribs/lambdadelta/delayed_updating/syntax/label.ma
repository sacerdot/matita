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

(* A SYSTEM OF λ-CALCULUS WITH DELAYED UPDATING
 * Initial invocation: - Patience on me to gain peace and perfection! -
 *)

include "delayed_updating/notation/functions/category_l_0.ma".
include "delayed_updating/notation/functions/nodelabel_d_1.ma".
include "delayed_updating/notation/functions/edgelabel_l_0.ma".
include "delayed_updating/notation/functions/edgelabel_a_0.ma".
include "delayed_updating/notation/functions/edgelabel_s_0.ma".
include "ground/arith/nat.ma".

(* LABEL ********************************************************************)

inductive label: Type[0] ≝
(* Note: label_d (𝟎) denotes a cleared inner variable *)
| label_d: ℕ → label
| label_L: label
| label_A: label
| label_S: label
.

interpretation
  "label ()"
  'CategoryL = (label).

interpretation
  "variable reference by depth (label)"
  'NodeLabelD k = (label_d k).

interpretation
  "name-free functional abstruction (label)"
  'EdgeLabelL = (label_L).

interpretation
  "application (label)"
  'EdgeLabelA = (label_A).

interpretation
  "side branch (label)"
  'EdgeLabelS = (label_S).

(* Basic inversions *********************************************************)

lemma eq_inv_d_bi (n1) (n2):
      (𝗱n1) = 𝗱n2 → n1 = n2.
#n1 #n2 #H0 destruct //
qed-.

(* Advanced destructions ****************************************************)

lemma label_is_d (l):
      ∨∨ ∃k. 𝗱k = l
       | ∀k. 𝗱k = l → ⊥.
* [ /3 width=2 by ex_intro, or_introl/ ]
@or_intror #k #H0 destruct
qed-.

lemma eq_label_dec (l1) (l2):
      Decidable (l1 =❪𝕃❫ l2).
* [ #k1 ] * [1,5,9,13: #k2 ]
[ elim (eq_nat_dec k1 k2) #Hnk destruct ]
/2 width=1 by or_introl/
@or_intror #H0 destruct
/2 width=1 by/
qed-.
