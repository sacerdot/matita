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

include "ground/lib/functions.ma".
include "apps_2/notation/models/upspoon_4.ma".
include "apps_2/models/model.ma".

(* MODEL ********************************************************************)

definition vpush (M): nat → dd M → evaluation M → evaluation M ≝
                      λj,d,lv,i. tri … i j (lv i) d (lv (↓i)).

interpretation "push (model evaluation)"
   'UpSpoon M i d lv = (vpush M i d lv).

(* Basic properties *********************************************************)

lemma vpush_lt (M): ∀lv,d,j,i. i < j → (⫯{M}[j←d] lv) i = lv i.
/2 width=1 by tri_lt/ qed-.

lemma vpush_eq (M): ∀lv,d,i. (⫯{M}[i←d] lv) i = d.
/2 width=1 by tri_eq/ qed-.

lemma vpush_gt (M): ∀lv,d,j,i. j < i → (⫯{M}[j←d] lv) i = lv (↓i).
/2 width=1 by tri_gt/ qed-.
