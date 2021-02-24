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
include "apps_2/functional/flifts_flifts_basic.ma".
include "apps_2/functional/mf_vlift.ma".

(* MULTIPLE EVALUATION LIFT *************************************************)

(* Properties with extensional equivalence **********************************)

lemma mf_gc_id: ∀j. ⇡[j]mf_gi ≐ mf_gi.
// qed.

lemma mf_vlift_comp (l): compatible_2 … (mf_vlift l) (exteq …) (exteq …).
#l #gv1 #gv2 #Hgv #i
>mf_vlift_rw >mf_vlift_rw //
qed.

(* Main properties with extensional equivalence *****************************)

theorem mf_vlift_swap: ∀l1,l2. l2 ≤ l1 → ∀v. ⇡[l2]⇡[l1]v ≐ ⇡[↑l1]⇡[l2]v.
/2 width=1 by flifts_basic_swap/ qed-.
