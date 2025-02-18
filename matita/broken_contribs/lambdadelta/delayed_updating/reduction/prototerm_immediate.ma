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

include "ground/relocation/fb/fbr_uni.ma".
include "delayed_updating/syntax/path_depth.ma".
include "delayed_updating/syntax/path_clear.ma".
include "delayed_updating/substitution/lift_prototerm.ma".
include "delayed_updating/notation/functions/subset_i_5.ma".

(* BALANCED REDUCTION IMMEDIATE SUBREDUCT *************************************)

definition bri (t) (p) (b) (q) (n): 𝒫❨ℙ❩ ≝
           (p●𝗔◗(⓪b)●𝗟◗q)●🠡[𝐮❨⁤↑(♭b+n)❩]⋔[p◖𝗦]t
.


interpretation
  "balanced reduction immediate subreduct (subset of paths)"
  'SubsetI t p b q n = (bri t p b q n).

(* Basic constructions ******************************************************)

lemma bri_unfold (t) (p) (b) (q) (n):
      (p●𝗔◗(⓪b)●𝗟◗q)●🠡[𝐮❨⁤↑(♭b+n)❩]⋔[p◖𝗦]t = 𝐈❨t,p,b,q,n❩.
//
qed.
