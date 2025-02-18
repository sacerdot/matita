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

include "delayed_updating/syntax/path_depth.ma".
include "delayed_updating/syntax/path_clear.ma".
include "delayed_updating/syntax/prototerm_constructors.ma".
include "delayed_updating/notation/functions/subset_d_5.ma".

(* BALANCED REDUCTION DELAYED SUBREDUCT *************************************)

definition brd (t) (p) (b) (q) (n): 𝒫❨ℙ❩ ≝
           (p●𝗔◗(⓪b)●𝗟◗q)●𝛕(⁤↑(♭b+n)).⋔[p◖𝗦]t
.


interpretation
  "balanced reduction delayed subreduct (subset of paths)"
  'SubsetD t p b q n = (brd t p b q n).

(* Basic constructions ******************************************************)

lemma brd_unfold (t) (p) (b) (q) (n):
      (p●𝗔◗(⓪b)●𝗟◗q)●𝛕(⁤↑(♭b+n)).⋔[p◖𝗦]t = 𝐃❨t,p,b,q,n❩.
//
qed.
