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

lemma in_comp_brd (t) (p) (y) (b) (q) (n):
      y ϵ ⋔[p◖𝗦]t →
      (p●𝗔◗(⓪b)●𝗟◗q)●𝗱(⁤↑(♭b+n))◗y ϵ 𝐃❨t,p,b,q,n❩.
#t #p  #y #b #q #n #Hx <brd_unfold
/3 width=1 by pt_append_in/
qed.

(* Basic inversions *********************************************************)

lemma in_comp_brd_inv_gen (t) (p) (x) (b) (q) (n):
      x ϵ 𝐃❨t,p,b,q,n❩ →
      ∃∃y. y ϵ ⋔[p◖𝗦]t & (p●𝗔◗(⓪b)●𝗟◗q)●𝗱(⁤↑(♭b+n))◗y = x.
#t #p #x #b #q #n <brd_unfold
* #z * #y #Hy #H1 #H2 destruct
/2 width=5 by ex2_intro/
qed-.
