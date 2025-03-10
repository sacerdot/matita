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

include "delayed_updating/syntax/prototerm.ma".
include "delayed_updating/notation/functions/subset_f_3.ma".

(* BALANCED REDUCTION EXTENDED FOCUS ****************************************)

definition brxf (p) (b) (q): 𝒫❨ℙ❩ ≝
           ↑(p●𝗔◗b●𝗟◗q)
.

interpretation
  "balanced reduction extended focus (subset of paths)"
  'SubsetF p b q = (brxf p b q).

(* Basic constructions ******************************************************)

lemma brxf_unfold (p) (b) (q):
      ↑(p●𝗔◗b●𝗟◗q) = 𝐅❨p,b,q❩.
//
qed.

(* Basic inversions *********************************************************)

lemma in_comp_brxf_inv_gen (x) (p) (b) (q):
      x ϵ 𝐅❨p,b,q❩ →
      ∃y. (p●𝗔◗b●𝗟◗q)●y = x.
#x #p #b #q * #y #_ #H0 destruct
/2 width=2 by ex_intro/
qed-.
