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

include "ground/arith/nat_psucc.ma".
include "delayed_updating/syntax/path_beta.ma".
include "delayed_updating/syntax/prototerm.ma".
include "delayed_updating/notation/functions/subset_f_4.ma".

(* BALANCED REDUCTION EXTENDED FOCUS ****************************************)

definition brxf (p) (b) (q) (n:ℕ): 𝒫❨ℙ❩ ≝
           ↑𝐫❨p,b,q,⁤↑n❩.

interpretation
  "balanced reduction extended focus (subset of paths)"
  'SubsetF p b q n = (brxf p b q n).

(* Basic constructions ******************************************************)

lemma brxf_unfold (p) (b) (q) (n):
      ↑𝐫❨p,b,q,⁤↑n❩ = 𝐅❨p,b,q,n❩.
//
qed.

(* Basic inversions *********************************************************)

(* REPLACED by term_in_slice_inv_gen
lemma in_comp_brxf_inv_gen (x) (p) (b) (q) (n):
      x ϵ 𝐅❨p,b,q,n❩ →
      ∃y. 𝐫❨p,b,q,⁤↑n❩●y = x.
#x #p #b #q #n #H0 * #y #_ #H0 destruct
/2 width=2 by ex_intro/
qed-.
*)
