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

include "ground/subsets/subset_le.ma".
include "ground/subsets/subset_and.ma".
include "ground/subsets/subset_listed_1.ma".
include "delayed_updating/syntax/prototerm.ma".
include "delayed_updating/notation/functions/subset_t_0.ma".

(* PRETERM ******************************************************************)

(* Note: the intended model of a preterm is a tree *)
record preterm_posts (t): Prop ≝
  { term_complete_post (p1) (p2):
(* Note: we cannot extend complete paths *)
      p1 ϵ t → p2 ϵ t → p1 ϵ ↑p2 → p1 = p2
  ; term_root_d_post (p) (l1) (k2):
(* Note: root paths do not fork on varible references *)
      p◖l1 ϵ ▵t → p◖𝗱k2 ϵ ▵t → l1 = 𝗱k2
  ; term_root_L_post (p) (l1):
(* Note: root paths do not fork on abstractions *)
      p◖l1 ϵ ▵t → p◖𝗟 ϵ ▵t → l1 = 𝗟
(* Note: applications have arguments *)
  ; term_full_A_post (p):
      p◖𝗔 ϵ ▵t → p◖𝗦 ϵ ▵t
(* application arguments are not empty *)
  ; term_proper_S_post (p):
      p◖𝗦 ⧸ϵ t
  }.

interpretation
  "preterm (prototerm)"
  'SubsetT = (preterm_posts).

(* Basic constructions ******************************************************)

lemma term_le_and_sn_single_dx (t) (p):
      t ϵ 𝐓 → p ϵ t → t ∩ ↑p ⊆ ❴p❵.
#t #p #Ht #Hp #r * #H1r #H2r
lapply (term_complete_post … Ht … H2r) //
qed.

(* Basic destructions *******************************************************)

lemma term_complete_append (t) (p) (q):
      t ϵ 𝐓 → p ϵ t → p●q ϵ t → (𝐞) = q.
#t #p #q #Ht #Hp #Hq
lapply (term_complete_post … Ht … Hq Hp ?) -t [ // ] #H0
@(eq_inv_list_append_dx_dx_refl … (sym_eq … H0))
qed-.
