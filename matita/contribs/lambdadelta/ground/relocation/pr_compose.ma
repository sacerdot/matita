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

include "ground/relocation/pr_after_after.ma".

(* FUNCTIONAL COMPOSITION FOR PARTIAL RELOCATION MAPS ***********************)

corec definition pr_compose: pr_map → pr_map → pr_map.
* * #g2 [ #f1 | * * #g1 ]
[ @pr_next @(pr_compose g2 f1)
| @pr_next @(pr_compose g2 g1)
| @pr_push @(pr_compose g2 g1)
]
defined.

interpretation
  "functional composition (partial relocation maps)"
  'compose f2 f1 = (pr_compose f2 f1).

(* Basic constructions ******************************************************)

lemma pr_compose_unfold_refl (f2) (f1): ⫯(f2∘f1) = (⫯f2)∘(⫯f1).
#f2 #f1
<(stream_unfold … ((⫯f2)∘(⫯f1))) in ⊢ (???%); //
qed.

lemma pr_compose_unfold_push (f2) (f1): ↑(f2∘f1) = (⫯f2)∘(↑f1).
#f2 #f1
<(stream_unfold … ((⫯f2)∘(↑f1))) in ⊢ (???%); //
qed.

(*** compose_next *)
lemma pr_compose_unfold_next (f2) (f1):
      ↑(f2∘f1) = (↑f2)∘f1.
#f2 #f1
<(stream_unfold … ((↑f2)∘f1)) in ⊢ (???%); //
qed.

(* Main constructions *******************************************************)

(*** after_total *)
corec theorem pr_after_total (f2) (f1):
              f2 ⊚ f1 ≘ f2∘f1.
cases (pr_map_split_tl f2)*
[ cases (pr_map_split_tl f1) * ]
[ @pr_after_refl /2 width=7 by/
| @pr_after_push /2 width=7 by/
| @pr_after_next /2 width=5 by/
]
qed.

(* Main inversions **********************************************************)

(*** after_inv_total *)
lemma pr_after_inv_total: ∀f2,f1,f. f2 ⊚ f1 ≘ f → f2 ∘ f1 ≡ f.
/2 width=4 by pr_after_mono/ qed-.
