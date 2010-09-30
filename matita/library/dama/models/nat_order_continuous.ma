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

include "dama/models/increasing_supremum_stabilizes.ma".
include "dama/models/nat_ordered_uniform.ma".

lemma nat_us_is_oc: ∀s:‡ℕ.order_continuity (segment_ordered_uniform_space ℕ s).
intros 3; split; intros 3; cases H1; cases H2; clear H2 H1; cases H; clear H;
[1: cases (increasing_supremum_stabilizes s a H1 ? H2); 
    exists [apply w1]; intros; 
    apply (restrict nat_ordered_uniform_space s ??? H4);     
    generalize in match (H ? H5);
    cases x; intro; 
    generalize in match (refl_eq ? (a i):a i = a i);
    generalize in match (a i) in ⊢ (?? % ? → %); intro X; cases X; clear X;  
    intro; rewrite < H9 in H7; simplify; rewrite < H7; simplify;
    apply (us_phi1 nat_uniform_space ? H3); simplify; apply (eq_reflexive (us_carr nat_uniform_space));
|2: cases (increasing_supremum_stabilizes_r s a H1 ? H2); 
    exists [apply w1]; intros; 
    apply (restrict nat_ordered_uniform_space s ??? H4);     
    generalize in match (H ? H5);
    cases x; intro; 
    generalize in match (refl_eq ? (a i):a i = a i);
    generalize in match (a i) in ⊢ (?? % ? → %); intro X; cases X; clear X;  
    intro; rewrite < H9 in H7; simplify; rewrite < H7; simplify;
    apply (us_phi1 nat_uniform_space ? H3); simplify; apply (eq_reflexive (us_carr nat_uniform_space));]
qed.
    
