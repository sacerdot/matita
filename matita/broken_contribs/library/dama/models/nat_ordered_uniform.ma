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

include "dama/models/nat_uniform.ma".  
include "dama/bishop_set_rewrite.ma".
include "dama/ordered_uniform.ma".

definition nat_ordered_uniform_space:ordered_uniform_space.
 apply (mk_ordered_uniform_space (mk_ordered_uniform_space_ ℕ ℕ (refl_eq ? ℕ)));
simplify; intros 10;  cases H (_); cases (H7 y); apply H8; cases (H7 s);
lapply (H11 H1) as H13; apply (le_le_eq);
[2: apply (le_transitive ??? H5); apply (Le≪ ? H13); assumption;
|1: assumption;
|3: change with (le (os_r ℕ) (\snd y) (\fst y));
    apply (ge_transitive ??? H5);apply (ge_transitive ???? H4);
    change with (le (os_l ℕ) (\fst s) (\snd s));
    apply (Le≫ ? H13); apply le_reflexive;
|4: assumption;]
qed. 
 
interpretation "Ordered uniform space N" 'N = nat_ordered_uniform_space.
