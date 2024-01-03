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

include "delayed_updating/syntax/preterm_proper.ma".
include "delayed_updating/syntax/preterm_inner.ma".
include "delayed_updating/unwind/unwind2_prototerm.ma".
include "delayed_updating/unwind/unwind2_path_append.ma".
include "ground/lib/subset_or.ma".

(* TAILED UNWIND FOR PRETERM ************************************************)

(* Basic inversions *********************************************************)

lemma in_comp_inv_unwind2_bi (f) (t1) (t2) (p):
      t1 ∪ t2 ϵ 𝐓 → p ϵ t1 →
      ▼[f]p ϵ ▼[f]t2 → p ϵ t2.
#f #t1 #t2 #p #Ht #Hp * #r #Hr #H0
lapply (eq_des_unwind2_path_bi_structure … H0) -H0 #H0
<(term_structure_inj … Ht … H0) -H0
/2 width=1 by subset_or_in_dx, subset_or_in_sn/
qed-.

(* Basic constructions ******************************************************)

(* Constructions with term_slice ********************************************)

lemma in_comp_slice_unwind2_bi (f) (t) (p) (r) (l):
      t ϵ 𝐓 → p◖l ϵ t → r ϵ t →
      r ϵ ↑p → ▼[f]r ϵ ↑⊗p.
#f #t #p #r #l #Ht #Hp #Hr * #s #_ #H0 destruct
<unwind2_path_append_ppc_dx //
/2 width=8 by term_in_comp_path_append_des_sn_rcons/
qed.





(*  
  
  Hr : (▼[f]sϵ↑⊗p) → (sϵ↑p)  

  H2s : )
*)  



(*
lemma pippo (f) (p1) (p2):
      ▼[f]p1 ϵ ↑▼[f]p2 → ⊗p1 ϵ ↑⊗p2.
#f #p1 #p2 * #q2
elim (path_inv_ppc q2) #Hq #H0 destruct
[ /2 width=1 by eq_des_unwind2_path_bi_structure/
| elim (unwind2_path_inv_append_ppc_dx … (sym_eq … H0)) -H0 // -Hq
  #r2 #s2 #Hr2 #H1 #H2 destruct
  >(eq_des_unwind2_path_structure … Hr2) -f -p2 //
]
qed-.

lemma unwind2_term_preterm (f) (t):
      t ϵ 𝐓 → ▼[f]t ϵ 𝐓.
#f #t * #H1 #H2
@mk_preterm_axs
[ #p1 #p2 * #r1 #Hr1 #H1 * #r2 #Hr2 #H2 #Hp destruct
  lapply (pippo … Hp) -Hp #Hr
  lapply (H1 … Hr)

  lapply (H1 … Hr1 Hr2) #H0
*)
