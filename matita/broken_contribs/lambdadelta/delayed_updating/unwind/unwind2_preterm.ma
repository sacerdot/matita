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
include "ground/subsets/subset_or.ma".

(* TAILED UNWIND FOR PRETERM ************************************************)

(* Inversions with preterm **************************************************)

lemma unwind2_path_inj (f) (t) (p1) (p2):
      t ϵ 𝐓 → p1 ϵ t → p2 ϵ t → ▼[f]p1 = ▼[f]p2 → p1 = p2.
#f #t #p1 #p2 #Ht #Hp1 #Hp2 #Hp12
/3 width=4 by eq_des_unwind2_path_bi_structure, term_structure_inj/
qed-.

lemma in_comp_inv_unwind2_bi (f) (t1) (t2) (p):
      t1 ∪ t2 ϵ 𝐓 → p ϵ t1 →
      ▼[f]p ϵ ▼[f]t2 → p ϵ t2.
#f #t1 #t2 #p #Ht #Hp * #r #Hr #H0
<(unwind2_path_inj … Ht … H0) -H0
/2 width=1 by subset_or_in_dx, subset_or_in_sn/
qed-.

(* Constructions with preterm and term_slice ********************************)

lemma in_comp_slice_unwind2_bi (f) (t) (p) (r) (l):
      t ϵ 𝐓 → p◖l ϵ t → r ϵ t →
      r ϵ ↑p → ▼[f]r ϵ ↑⊗p.
#f #t #p #r #l #Ht #Hp #Hr * #s #_ #H0 destruct
<unwind2_path_append_ppc_dx //
/2 width=8 by term_in_comp_path_append_des_sn_rcons/
qed.

(****************************************************************************)

(* Note: proof in TODO *)
axiom unwind2_preterm (f) (t):
      t ϵ 𝐓 → ▼[f]t ϵ 𝐓.
