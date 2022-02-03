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

include "ground/lib/subset_equivalence.ma".
include "delayed_updating/syntax/preterm.ma".
include "delayed_updating/substitution/lift_structure.ma".
include "delayed_updating/substitution/lift_prototerm.ma".

(* LIFT FOR PRETERM *********************************************************)

(* Constructions with subset_equivalence ************************************)

lemma lift_grafted_S_sn (f) (t) (p):
      ↑[↑[p]f](t⋔(p◖𝗦)) ⊆ (↑[f]t)⋔((⊗p)◖𝗦).
#f #t #p #q * #r #Hr #H0 destruct
@(ex2_intro … Hr) -Hr
<list_append_rcons_sn <list_append_rcons_sn
<lift_append_proper_dx //
qed-.

lemma lift_grafted_S_dx (f) (t) (p): p ϵ ▵t → t ϵ 𝐓 →
      (↑[f]t)⋔((⊗p)◖𝗦) ⊆ ↑[↑[p]f](t⋔(p◖𝗦)).
#f #t #p #Hp #Ht #q * #r #Hr
<list_append_rcons_sn #H0
elim (lift_inv_append_proper_dx … (sym_eq … H0)) -H0 //
#p0 #q0 #Hp0 #Hq0 #H0 destruct
<(Ht … Hp0) [|*: /2 width=2 by ex_intro/ ] -p
elim (lift_path_inv_S_sn … (sym_eq … Hq0)) -Hq0
#r1 #r2 #Hr1 #Hr2 #H0 destruct
lapply (preterm_in_root_append_inv_structure_empty_dx … p0 … Ht Hr1)
[ /2 width=2 by ex_intro/ ] -Hr1 #Hr1 destruct
/2 width=1 by in_comp_lift_bi/
qed-.

lemma lift_grafted_S (f) (t) (p): p ϵ ▵t → t ϵ 𝐓 →
      ↑[↑[p]f](t⋔(p◖𝗦)) ⇔ (↑[f]t)⋔((⊗p)◖𝗦).
/3 width=1 by lift_grafted_S_sn, conj, lift_grafted_S_dx/ qed.
