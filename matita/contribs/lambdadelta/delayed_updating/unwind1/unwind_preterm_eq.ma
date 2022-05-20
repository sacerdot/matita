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
include "delayed_updating/syntax/path_structure_inner.ma".
include "delayed_updating/syntax/preterm.ma".
include "delayed_updating/unwind1/unwind_structure.ma".
include "delayed_updating/unwind1/unwind_prototerm.ma".

(* UNWIND FOR PRETERM *******************************************************)

(* Constructions with subset_equivalence ************************************)

lemma unwind_grafted_sn (f) (t) (p): p ϵ 𝐈 →
      ▼[▼[p]f](t⋔p) ⊆ (▼[f]t)⋔(⊗p).
#f #t #p #Hp #q * #r #Hr #H0 destruct
@(ex2_intro … Hr) -Hr
<unwind_append_inner_sn //
qed-.

lemma unwind_grafted_dx (f) (t) (p): p ϵ 𝐈 → p ϵ ▵t → t ϵ 𝐓 →
      (▼[f]t)⋔(⊗p) ⊆ ▼[▼[p]f](t⋔p).
#f #t #p #H1p #H2p #Ht #q * #r #Hr #H0
elim (unwind_inv_append_inner_sn … (sym_eq … H0)) -H0 //
#p0 #q0 #Hp0 #Hq0 #H0 destruct
<(Ht … Hp0) [|*: /2 width=2 by ex_intro/ ] -p
/2 width=1 by in_comp_unwind_bi/
qed-.

lemma unwind_grafted (f) (t) (p): p ϵ 𝐈 → p ϵ ▵t → t ϵ 𝐓 →
      ▼[▼[p]f](t⋔p) ⇔ (▼[f]t)⋔(⊗p).
/3 width=1 by unwind_grafted_sn, conj, unwind_grafted_dx/ qed.


lemma unwind_grafted_S_dx (f) (t) (p): p ϵ ▵t → t ϵ 𝐓 →
      (▼[f]t)⋔((⊗p)◖𝗦) ⊆ ▼[▼[p]f](t⋔(p◖𝗦)).
#f #t #p #Hp #Ht #q * #r #Hr
<list_append_rcons_sn #H0
elim (unwind_inv_append_proper_dx … (sym_eq … H0)) -H0 //
#p0 #q0 #Hp0 #Hq0 #H0 destruct
<(Ht … Hp0) [|*: /2 width=2 by ex_intro/ ] -p
elim (unwind_path_inv_S_sn … (sym_eq … Hq0)) -Hq0
#r1 #r2 #Hr1 #Hr2 #H0 destruct
lapply (preterm_in_root_append_inv_structure_empty_dx … p0 … Ht Hr1)
[ /2 width=2 by ex_intro/ ] -Hr1 #Hr1 destruct
/2 width=1 by in_comp_unwind_bi/
qed-.

lemma unwind_grafted_S (f) (t) (p): p ϵ ▵t → t ϵ 𝐓 →
      ▼[▼[p]f](t⋔(p◖𝗦)) ⇔ (▼[f]t)⋔((⊗p)◖𝗦).
#f #t #p #Hp #Ht
@conj
[ >unwind_rmap_S_dx >structure_S_dx
  @unwind_grafted_sn //
| /2 width=1 by unwind_grafted_S_dx/
]
qed.