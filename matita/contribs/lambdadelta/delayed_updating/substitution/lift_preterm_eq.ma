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

lemma pippo (p):
      ⊗p ϵ 𝐈.
#p @(list_ind_rcons … p) -p
[ <structure_empty //
| #p * [ #n ] #IH
  [ <structure_d_dx //
  | <structure_m_dx //
  | <structure_L_dx //
  | <structure_A_dx //
  | <structure_S_dx //
  ]
]
qed.

(* LIFT FOR PRETERM *********************************************************)

(* Constructions with subset_equivalence ************************************)

lemma lift_grafted_sn (f) (t) (p): p ϵ 𝐈 →
      ↑[↑[p]f](t⋔p) ⊆ (↑[f]t)⋔(⊗p).
#f #t #p #Hp #q * #r #Hr #H0 destruct
@(ex2_intro … Hr) -Hr
<lift_append_inner_sn //
qed-.

lemma lift_grafted_dx (f) (t) (p): p ϵ 𝐈 → p ϵ ▵t → t ϵ 𝐓 →
      (↑[f]t)⋔(⊗p) ⊆ ↑[↑[p]f](t⋔p).
#f #t #p #H1p #H2p #Ht #q * #r #Hr #H0
elim (lift_inv_append_inner_sn … (sym_eq … H0)) -H0 //
#p0 #q0 #Hp0 #Hq0 #H0 destruct
<(Ht … Hp0) [|*: /2 width=2 by ex_intro/ ] -p
/2 width=1 by in_comp_lift_bi/
qed-.

lemma lift_grafted (f) (t) (p): p ϵ 𝐈 → p ϵ ▵t → t ϵ 𝐓 →
      ↑[↑[p]f](t⋔p) ⇔ (↑[f]t)⋔(⊗p).
/3 width=1 by lift_grafted_sn, conj, lift_grafted_dx/ qed.

(*

-lemma lift_grafted_S_dx (f) (t) (p): p ϵ ▵t → t ϵ ������ →
-      (↑[f]t)⋔((⊗p)◖������) ⊆ ↑[↑[p]f](t⋔(p◖������)).
-#f #t #p #Hp #Ht #q * #r #Hr
-<list_append_rcons_sn #H0
-elim (lift_inv_append_proper_dx … (sym_eq … H0)) -H0 //
+lemma lift_grafted_dx (f) (t) (p): p ϵ ������ → p ϵ ▵t → t ϵ ������ →
+      (↑[f]t)⋔(⊗p) ⊆ ↑[↑[p]f](t⋔p).
+#f #t #p #H1p #H2p #Ht #q * #r #Hr #H0
+elim (lift_inv_append_inner_sn … (sym_eq … H0)) -H0 //
 #p0 #q0 #Hp0 #Hq0 #H0 destruct
 <(Ht … Hp0) [|*: /2 width=2 by ex_intro/ ] -p
-elim (lift_path_inv_S_sn … (sym_eq … Hq0)) -Hq0
-#r1 #r2 #Hr1 #Hr2 #H0 destruct
-lapply (preterm_in_root_append_inv_structure_empty_dx … p0 … Ht Hr1)
-[ /2 width=2 by ex_intro/ ] -Hr1 #Hr1 destruct
 /2 width=1 by in_comp_lift_bi/
 qed-.
 
-lemma lift_grafted_S (f) (t) (p): p ϵ ▵t → t ϵ ������ →
-      ↑[↑[p]f](t⋔(p◖������)) ⇔ (↑[f]t)⋔((⊗p)◖������).
-/3 width=1 by lift_grafted_S_sn, conj, lift_grafted_S_dx/ qed.
+lemma lift_grafted (f) (t) (p): p ϵ ������ → p ϵ ▵t → t ϵ ������ →
+      ↑[↑[p]f](t⋔p) ⇔ (↑[f]t)⋔(⊗p).
+/3 width=1 by lift_grafted_sn, conj, lift_grafted_dx/ qed.

*)
