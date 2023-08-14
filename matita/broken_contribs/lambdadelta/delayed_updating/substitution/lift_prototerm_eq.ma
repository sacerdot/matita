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

(**) (* reverse include *)
include "ground/lib/subset_ext_equivalence.ma".
include "delayed_updating/substitution/lift_path_eq.ma".
include "delayed_updating/substitution/lift_prototerm.ma".

(* LIFT FOR PROTOTERM *******************************************************)

(* Constructions with subset_eq *********************************************)

lemma lift_term_eq_repl_sn (t):
      compatible_2_fwd … fbr_eq (subset_eq …) (λf.🠡[f]t).
/3 width=1 by subset_equivalence_ext_f1_exteq, lift_path_eq_repl/
qed.

lemma lift_term_eq_repl_dx (f):
      compatible_2_fwd … (subset_eq …) (subset_eq …) (λt.🠡[f]t).
/2 width=1 by subset_equivalence_ext_f1_bi/
qed.

lemma lift_term_id_sn (t):
      t ⊆ 🠡[𝐢]t.
#t #p #Hp
>(lift_path_id p)
/2 width=1 by in_comp_lift_path_term/
qed-.

lemma lift_term_id_dx (t):
      🠡[𝐢]t ⊆ t.
#t #p * #q #Hq #H destruct //
qed-.

lemma lift_term_id (t):
      t ⇔ 🠡[𝐢]t.
/3 width=2 by lift_term_id_dx, lift_term_id_sn, conj/
qed.

lemma lift_term_grafted_sn (f) (t) (p):
      🠡[🠢[p]f](t⋔p) ⊆ (🠡[f]t)⋔(🠡[f]p).
#f #t #p #q * #r #Hr #H0 destruct
/2 width=3 by ex2_intro/
qed-.

lemma lift_term_grafted_dx (f) (t) (p):
      (🠡[f]t)⋔(🠡[f]p) ⊆ 🠡[🠢[p]f](t⋔p).
#f #t #p #q * #r #Hr #H0
elim (lift_path_inv_append_sn … (sym_eq … H0)) -H0
#p0 #q0 #Hp0 #Hq0 #H0 destruct
lapply (lift_path_inj … Hp0) -Hp0 #Hp0 destruct
/2 width=1 by in_comp_lift_path_term/
qed-.

lemma lift_term_grafted (f) (t) (p):
      🠡[🠢[p]f](t⋔p) ⇔ (🠡[f]t)⋔(🠡[f]p).
/3 width=1 by lift_term_grafted_sn, lift_term_grafted_dx, conj/ qed.

lemma lift_term_grafted_S (f) (t) (p):
      🠡[🠢[p]f](t⋔(p◖𝗦)) ⇔ (🠡[f]t)⋔((🠡[f]p)◖𝗦).
// qed.
