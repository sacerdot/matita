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

include "delayed_updating/substitution/fsubst.ma".
include "delayed_updating/substitution/lift_prototerm_eq.ma".

(* FOCALIZED SUBSTITUTION ***************************************************)

(* Constructions with lift for preterm **************************************)

lemma lift_term_fsubst_sn (f) (t) (u) (p):
      (🠡[f]t)[⋔(🠡[f]p)←🠡[🠢[p]f]u] ⊆ 🠡[f](t[⋔p←u]).
#f #t #u #p #ql * *
[ #rl * #r #Hr #H1 #H2 destruct
  >lift_path_append
  /4 width=3 by in_comp_lift_path_term, or_introl, ex2_intro/
| * #q #Hq #H1 #H0
  @(ex2_intro … H1) @or_intror @conj // -Hq #r #H2 destruct
  /2 width=2 by/
]
qed-.

lemma lift_term_fsubst_dx (f) (t) (u) (p):
      (🠡[f](t[⋔p←u])) ⊆ (🠡[f]t)[⋔(🠡[f]p)←🠡[🠢[p]f]u].
#f #t #u #p #ql * #q * *
[ #r #Hu #H1 #H2 destruct
  @or_introl @ex2_intro
  [|| <lift_path_append // ]
  /2 width=3 by ex2_intro/
| #Hq #H0 #H1 destruct
  @or_intror @conj [ /2 width=1 by in_comp_lift_path_term/ ] -Hq #r #Hr
  elim (lift_path_inv_append_sn … Hr) -Hr #s1 #s2 #Hs1 #_ #H1 destruct
  lapply (lift_path_inj … Hs1) -Hs1 #H1 destruct 
  /2 width=2 by/
]
qed-.

lemma lift_term_fsubst (f) (t) (u) (p):
      (🠡[f]t)[⋔(🠡[f]p)←🠡[🠢[p]f]u] ⇔ 🠡[f](t[⋔p←u]).
/3 width=1 by lift_term_fsubst_sn, conj, lift_term_fsubst_dx/ qed.
