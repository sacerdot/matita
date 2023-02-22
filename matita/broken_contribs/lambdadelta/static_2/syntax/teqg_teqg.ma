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

include "static_2/syntax/teqg.ma".

(* GENERIC EQUIVALENCE ON TERMS *********************************************)

(* Main properties **********************************************************)

theorem teqg_trans (S):
        Transitive … S → Transitive … (teqg S).
#S #HS #T1 #T #H elim H -T1 -T //
[ #s1 #s #Hs1 #X #H
  elim (teqg_inv_sort1 … H) -H /3 width=3 by teqg_sort/
| #I #V1 #V #T1 #T #_ #_ #IHV #IHT #X #H
  elim (teqg_inv_pair1 … H) -H /3 width=1 by teqg_pair/
]
qed-.

theorem teqg_canc_sn (S):
        symmetric … S → Transitive … S →
        left_cancellable … (teqg S).
/3 width=3 by teqg_trans, teqg_sym/ qed-.

theorem teqg_canc_dx (S):
        symmetric … S → Transitive … S →
        right_cancellable … (teqg S).
/3 width=3 by teqg_trans, teqg_sym/ qed-.

theorem teqg_repl (S):
        symmetric … S → Transitive … S →
        replace_2 … (teqg S) (teqg S) (teqg S).
/3 width=3 by teqg_canc_sn, teqg_trans/ qed-.

(* Negated main properies ***************************************************)

theorem teqg_tneqg_trans (S):
        symmetric … S → Transitive … S →
        ∀T1,T. T1 ≛[S] T → ∀T2. (T ≛[S] T2 → ⊥) → T1 ≛[S] T2 → ⊥.
/3 width=3 by teqg_canc_sn/ qed-.

theorem tneqg_teqg_canc_dx (S):
        Transitive … S →
        ∀T1,T. (T1 ≛[S] T → ⊥) → ∀T2. T2 ≛[S] T → T1 ≛[S] T2 → ⊥.
/3 width=3 by teqg_trans/ qed-.
