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

include "basic_2/rt_transition/lpx_reqg.ma".
include "basic_2/rt_computation/lpxs_lpx.ma".

(* EXTENDED PARALLEL RT-COMPUTATION FOR FULL LOCAL ENVIRONMENTS *************)

(* Properties with generic equivalence on referred entries ******************)

(* Basic_2A1: uses: lleq_lpxs_trans *)
lemma reqg_lpxs_trans (S) (G) (T:term):
      reflexive … S → symmetric … S →
      ∀L2,K2. ❨G,L2❩ ⊢ ⬈* K2 → ∀L1. L1 ≛[S,T] L2 →
      ∃∃K1. ❨G,L1❩ ⊢ ⬈* K1 & K1 ≛[S,T] K2.
#S #G #T #H1S #H2S #L2 #K2 #H @(lpxs_ind_sn … H) -L2 /2 width=3 by ex2_intro/
#L #L2 #HL2 #_ #IH #L1 #HT
elim (reqg_lpx_trans … HL2 … HT) // -L #L #HL1 #HT
elim (IH … HT) -L2 #K #HLK #HT
/3 width=3 by lpxs_step_sn, ex2_intro/
qed-.

(* Basic_2A1: uses: lpxs_nlleq_inv_step_sn *)
lemma lpxs_rneqg_inv_step_sn (S) (G) (T:term):
      reflexive … S → symmetric … S → Transitive … S →
      (∀s1,s2. Decidable (S s1 s2)) →
      ∀L1,L2. ❨G,L1❩ ⊢ ⬈* L2 → (L1 ≛[S,T] L2 → ⊥) →
      ∃∃L,L0. ❨G,L1❩ ⊢ ⬈ L & L1 ≛[S,T] L → ⊥ & ❨G,L❩ ⊢ ⬈* L0 & L0 ≛[S,T] L2.
#S #G #T #H1S #H2S #H3S #H4S #L1 #L2 #H @(lpxs_ind_sn … H) -L1
[ #H elim H -H /2 width=1 by reqg_refl/
| #L1 #L #H1 #H2 #IH2 #H12 elim (reqg_dec S … L1 L T) // #H
  [ -H1 -H2 elim IH2 -IH2 /3 width=3 by reqg_trans/ -H12
    #L0 #L3 #H1 #H2 #H3 #H4 lapply (reqg_rneqg_trans … H … H2) -H2 //
    #H2 elim (reqg_lpx_trans … H1 … H) -L //
    #L #H1 #H lapply (rneqg_reqg_div … H … H2) -H2 //
    #H2 elim (reqg_lpxs_trans … H3 … H) -L0
    /3 width=8 by reqg_trans, ex4_2_intro/
  | -H12 -IH2 /3 width=6 by reqg_refl, ex4_2_intro/
  ]
]
qed-.
