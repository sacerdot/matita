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

include "static_2/static/reqg_reqg.ma".
include "static_2/static/feqg.ma".

(* GENERIC EQUIVALENCE FOR CLOSURES ON REFERRED ENTRIES *********************)

(* Advanced properties ******************************************************)

lemma feqg_sym (S):
      reflexive … S → symmetric … S →
      tri_symmetric … (feqg S).
#S #H1S #H2S #G1 #G2 #L1 #L2 #T1 #T2 * -G1 -L1 -T1
/3 width=1 by feqg_intro_dx, reqg_sym, teqg_sym/
qed-.

lemma feqg_dec (S):
      (∀s1,s2. Decidable … (S s1 s2)) →
      ∀G1,G2,L1,L2,T1,T2. Decidable (❨G1,L1,T1❩ ≛[S] ❨G2,L2,T2❩).
#S #HS #G1 #G2 #L1 #L2 #T1 #T2
elim (eq_genv_dec G1 G2) #HnG destruct
[ elim (reqg_dec … HS L1 L2 T1) #HnL
  [ elim (teqg_dec … HS T1 T2) #HnT
    [ /3 width=1 by feqg_intro_sn, or_introl/ ]
  ]
]
@or_intror #H
elim (feqg_inv_gen_sn … H) -H #H #HL #HT destruct
/2 width=1 by/
qed-.

(* Main properties **********************************************************)

theorem feqg_trans (S):
        reflexive … S → symmetric … S → Transitive … S →
        tri_transitive … (feqg S).
#S #H1S #H2S #H3S #G1 #G #L1 #L #T1 #T * -G -L -T
#L #T #HL1 #HT1 #G2 #L2 #T2 * -G2 -L2 -T2
/4 width=8 by feqg_intro_sn, reqg_trans, teqg_reqg_div, teqg_trans/
qed-.

theorem feqg_canc_sn (S):
        reflexive … S → symmetric … S → Transitive … S →
        ∀G,G1,L,L1,T,T1. ❨G,L,T❩ ≛[S] ❨G1,L1,T1❩ →
        ∀G2,L2,T2. ❨G,L,T❩ ≛[S] ❨G2,L2,T2❩ → ❨G1,L1,T1❩ ≛[S] ❨G2,L2,T2❩.
/3 width=5 by feqg_trans, feqg_sym/ qed-.

theorem feqg_canc_dx (S):
        reflexive … S → symmetric … S → Transitive … S →
        ∀G1,G,L1,L,T1,T. ❨G1,L1,T1❩ ≛[S] ❨G,L,T❩ →
        ∀G2,L2,T2. ❨G2,L2,T2❩ ≛[S] ❨G,L,T❩ → ❨G1,L1,T1❩ ≛[S] ❨G2,L2,T2❩.
/3 width=5 by feqg_trans, feqg_sym/ qed-.

lemma feqg_reqg_trans (S) (G2) (L) (T2):
      reflexive … S → symmetric … S → Transitive … S →
      ∀G1,L1,T1. ❨G1,L1,T1❩ ≛[S] ❨G2,L,T2❩ →
      ∀L2. L ≛[S,T2] L2 → ❨G1,L1,T1❩ ≛[S] ❨G2,L2,T2❩.
#S #G2 #L #T2 #H1S #H2S #H3S #G1 #L1 #T1 #H1 #L2 #HL2
/4 width=5 by feqg_trans, feqg_intro_sn, teqg_refl/
qed-.

(* Inversion lemmas with generic equivalence on terms ***********************)

(* Basic_2A1: uses: feqg_tneqg_repl_dx *)
lemma feqg_tneqg_trans (S) (G1) (G2) (L1) (L2) (T):
      reflexive … S → symmetric … S → Transitive … S →
      ∀T1. ❨G1,L1,T1❩ ≛[S] ❨G2,L2,T❩ →
      ∀T2. (T ≛[S] T2 → ⊥) → (T1 ≛[S] T2 → ⊥).
#S #G1 #G2 #L1 #L2 #T #H1S #H2S #H3S #T1 #H1 #T2 #HnT2 #HT12
elim (feqg_inv_gen_sn … H1) -H1 #_ #_ #HnT1 -G1 -G2 -L1 -L2
/3 width=3 by teqg_canc_sn/
qed-.
