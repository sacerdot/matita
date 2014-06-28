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

include "basic_2/notation/relations/suptermstar_6.ma".
include "basic_2/substitution/fquq.ma".
include "basic_2/multiple/fqup.ma".

(* STAR-ITERATED SUPCLOSURE *************************************************)

definition fqus: tri_relation genv lenv term ≝ tri_TC … fquq.

interpretation "star-iterated structural successor (closure)"
   'SupTermStar G1 L1 T1 G2 L2 T2 = (fqus G1 L1 T1 G2 L2 T2).

(* Basic eliminators ********************************************************)

lemma fqus_ind: ∀G1,L1,T1. ∀R:relation3 …. R G1 L1 T1 →
                (∀G,G2,L,L2,T,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊐⸮ ⦃G2, L2, T2⦄ → R G L T → R G2 L2 T2) →
                ∀G2,L2,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ → R G2 L2 T2.
#G1 #L1 #T1 #R #IH1 #IH2 #G2 #L2 #T2 #H
@(tri_TC_star_ind … IH1 IH2 G2 L2 T2 H) //
qed-.

lemma fqus_ind_dx: ∀G2,L2,T2. ∀R:relation3 …. R G2 L2 T2 →
                   (∀G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊐* ⦃G2, L2, T2⦄ → R G L T → R G1 L1 T1) →
                   ∀G1,L1,T1. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ → R G1 L1 T1.
#G2 #L2 #T2 #R #IH1 #IH2 #G1 #L1 #T1 #H
@(tri_TC_star_ind_dx … IH1 IH2 G1 L1 T1 H) //
qed-.

(* Basic properties *********************************************************)

lemma fqus_refl: tri_reflexive … fqus.
/2 width=1 by tri_inj/ qed.

lemma fquq_fqus: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄.
/2 width=1 by tri_inj/ qed.

lemma fqus_strap1: ∀G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                   ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄.
/2 width=5 by tri_step/ qed-.

lemma fqus_strap2: ∀G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊐* ⦃G2, L2, T2⦄ →
                   ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄.
/2 width=5 by tri_TC_strap/ qed-.

lemma fqus_drop: ∀G1,G2,K1,K2,T1,T2. ⦃G1, K1, T1⦄ ⊐* ⦃G2, K2, T2⦄ →
                  ∀L1,U1,e. ⇩[e] L1 ≡ K1 → ⇧[0, e] T1 ≡ U1 →
                  ⦃G1, L1, U1⦄ ⊐* ⦃G2, K2, T2⦄.
#G1 #G2 #K1 #K2 #T1 #T2 #H @(fqus_ind … H) -G2 -K2 -T2
/3 width=5 by fqus_strap1, fquq_fqus, fquq_drop/
qed-.

lemma fqup_fqus: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
/3 width=5 by fqus_strap1, fquq_fqus, fqu_fquq/
qed.

(* Basic forward lemmas *****************************************************)

lemma fqus_fwd_fw: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ → ♯{G2, L2, T2} ≤ ♯{G1, L1, T1}.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fqus_ind … H) -L2 -T2
/3 width=3 by fquq_fwd_fw, transitive_le/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma fqup_inv_step_sn: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                        ∃∃G,L,T. ⦃G1, L1, T1⦄ ⊐ ⦃G, L, T⦄ & ⦃G, L, T⦄ ⊐* ⦃G2, L2, T2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind_dx … H) -G1 -L1 -T1 /2 width=5 by ex2_3_intro/
#G1 #G #L1 #L #T1 #T #H1 #_ * /4 width=9 by fqus_strap2, fqu_fquq, ex2_3_intro/
qed-.
