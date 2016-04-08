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

include "basic_2/s_computation/fqup.ma".
include "basic_2/s_computation/fqus.ma".

(* STAR-ITERATED SUPCLOSURE *************************************************)

(* Alternative definition with plus-iterated supclosure *********************)

lemma fqup_fqus: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
/3 width=5 by fqus_strap1, fquq_fqus, fqu_fquq/
qed.

(* Basic_2A1: was: fqus_inv_gen *)
lemma fqus_inv_fqup: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                     ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ ∨ (∧∧ G1 = G2 & L1 = L2 & T1 = T2).
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fqus_ind … H) -G2 -L2 -T2 //
#G #G2 #L #L2 #T #T2 #_ *
[ #H2 * /3 width=5 by fqup_strap1, or_introl/
  * /3 width=1 by fqu_fqup, or_introl/
| * #HG #HL #HT destruct * /2 width=1 by or_introl/
  * /2 width=1 by or_intror/
]
qed-.

(* Advanced properties ******************************************************)

lemma fqus_strap1_fqu: ∀G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊐ ⦃G2, L2, T2⦄ →
                       ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄.
#G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H2 elim (fqus_inv_fqup … H1) -H1
[ /2 width=5 by fqup_strap1/
| * /2 width=1 by fqu_fqup/
]
qed-.

lemma fqus_strap2_fqu: ∀G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊐* ⦃G2, L2, T2⦄ →
                       ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄.
#G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H2 elim (fqus_inv_fqup … H2) -H2
[ /2 width=5 by fqup_strap2/
| * /2 width=1 by fqu_fqup/
]
qed-.

lemma fqus_fqup_trans: ∀G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G, L, T⦄ → ⦃G, L, T⦄ ⊐+ ⦃G2, L2, T2⦄ →
                       ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄.
#G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 #H2 @(fqup_ind … H2) -H2 -G2 -L2 -T2
/2 width=5 by fqus_strap1_fqu, fqup_strap1/
qed-.

lemma fqup_fqus_trans: ∀G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G, L, T⦄ →
                       ⦃G, L, T⦄ ⊐* ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄.
#G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 @(fqup_ind_dx … H1) -H1 -G1 -L1 -T1
/3 width=5 by fqus_strap2_fqu, fqup_strap2/
qed-.

(* Advanced inversion lemmas for plus-iterated supclosure *******************)

lemma fqup_inv_step_sn: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                        ∃∃G,L,T. ⦃G1, L1, T1⦄ ⊐ ⦃G, L, T⦄ & ⦃G, L, T⦄ ⊐* ⦃G2, L2, T2⦄.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind_dx … H) -G1 -L1 -T1 /2 width=5 by ex2_3_intro/
#G1 #G #L1 #L #T1 #T #H1 #_ * /4 width=9 by fqus_strap2, fqu_fquq, ex2_3_intro/
qed-.
