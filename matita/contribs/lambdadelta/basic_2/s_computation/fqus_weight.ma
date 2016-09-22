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

include "basic_2/s_transition/fquq_weight.ma".
include "basic_2/s_computation/fqus.ma".

(* STAR-ITERATED SUPCLOSURE *************************************************)

(* Forward lemmas with weight for closures **********************************)

lemma fqus_fwd_fw: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ → ♯{G2, L2, T2} ≤ ♯{G1, L1, T1}.
#G1 #G2 #L1 #L2 #T1 #T2 #H @(fqus_ind … H) -L2 -T2
/3 width=3 by fquq_fwd_fw, transitive_le/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma fqus_inv_refl_atom3: ∀I,G,L,X. ⦃G, L, ⓪{I}⦄ ⊐* ⦃G, L, X⦄ → ⓪{I} = X.
#I #G #L #X #H elim (fqus_inv_fqu_sn … H) -H * //
#G0 #L0 #T0 #H1 #H2 lapply (fqu_fwd_fw … H1) lapply (fqus_fwd_fw … H2) -H2 -H1
#H2 #H1 lapply (le_to_lt_to_lt … H2 H1) -G0 -L0 -T0
#H elim (lt_le_false … H) -H /2 width=1 by monotonic_le_plus_r/
qed-.  
