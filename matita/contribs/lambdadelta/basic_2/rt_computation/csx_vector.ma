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

include "basic_2/syntax/term_vector.ma".
include "basic_2/rt_computation/csx.ma".

(* STRONGLY NORMALIZING TERMS VECTORS FOR UNBOUND PARALLEL RT-TRANSITION ****)

definition csxv: ∀h. sd h → relation3 genv lenv (list term) ≝
                 λh,o,G,L. all … (csx h o G L).

interpretation
   "strong normalization for unbound context-sensitive parallel rt-transition (term vector)"
   'PRedTyStrong h o G L Ts = (csxv h o G L Ts).

(* Basic inversion lemmas ***************************************************)

lemma csxv_inv_cons: ∀h,o,G,L,T,Ts. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T@Ts⦄ →
                     ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄ ∧ ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃Ts⦄.
normalize // qed-.

(* Basic forward lemmas *****************************************************)

lemma csx_fwd_applv: ∀h,o,G,L,T,Vs. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃ⒶVs.T⦄ →
                     ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃Vs⦄ ∧ ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄.
#h #o #G #L #T #Vs elim Vs -Vs /2 width=1 by conj/
#V #Vs #IHVs #HVs
lapply (csx_fwd_pair_sn … HVs) #HV
lapply (csx_fwd_flat_dx … HVs) -HVs #HVs
elim (IHVs HVs) -IHVs -HVs /3 width=1 by conj/
qed-.
