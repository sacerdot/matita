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

include "basic_2/grammar/term_vector.ma".
include "basic_2/computation/csn.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERM VECTORS *************)

definition csnv: ∀h. sd h → lenv → predicate (list term) ≝
                 λh,g,L. all … (csn h g L).

interpretation
   "context-sensitive strong normalization (term vector)"
   'SN h g L Ts = (csnv h g L Ts).

(* Basic inversion lemmas ***************************************************)

lemma csnv_inv_cons: ∀h,g,L,T,Ts. ⦃h, L⦄ ⊢ ⬊*[g] T @ Ts →
                     ⦃h, L⦄ ⊢ ⬊*[g] T ∧ ⦃h, L⦄ ⊢ ⬊*[g] Ts.
normalize // qed-.

(* Basic forward lemmas *****************************************************)

lemma csn_fwd_applv: ∀h,g,L,T,Vs. ⦃h, L⦄ ⊢ ⬊*[g] Ⓐ Vs.T →
                     ⦃h, L⦄ ⊢ ⬊*[g] Vs ∧ ⦃h, L⦄ ⊢ ⬊*[g] T.
#h #g #L #T #Vs elim Vs -Vs /2 width=1/
#V #Vs #IHVs #HVs
lapply (csn_fwd_pair_sn … HVs) #HV
lapply (csn_fwd_flat_dx … HVs) -HVs #HVs
elim (IHVs HVs) -IHVs -HVs /3 width=1/
qed-.
