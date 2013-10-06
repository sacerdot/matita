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
include "basic_2/computation/csx.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERM VECTORS *************)

definition csxv: ∀h. sd h → relation3 genv lenv (list term) ≝
                 λh,g,G,L. all … (csx h g G L).

interpretation
   "context-sensitive strong normalization (term vector)"
   'SN h g G L Ts = (csxv h g G L Ts).

(* Basic inversion lemmas ***************************************************)

lemma csxv_inv_cons: ∀h,g,G,L,T,Ts. ⦃G, L⦄ ⊢ ⬊*[h, g] T @ Ts →
                     ⦃G, L⦄ ⊢ ⬊*[h, g] T ∧ ⦃G, L⦄ ⊢ ⬊*[h, g] Ts.
normalize // qed-.

(* Basic forward lemmas *****************************************************)

lemma csx_fwd_applv: ∀h,g,G,L,T,Vs. ⦃G, L⦄ ⊢ ⬊*[h, g] Ⓐ Vs.T →
                     ⦃G, L⦄ ⊢ ⬊*[h, g] Vs ∧ ⦃G, L⦄ ⊢ ⬊*[h, g] T.
#h #g #G #L #T #Vs elim Vs -Vs /2 width=1/
#V #Vs #IHVs #HVs
lapply (csx_fwd_pair_sn … HVs) #HV
lapply (csx_fwd_flat_dx … HVs) -HVs #HVs
elim (IHVs HVs) -IHVs -HVs /3 width=1/
qed-.
