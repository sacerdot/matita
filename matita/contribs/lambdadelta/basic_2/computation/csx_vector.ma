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
                 λh,o,G,L. all … (csx h o G L).

interpretation
   "context-sensitive strong normalization (term vector)"
   'SN h o G L Ts = (csxv h o G L Ts).

(* Basic inversion lemmas ***************************************************)

lemma csxv_inv_cons: ∀h,o,G,L,T,Ts. ⦃G, L⦄ ⊢ ⬊*[h, o] T @ Ts →
                     ⦃G, L⦄ ⊢ ⬊*[h, o] T ∧ ⦃G, L⦄ ⊢ ⬊*[h, o] Ts.
normalize // qed-.

(* Basic forward lemmas *****************************************************)

lemma csx_fwd_applv: ∀h,o,G,L,T,Vs. ⦃G, L⦄ ⊢ ⬊*[h, o] Ⓐ Vs.T →
                     ⦃G, L⦄ ⊢ ⬊*[h, o] Vs ∧ ⦃G, L⦄ ⊢ ⬊*[h, o] T.
#h #o #G #L #T #Vs elim Vs -Vs /2 width=1 by conj/
#V #Vs #IHVs #HVs
lapply (csx_fwd_pair_sn … HVs) #HV
lapply (csx_fwd_flat_dx … HVs) -HVs #HVs
elim (IHVs HVs) -IHVs -HVs /3 width=1 by conj/
qed-.
