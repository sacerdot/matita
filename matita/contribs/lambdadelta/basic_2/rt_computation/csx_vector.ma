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

include "static_2/syntax/term_vector.ma".
include "basic_2/rt_computation/csx.ma".

(* STRONGLY NORMALIZING TERMS VECTORS FOR UNBOUND PARALLEL RT-TRANSITION ****)

definition csxv (h) (G) (L): predicate (list term) ≝
           all … (csx h G L).

interpretation
   "strong normalization for unbound context-sensitive parallel rt-transition (term vector)"
   'PRedTyStrong h G L Ts = (csxv h G L Ts).

(* Basic inversion lemmas ***************************************************)

lemma csxv_inv_cons (h) (G) (L):
      ∀T,Ts. ❪G,L❫ ⊢ ⬈*𝐒[h] T⨮Ts →
      ∧∧ ❪G,L❫ ⊢ ⬈*𝐒[h] T & ❪G,L❫ ⊢ ⬈*𝐒[h] Ts.
normalize // qed-.

(* Basic forward lemmas *****************************************************)

lemma csx_fwd_applv (h) (G) (L):
      ∀T,Vs. ❪G,L❫ ⊢ ⬈*𝐒[h] ⒶVs.T →
      ∧∧ ❪G,L❫ ⊢ ⬈*𝐒[h] Vs & ❪G,L❫ ⊢ ⬈*𝐒[h] T.
#h #G #L #T #Vs elim Vs -Vs /2 width=1 by conj/
#V #Vs #IHVs #HVs
lapply (csx_fwd_pair_sn … HVs) #HV
lapply (csx_fwd_flat_dx … HVs) -HVs #HVs
elim (IHVs HVs) -IHVs -HVs /3 width=1 by conj/
qed-.
