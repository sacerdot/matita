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

(* STRONGLY NORMALIZING TERMS VECTORS FOR EXTENDED PARALLEL RT-TRANSITION ***)

definition csxv (G) (L): predicate (list term) ≝
           all … (csx G L).

interpretation
  "strong normalization for extended context-sensitive parallel rt-transition (term vector)"
  'PRedTyStrong G L Ts = (csxv G L Ts).

(* Basic inversion lemmas ***************************************************)

lemma csxv_inv_cons (G) (L):
      ∀T,Ts. ❪G,L❫ ⊢ ⬈*𝐒 T⨮Ts →
      ∧∧ ❪G,L❫ ⊢ ⬈*𝐒 T & ❪G,L❫ ⊢ ⬈*𝐒 Ts.
normalize // qed-.

(* Basic forward lemmas *****************************************************)

lemma csx_fwd_applv (G) (L):
      ∀T,Vs. ❪G,L❫ ⊢ ⬈*𝐒 ⒶVs.T →
      ∧∧ ❪G,L❫ ⊢ ⬈*𝐒 Vs & ❪G,L❫ ⊢ ⬈*𝐒 T.
#G #L #T #Vs elim Vs -Vs /2 width=1 by conj/
#V #Vs #IHVs #HVs
lapply (csx_fwd_pair_sn … HVs) #HV
lapply (csx_fwd_flat_dx … HVs) -HVs #HVs
elim (IHVs HVs) -IHVs -HVs /3 width=1 by conj/
qed-.
