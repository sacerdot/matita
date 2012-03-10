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

(* CONTEXT-SENSITIVE STRONGLY NORMALIZING TERM VECTORS **********************)

inductive csnv (L:lenv): predicate (list term) ≝
| csnv_nil: csnv L ◊
| csn_cons: ∀Ts,T. L  ⊢ ⬇* T → csnv L Ts → csnv L (T :: Ts)
.

interpretation
   "context-sensitive strong normalization (term vector)"
   'SN L Ts = (csnv L Ts).

(* Basic inversion lemmas ***************************************************)

fact csnv_inv_cons_aux: ∀L,Ts. L ⊢ ⬇* Ts → ∀U,Us. Ts = U :: Us →
                        L ⊢ ⬇* U ∧ L ⊢ ⬇* Us.
#L #Ts * -Ts
[ #U #Us #H destruct
| #Ts #T #HT #HTs #U #Us #H destruct /2 width=1/
]
qed.

lemma csnv_inv_cons: ∀L,T,Ts. L ⊢ ⬇* T :: Ts → L ⊢ ⬇* T ∧ L ⊢ ⬇* Ts.
/2 width=3/ qed-.

include "basic_2/computation/csn_cpr.ma".

lemma csn_fwd_applv: ∀L,T,Vs. L ⊢ ⬇* Ⓐ Vs. T → L ⊢ ⬇* Vs ∧ L ⊢ ⬇* T.
#L #T #Vs elim Vs -Vs /2 width=1/
#V #Vs #IHVs #HVs
lapply (csn_fwd_pair_sn … HVs) #HV
lapply (csn_fwd_flat_dx … HVs) -HVs #HVs
elim (IHVs HVs) -IHVs -HVs /3 width=1/
qed-.
