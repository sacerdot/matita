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

include "basic_2/notation/relations/pconv_3.ma".
include "basic_2/reduction/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL CONVERSION ON TERMS ***************************)

definition cpc: lenv → relation term ≝
   λL,T1,T2. L ⊢ T1 ➡ T2 ∨ L ⊢ T2 ➡ T1.

interpretation
   "context-sensitive parallel conversion (term)"
   'PConv L T1 T2 = (cpc L T1 T2).

(* Basic properties *********************************************************)

lemma cpc_refl: ∀L. reflexive … (cpc L).
/2 width=1/ qed.

lemma cpc_sym: ∀L. symmetric … (cpc L).
#L #T1 #T2 * /2 width=1/
qed.

(* Basic forward lemmas *****************************************************)

lemma cpc_fwd_cpr: ∀L,T1,T2. L ⊢ T1 ⬌ T2 → ∃∃T. L ⊢ T1 ➡ T & L ⊢ T2 ➡ T.
#L #T1 #T2 * /2 width=3/
qed.
