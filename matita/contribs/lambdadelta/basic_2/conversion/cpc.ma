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

include "basic_2/notation/relations/pconv_4.ma".
include "basic_2/reduction/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL CONVERSION ON TERMS ***************************)

definition cpc: relation4 genv lenv term term ≝
                λG,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡ T2 ∨ ⦃G, L⦄ ⊢ T2 ➡ T1.

interpretation
   "context-sensitive parallel conversion (term)"
   'PConv G L T1 T2 = (cpc G L T1 T2).

(* Basic properties *********************************************************)

lemma cpc_refl: ∀G,L. reflexive … (cpc G L).
/2 width=1/ qed.

lemma cpc_sym: ∀G,L. symmetric … (cpc L G).
#G #L #T1 #T2 * /2 width=1/
qed.

(* Basic forward lemmas *****************************************************)

lemma cpc_fwd_cpr: ∀G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ⬌ T2 → ∃∃T. ⦃G, L⦄ ⊢ T1 ➡ T & ⦃G, L⦄ ⊢ T2 ➡ T.
#G #L #T1 #T2 * /2 width=3/
qed-.
