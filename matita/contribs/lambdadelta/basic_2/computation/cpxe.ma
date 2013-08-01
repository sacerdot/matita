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

include "basic_2/notation/relations/peval_5.ma".
include "basic_2/computation/cpxs.ma".
include "basic_2/computation/csn.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL EVALUATION ON TERMS ******************)

definition cpxe: ∀h. sd h → lenv → relation term ≝
                 λh,g,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 ∧ ⦃G, L⦄ ⊢ 𝐍[h, g]⦃T2⦄.

interpretation "context-sensitive extended parallel evaluation (term)"
   'PEval h g L T1 T2 = (cpxe h g L T1 T2).

(* Basic_properties *********************************************************)

lemma csn_cpxe: ∀h,g,L,T1. ⦃G, L⦄ ⊢ ⬊*[h, g] T1 → ∃T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] 𝐍⦃T2⦄.
#h #g #L #T1 #H @(csn_ind … H) -T1
#T1 #_ #IHT1
elim (cnx_dec h g L T1) /3 width=3/
* #T #H1T1 #H2T1
elim (IHT1 … H1T1 H2T1) -IHT1 -H2T1 #T2 * /4 width=3/
qed-.
