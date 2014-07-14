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

include "basic_2/notation/relations/predeval_6.ma".
include "basic_2/computation/cpxs.ma".
include "basic_2/computation/csx.ma".

(* EVALUATION FOR CONTEXT-SENSITIVE EXTENDED PARALLEL REDUCTION ON TERMS ****)

definition cpxe: ∀h. sd h → relation4 genv lenv term term ≝
                 λh,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 ∧ ⦃G, L⦄ ⊢ ➡[h, g] 𝐍⦃T2⦄.

interpretation "evaluation for context-sensitive extended parallel reduction (term)"
   'PRedEval h g G L T1 T2 = (cpxe h g G L T1 T2).

(* Basic properties *********************************************************)

lemma csx_cpxe: ∀h,g,G,L,T1. ⦃G, L⦄ ⊢ ⬊*[h, g] T1 → ∃T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] 𝐍⦃T2⦄.
#h #g #G #L #T1 #H @(csx_ind … H) -T1
#T1 #_ #IHT1 elim (cnx_dec h g G L T1) /3 width=3 by ex_intro, conj/
* #T #H1T1 #H2T1 elim (IHT1 … H1T1 H2T1) -IHT1 -H2T1
#T2 * /4 width=3 by cpxs_strap2, ex_intro, conj/
qed-.
