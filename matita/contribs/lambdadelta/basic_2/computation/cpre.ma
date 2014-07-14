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

include "basic_2/notation/relations/predeval_4.ma".
include "basic_2/computation/cprs.ma".
include "basic_2/computation/csx.ma".

(* EVALUATION FOR CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS *************)

definition cpre: relation4 genv lenv term term ≝
                 λG,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡* T2 ∧ ⦃G, L⦄ ⊢ ➡ 𝐍⦃T2⦄.

interpretation "evaluation for context-sensitive parallel reduction (term)"
   'PRedEval G L T1 T2 = (cpre G L T1 T2).

(* Basic properties *********************************************************)

(* Basic_1: was just: nf2_sn3 *)
lemma csx_cpre: ∀h,g,G,L,T1. ⦃G, L⦄ ⊢ ⬊*[h, g] T1 → ∃T2. ⦃G, L⦄ ⊢ T1 ➡* 𝐍⦃T2⦄.
#h #g #G #L #T1 #H @(csx_ind … H) -T1
#T1 #_ #IHT1 elim (cnr_dec G L T1) /3 width=3 by ex_intro, conj/
* #T #H1T1 #H2T1 elim (IHT1 … H2T1) -IHT1 -H2T1 /2 width=2 by cpr_cpx/
#T2 * /4 width=3 by cprs_strap2, ex_intro, conj/
qed.
