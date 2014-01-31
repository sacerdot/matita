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

include "basic_2/substitution/cpys_alt.ma".
include "basic_2/reduction/cpx.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL REDUCTION FOR TERMS ******************)

(* Properties on context-sensitive extended multiple substitution for terms *)

lemma cpys_cpx: ∀h,g,G,L,T1,T2,d,e. ⦃G, L⦄ ⊢ T1 ▶*[d, e] T2 → ⦃G, L⦄ ⊢ T1 ➡[h, g] T2.
#h #g #G #L #T1 #T2 #d #e #H @(cpys_ind_alt … H) -G -L -T1 -T2 -d -e
/2 width=7 by cpx_delta, cpx_bind, cpx_flat/
qed.

lemma cpy_cpx: ∀h,g,G,L,T1,T2,d,e. ⦃G, L⦄ ⊢ T1 ▶[d, e] T2 → ⦃G, L⦄ ⊢ T1 ➡[h, g] T2.
/3 width=3 by cpy_cpys, cpys_cpx/ qed.
