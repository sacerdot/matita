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

include "basic_2/rt_transition/cnx_cnx.ma".
include "basic_2/rt_computation/cpxs.ma".

(* UNBOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Properties with normal forms *********************************************)

lemma cpxs_cnx (h) (G) (L) (T1):
      (∀T2. ❪G,L❫ ⊢ T1 ⬈*[h] T2 → T1 ≛ T2) → ❪G,L❫ ⊢ ⬈[h] 𝐍❪T1❫.
/3 width=1 by cpx_cpxs/ qed.

(* Inversion lemmas with normal terms ***************************************)

lemma cpxs_inv_cnx1 (h) (G) (L):
      ∀T1,T2. ❪G,L❫ ⊢ T1 ⬈*[h] T2 → ❪G,L❫ ⊢ ⬈[h] 𝐍❪T1❫ → T1 ≛ T2.
#h #G #L #T1 #T2 #H @(cpxs_ind_dx … H) -T1
/5 width=9 by cnx_teqx_trans, teqx_trans/
qed-.
