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

include "basic_2/reduction/lpx_aaa.ma".
include "basic_2/computation/cpxs.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL COMPUTATION ON TERMS *****************)

(* Properties about atomic arity assignment on terms ************************)

lemma cpxs_aaa_conf: ∀h,g,G,L,T1,A. ⦃G, L⦄ ⊢ T1 ⁝ A →
                     ∀T2. ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2 → ⦃G, L⦄ ⊢ T2 ⁝ A.
#h #g #G #L #T1 #A #HT1 #T2 #HT12
@(TC_Conf3 … HT1 ? HT12) -A -T1 -T2 /2 width=5 by cpx_aaa_conf/
qed-.

lemma cprs_aaa_conf: ∀G,L,T1,A. ⦃G, L⦄ ⊢ T1 ⁝ A → ∀T2. ⦃G, L⦄ ⊢ T1 ➡* T2 → ⦃G, L⦄ ⊢ T2 ⁝ A.
/3 width=5 by cpxs_aaa_conf, cprs_cpxs/ qed-.
