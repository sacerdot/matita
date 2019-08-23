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

include "basic_2/rt_computation/cpms_cnh.ma".
include "basic_2/rt_computation/cpmhe_csx.ma".
include "basic_2/rt_equivalence/cpes.ma".
include "basic_2/dynamic/cnv_preserve.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Properties with head evaluation for t-bound rt-transition on terms *******)

lemma cnv_cpmhe_trans (a) (h) (G) (L):
      ∀T1. ⦃G,L⦄ ⊢ T1 ![a,h] →
      ∀T2,n. ⦃G,L⦄ ⊢ T1 ➡*[h,n] 𝐍*⦃T2⦄ → ⦃G,L⦄ ⊢ T2 ![a,h].
/3 width=4 by cpmhe_fwd_cpms, cnv_cpms_trans/ qed-.

lemma cnv_R_cpmhe_total (a) (h) (G) (L):
      ∀T1. ⦃G,L⦄ ⊢ T1 ![a,h] → ∃n. R_cpmhe h G L T1 n.
/4 width=2 by cnv_fwd_fsb, fsb_inv_csx, R_cpmhe_total_csx/ qed-.

axiom cnv_R_cpmhe_dec (a) (h) (G) (L):
      ∀T. ⦃G,L⦄ ⊢ T ![a,h] → ∀n. Decidable (R_cpmhe h G L T n).

(* Main inversions with head evaluation for t-bound rt-transition on terms **)

theorem cnv_cpmhe_mono (a) (h) (G) (L):
        ∀T0. ⦃G,L⦄ ⊢ T0 ![a,h] → ∀T1,n1. ⦃G,L⦄ ⊢ T0 ➡*[h,n1] 𝐍*⦃T1⦄ →
        ∀T2,n2. ⦃G,L⦄ ⊢ T0 ➡*[h,n2] 𝐍*⦃T2⦄ →
        ∧∧ ⦃G,L⦄ ⊢ T1 ⬌*[h,n2-n1,n1-n2] T2 & T1 ⩳ T2.
#a #h #G #L #T0 #HT0 #T1 #n1 * #HT01 #HT1 #T2 #n2 * #HT02 #HT2
elim (cnv_cpms_conf … HT0 … HT01 … HT02) -T0 #T0 #HT10 #HT20
/4 width=8 by cpms_div, cpms_inv_cnh_sn, theq_canc_dx, conj/
qed-.
