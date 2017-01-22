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

include "basic_2/computation/fprs_aaa.ma".
include "basic_2/equivalence/fpcs_fpcs.ma".

(* CONTEXT-FREE PARALLEL EQUIVALENCE ON CLOSURES ****************************)

(* Main properties about atomic arity assignment on terms *******************)

theorem aaa_fpcs_mono: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⬌* ⦃L2, T2⦄ →
                       ∀A1. L1 ⊢ T1 ⁝ A1 → ∀A2. L2 ⊢ T2 ⁝ A2 →
                       A1 = A2.
#L1 #L2 #T1 #T2 #H12 #A1 #HT1 #A2 #HT2
elim (fpcs_inv_fprs … H12) -H12 #L #T #H1 #H2
lapply (aaa_fprs_conf … HT1 … H1) -L1 -T1 #HT1
lapply (aaa_fprs_conf … HT2 … H2) -L2 -T2 #HT2
lapply (aaa_mono … HT1 … HT2) -L -T //
qed-.
