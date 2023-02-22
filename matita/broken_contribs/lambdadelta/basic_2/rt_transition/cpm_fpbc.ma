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

include "basic_2/rt_transition/fpbc_fqup.ma".
include "basic_2/rt_transition/cpm_cpx.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Forward lemmas with proper rst-transition for closures *******************)

(* Basic_2A1: includes: cpr_fpb *)
(* Basic_2A1: uses: cpm_fpb *)
lemma cpm_fwd_fpbc (h) (n) (G) (L):
      ∀T1,T2. ❨G,L❩ ⊢ T1 ➡[h,n] T2 → (T1 ≅ T2 → ⊥) → ❨G,L,T1❩ ≻ ❨G,L,T2❩.
/3 width=3 by cpx_fpbc, cpm_fwd_cpx/ qed-.
