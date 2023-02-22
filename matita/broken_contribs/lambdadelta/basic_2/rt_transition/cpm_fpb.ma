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

include "basic_2/rt_transition/fpb_fqup.ma".
include "basic_2/rt_transition/cpm_cpx.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Forward lemmas with rst-transition for closures **************************)

(* Basic_2A1: includes: cpr_fpbq *)
(* Basic_2A1: uses: cpm_fpbq *)
lemma cpm_fwd_fpb (h) (n) (G) (L):
      ∀T1,T2. ❨G,L❩ ⊢ T1 ➡[h,n] T2 → ❨G,L,T1❩ ≽ ❨G,L,T2❩.
/3 width=3 by cpx_fpb, cpm_fwd_cpx/ qed-.
