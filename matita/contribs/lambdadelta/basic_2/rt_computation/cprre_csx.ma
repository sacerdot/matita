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

include "basic_2/rt_transition/cpm_cpx.ma".
include "basic_2/rt_transition/cnr_teqx.ma".
include "basic_2/rt_computation/csx.ma".
include "basic_2/rt_computation/cprre.ma".

(* EVALUATION FOR CONTEXT-SENSITIVE PARALLEL R-TRANSITION ON TERMS **********)

(* Properties with strong normalization for unbound rt-transition for terms *)

(* Basic_1: was just: nf2_sn3 *)
(* Basic_2A1: was: csx_cpre *)
lemma cprre_total_csx (h) (G) (L):
      ∀T1. ❪G,L❫ ⊢ ⬈*[h] 𝐒❪T1❫ → ∃T2. ❪G,L❫ ⊢ T1 ➡*𝐍[h,0] T2.
#h #G #L #T1 #H
@(csx_ind … H) -T1 #T1 #_ #IHT1
elim (cnr_dec_teqx h G L T1) [ /3 width=3 by ex_intro, cpmre_intro/ ] *
#T0 #HT10 #HnT10
elim (IHT1 … HnT10) -IHT1 -HnT10 [| /2 width=2 by cpm_fwd_cpx/ ]
#T2 * /4 width=3 by cprs_step_sn, ex_intro, cpmre_intro/
qed-.
