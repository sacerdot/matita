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

include "basic_2/rt_computation/fpbg.ma".
include "basic_2/rt_computation/cpms_fpbs.ma".
include "basic_2/dynamic/cnv.ma".

(* CONTEXT-SENSITIVE NATIVE VALIDITY FOR TERMS ******************************)

(* Inductive premises for the preservation results **************************)

definition IH_cnv_cpm_trans_lpr (a) (h): relation3 genv lenv term ≝
                                λG,L1,T1. ⦃G, L1⦄ ⊢ T1 ![a,h] →
                                ∀n,T2. ⦃G, L1⦄ ⊢ T1 ➡[n,h] T2 →
                                ∀L2. ⦃G, L1⦄ ⊢ ➡[h] L2 → ⦃G, L2⦄ ⊢ T2 ![a,h].

definition IH_cnv_cpms_trans_lpr (a) (h): relation3 genv lenv term ≝
                                 λG,L1,T1. ⦃G, L1⦄ ⊢ T1 ![a,h] →
                                 ∀n,T2. ⦃G, L1⦄ ⊢ T1 ➡*[n,h] T2 →
                                 ∀L2. ⦃G, L1⦄ ⊢ ➡[h] L2 → ⦃G, L2⦄ ⊢ T2 ![a,h].

definition IH_cnv_cpm_conf_lpr (a) (h): relation3 genv lenv term ≝
                               λG,L0,T0. ⦃G, L0⦄ ⊢ T0 ![a,h] →
                               ∀n1,T1. ⦃G, L0⦄ ⊢ T0 ➡[n1,h] T1 → ∀n2,T2. ⦃G, L0⦄ ⊢ T0 ➡[n2,h] T2 →
                               ∀L1. ⦃G, L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h] L2 →
                               ∃∃T. ⦃G, L1⦄ ⊢ T1 ➡*[n2-n1,h] T & ⦃G, L2⦄ ⊢ T2 ➡*[n1-n2,h] T.

definition IH_cnv_cpms_strip_lpr (a) (h): relation3 genv lenv term ≝
                                 λG,L0,T0. ⦃G, L0⦄ ⊢ T0 ![a,h] →
                                 ∀n1,T1. ⦃G, L0⦄ ⊢ T0 ➡*[n1,h] T1 → ∀n2,T2. ⦃G, L0⦄ ⊢ T0 ➡[n2,h] T2 →
                                 ∀L1. ⦃G, L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h] L2 →
                                 ∃∃T. ⦃G, L1⦄ ⊢ T1 ➡*[n2-n1,h] T & ⦃G, L2⦄ ⊢ T2 ➡*[n1-n2,h] T.

definition IH_cnv_cpms_conf_lpr (a) (h): relation3 genv lenv term ≝
                                λG,L0,T0. ⦃G, L0⦄ ⊢ T0 ![a,h] →
                                ∀n1,T1. ⦃G, L0⦄ ⊢ T0 ➡*[n1,h] T1 → ∀n2,T2. ⦃G, L0⦄ ⊢ T0 ➡*[n2,h] T2 →
                                ∀L1. ⦃G, L0⦄ ⊢ ➡[h] L1 → ∀L2. ⦃G, L0⦄ ⊢ ➡[h] L2 →
                                ∃∃T. ⦃G, L1⦄ ⊢ T1 ➡*[n2-n1,h] T & ⦃G, L2⦄ ⊢ T2 ➡*[n1-n2,h] T.

(* Auxiliary properties for preservation ************************************)

fact cnv_cpms_trans_lpr_aux (a) (h) (o):
                            ∀G0,L0,T0.
                            (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, o] ⦃G1, L1, T1⦄ → IH_cnv_cpm_trans_lpr a h G1 L1 T1) →
                            ∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, o] ⦃G1, L1, T1⦄ → IH_cnv_cpms_trans_lpr a h G1 L1 T1.
#a #h #o #G0 #L0 #T0 #IH #G1 #L1 #T1 #H01 #HT1 #n #T2 #H
@(cpms_ind_dx … H) -n -T2
/4 width=7 by cpms_fwd_fpbs, fpbg_fpbs_trans/
qed-.
(*
fact cnv_cpms_strip_lpr_aux (a) (h) (o):
                            ∀G0,L0,T0.
                            (∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, o] ⦃G1, L1, T1⦄ → IH_cnv_cpm_conf_lpr a h G1 L1 T1) →
                            ∀G1,L1,T1. ⦃G0, L0, T0⦄ >[h, o] ⦃G1, L1, T1⦄ → IH_cnv_cpms_strip_lpr a h G1 L1 T1.
#a #h #o #G0 #L0 #T0 #IH0 #G #L #T #H0 #HT #n1 #T1 #H
generalize in match HT; generalize in match H0; -H0 -HT
@(cpms_ind_sn … H) -n1 -T [ /2 width=8 by/ ]
#n1 #n2 #T #X #HTX #HXT1 #IH #H0 #HT #n2 #T2 #HT2 #L1 #HL1 #L2 #HL2
elim (IH0 … HTX … HT2 … HL1 … HL2) // -L -T #T0 #HXT0 #HT20  
  
  @(IH … 0 T … HT2 … HL1 … HL2) // -L -IH
  #T0 #HT20 #HT0  
*)
