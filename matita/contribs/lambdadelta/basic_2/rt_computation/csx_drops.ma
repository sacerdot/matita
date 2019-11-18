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

include "static_2/relocation/lifts_teqx.ma".
include "basic_2/rt_transition/cpx_drops.ma".
include "basic_2/rt_computation/csx.ma".

(* STRONGLY NORMALIZING TERMS FOR UNBOUND PARALLEL RT-TRANSITION ************)

(* Properties with generic relocation ***************************************)

(* Basic_1: was just: sn3_lift *)
(* Basic_2A1: was just: csx_lift *)
lemma csx_lifts: ∀h,G. d_liftable1 … (csx h G).
#h #G #K #T #H @(csx_ind … H) -T
#T1 #_ #IH #b #f #L #HLK #U1 #HTU1
@csx_intro #U2 #HU12 #HnU12
elim (cpx_inv_lifts_sn … HU12 … HLK … HTU1) -HU12
/4 width=7 by teqx_lifts_bi/
qed-.

(* Inversion lemmas with generic slicing ************************************)

(* Basic_1: was just: sn3_gen_lift *)
(* Basic_2A1: was just: csx_inv_lift *)
lemma csx_inv_lifts: ∀h,G. d_deliftable1 … (csx h G).
#h #G #L #U #H @(csx_ind … H) -U
#U1 #_ #IH #b #f #K #HLK #T1 #HTU1
@csx_intro #T2 #HT12 #HnT12
elim (cpx_lifts_sn … HT12 … HLK … HTU1) -HT12
/4 width=7 by teqx_inv_lifts_bi/
qed-.
