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

include "basic_2A/static/da_lift.ma".
include "basic_2A/unfold/lstas_lift.ma".
include "basic_2A/computation/cprs_lift.ma".
include "basic_2A/computation/scpds.ma".

(* STRATIFIED DECOMPOSED PARALLEL COMPUTATION ON TERMS **********************)

(* Relocation properties ****************************************************)

lemma scpds_lift: ∀h,g,G,d. d_liftable (scpds h g d G).
#h #g #G #d2 #K #T1 #T2 * #T #d1 #Hd21 #Hd1 #HT1 #HT2 #L #s #l #m
elim (lift_total T l m)
/3 width=15 by cprs_lift, da_lift, lstas_lift, ex4_2_intro/
qed.

lemma scpds_inv_lift1: ∀h,g,G,d. d_deliftable_sn (scpds h g d G).
#h #g #G #d2 #L #U1 #U2 * #U #d1 #Hd21 #Hd1 #HU1 #HU2 #K #s #l #m #HLK #T1 #HTU1
lapply (da_inv_lift … Hd1 … HLK … HTU1) -Hd1 #Hd1
elim (lstas_inv_lift1 … HU1 … HLK … HTU1) -U1 #T #HTU #HT1
elim (cprs_inv_lift1 … HU2 … HLK … HTU) -U -L
/3 width=8 by ex4_2_intro, ex2_intro/
qed-.
