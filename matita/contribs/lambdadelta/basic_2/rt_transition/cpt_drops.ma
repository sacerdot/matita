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

include "basic_2/rt_transition/cpg_drops.ma".
include "basic_2/rt_transition/cpt.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL T-TRANSITION FOR TERMS ****************)

(* Properties with generic slicing for local environments *******************)

lemma cpt_lifts_sn (h) (n) (G):
      d_liftable2_sn … lifts (λL. cpt h G L n).
#h #n #G #K #T1 #T2 * #c #Hc #HT12 #b #f #L #HLK #U1 #HTU1
elim (cpg_lifts_sn … HT12 … HLK … HTU1) -K -T1
/3 width=5 by ex2_intro/
qed-.

lemma cpt_lifts_bi (h) (n) (G):
      d_liftable2_bi … lifts (λL. cpt h G L n).
#h #n #G #K #T1 #T2 * /3 width=11 by cpg_lifts_bi, ex2_intro/
qed-.

(* Inversion lemmas with generic slicing for local environments *************)

lemma cpt_inv_lifts_sn (h) (n) (G):
      d_deliftable2_sn … lifts (λL. cpt h G L n).
#h #n #G #L #U1 #U2 * #c #Hc #HU12 #b #f #K #HLK #T1 #HTU1
elim (cpg_inv_lifts_sn … HU12 … HLK … HTU1) -L -U1
/3 width=5 by ex2_intro/
qed-.

lemma cpt_inv_lifts_bi (h) (n) (G):
      d_deliftable2_bi … lifts (λL. cpt h G L n).
#h #n #G #L #U1 #U2 * /3 width=11 by cpg_inv_lifts_bi, ex2_intro/
qed-.
