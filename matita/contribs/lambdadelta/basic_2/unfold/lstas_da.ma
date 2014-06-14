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

include "basic_2/unfold/lstas.ma".
include "basic_2/static/da_sta.ma".

(* NAT-ITERATED STATIC TYPE ASSIGNMENT FOR TERMS ****************************)

(* Properties on degree assignment for terms ********************************)

lemma lstas_da_conf: ∀h,g,G,L,T,U,l1. ⦃G, L⦄ ⊢ T •*[h, l1] U →
                     ∀l2. ⦃G, L⦄ ⊢ T ▪[h, g] l2 → ⦃G, L⦄ ⊢ U ▪[h, g] l2-l1.
#h #g #G #L #T #U #l1 #H @(lstas_ind_dx … H) -U -l1 //
#l1 #U #U0 #_ #HU0 #IHTU #l2 #HT
<minus_plus /3 width=3 by da_sta_conf/
qed-.
