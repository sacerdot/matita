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

(* Advanced inversion lemmas ************************************************)

lemma lstas_inv_refl_pos: ∀h,G,L,T,l. ⦃G, L⦄ ⊢ T •*[h, l+1] T → ⊥.
#h #G #L #T #l #H elim (lstas_inv_step_sn … H)
#U #HTU #_ elim (sta_da_ge … (l+1) HTU) -U
#g #l0 #HT #Hl0 lapply (lstas_da_conf … H … HT) -H
#H0T lapply (da_mono … HT … H0T) -h -G -L -T
#H elim (discr_x_minus_xy … H) -H
[ #H destruct /2 width=3 by le_plus_xSy_O_false/
| -Hl0 <plus_n_Sm #H destruct 
]
qed-.
