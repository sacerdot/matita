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

include "basic_2/rt_computation/cnuw.ma".
include "basic_2/rt_computation/cprs_tweq.ma".
include "basic_2/rt_computation/lprs_cpms.ma".

(* NORMAL TERMS FOR T-UNUNBOUND WHD RT-TRANSITION ***************************)

(* Advanced inversion lemmas ************************************************)

lemma cnuw_inv_abbr_pos (h) (G) (L):
      ∀V,T. ⦃G,L⦄ ⊢ ➡𝐍𝐖*[h] +ⓓV.T → ⊥.
#h #G #L #V #T1 #H
elim (cprs_abbr_pos_twneq h G L V T1) #T2 #HT12 #HnT12
/3 width=2 by/
qed-.

(* Advanced properties ******************************************************)

lemma cnuw_abbr_neg (h) (G) (L): ∀V,T. ⦃G,L⦄ ⊢ ➡𝐍𝐖*[h] -ⓓV.T.
#h #G #L #V1 #T1 #n #X #H
elim (cpms_inv_abbr_sn_dx … H) -H *
[ #V2 #T2 #_ #_ #H destruct /1 width=1 by tweq_abbr_neg/
| #X1 #_ #_ #H destruct
]
qed.

lemma cnuw_abst (h) (p) (G) (L): ∀W,T. ⦃G,L⦄ ⊢ ➡𝐍𝐖*[h] ⓛ{p}W.T.
#h #p #G #L #W1 #T1 #n #X #H
elim (cpms_inv_abst_sn … H) -H #W2 #T2 #_ #_ #H destruct
/1 width=1 by tweq_abst/
qed.

lemma cnuw_cpms_trans (h) (n) (G) (L):
      ∀T1. ⦃G,L⦄ ⊢ ➡𝐍𝐖*[h] T1 →
      ∀T2. ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2 → ⦃G,L⦄ ⊢ ➡𝐍𝐖*[h] T2.
#h #n1 #G #L #T1 #HT1 #T2 #HT12 #n2 #T3 #HT23
/4 width=5 by cpms_trans, tweq_canc_sn/
qed-.
