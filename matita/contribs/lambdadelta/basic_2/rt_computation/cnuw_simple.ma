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

include "static_2/syntax/tweq_simple.ma".
include "basic_2/rt_computation/cpms_cpms.ma".
include "basic_2/rt_computation/cnuw.ma".

(* NORMAL TERMS FOR T-UNUNBOUND WHD RT-TRANSITION ***************************)

(* Advanced forward lemma with with simple terms ****************************)
(*
lemma cnuw_fwd_appl_simple (h) (G) (L):
      ∀V,T. ⦃G,L⦄ ⊢ ➡𝐍𝐖*[h] ⓐV.T → 𝐒⦃T⦄.
#h #G #L #V #T #HT
elim (simple_dec_ex T) [ // ] * #p #I #W #U #H destruct
*)
(* Advanced properties with simple terms ************************************)

lemma cnuw_appl_simple (h) (G) (L):
      ∀V,T. 𝐒⦃T⦄ → ⦃G,L⦄ ⊢ ➡𝐍𝐖*[h] T → ⦃G,L⦄ ⊢ ➡𝐍𝐖*[h] ⓐV.T.
#h #G #L #V1 #T1 #H1T1 #H2T1 #n #X #H
elim (cpms_inv_appl_sn … H) -H *
[ #V2 #T2 #_ #HT12 #H destruct -H1T1
  /3 width=2 by tweq_appl/
| #n1 #n2 #p #V2 #T2 #HT12 #_ #_ -n -n2
  lapply (H2T1 … HT12) -H2T1 -n1 #H
  lapply (tweq_simple_trans … H H1T1) -H -H1T1 #H
  elim (simple_inv_bind … H)
| #n1 #n2 #p #V2 #W2 #W #T2 #_ #_ #HT12 #_ #_ -n -n2 -V2 -W2
  lapply (H2T1 … HT12) -H2T1 -n1 #H
  lapply (tweq_simple_trans … H H1T1) -H -H1T1 #H
  elim (simple_inv_bind … H)
]
qed.
