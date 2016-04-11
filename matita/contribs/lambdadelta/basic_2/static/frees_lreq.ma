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

include "basic_2/relocation/lreq.ma".
include "basic_2/static/frees.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Properties with ranged equivalence for local environments ****************)

lemma frees_lreq_conf: ∀L1,T,f. L1 ⊢ 𝐅*⦃T⦄ ≡ f → ∀L2. L1 ≡[f] L2 → L2 ⊢ 𝐅*⦃T⦄ ≡ f.
#L1 #T #f #H elim H -L1 -T -f
[ #I #f #Hf #X #H lapply (lreq_inv_atom1 … H) -H
  #H destruct /2 width=1 by frees_atom/
| #I #L1 #V1 #s #f #_ #IH #X #H elim (lreq_inv_push1 … H) -H
  /3 width=1 by frees_sort/
| #I #L1 #V1 #f #_ #IH #X #H elim (lreq_inv_next1 … H) -H
  /3 width=1 by frees_zero/
| #I #L1 #V1 #i #f #_ #IH #X #H elim (lreq_inv_push1 … H) -H
  /3 width=1 by frees_lref/
| #I #L1 #V1 #l #f #_ #IH #X #H elim (lreq_inv_push1 … H) -H
  /3 width=1 by frees_gref/
| /6 width=5 by frees_bind, lreq_inv_tl, sle_lreq_trans, sor_inv_sle_dx, sor_inv_sle_sn/
| /5 width=5 by frees_flat, sle_lreq_trans, sor_inv_sle_dx, sor_inv_sle_sn/
]
qed-.

lemma lreq_frees_trans: ∀L1,T,f. L1 ⊢ 𝐅*⦃T⦄ ≡ f → ∀L2. L2 ≡[f] L1 → L2 ⊢ 𝐅*⦃T⦄ ≡ f.
/3 width=3 by frees_lreq_conf, lreq_sym/ qed-.
