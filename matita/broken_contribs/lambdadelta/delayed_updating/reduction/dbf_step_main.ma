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

include "delayed_updating/reduction/prototerm_x_redex_main.ma".
include "delayed_updating/reduction/dbf_step.ma".

(* DELAYED BALANCED FOCUSED REDUCTION ***************************************)

(* Advanced inversions ******************************************************)

lemma dbfs_inv_pxr_sx (t1) (t2) (r) (p) (b) (q) (n):
      t1 ➡𝐝𝐛𝐟[r] t2 → r ϵ 𝐑❨p,b,q,n❩ →
      ⬕[𝐅❨p,b,q,n❩←𝐃❨t1,p,b,q,n❩]t1 ⇔ t2.
#t1 #t2 #r #p1 #b1 #q1 #n1
* #p2 #b2 #q2 #n2 * #_ #H2r #Ht12 #H1r
elim (pxr_inj … H1r H2r) -r #H1 #H2 #H3 #H4 destruct //
qed-.

(* Was: dbfs_preterm_inv_sx *)
lemma dbfs_inv_pcxr_sx (t1) (t2) (r) (p) (b) (q) (n):
      t1 ➡𝐝𝐛𝐟[r] t2 → r ϵ 𝐑❨t1,p,b,q,n❩ →
      ⬕[𝐅❨p,b,q,n❩←𝐃❨t1,p,b,q,n❩]t1 ⇔ t2.
#t1 #t2 #r #p1 #b1 #q1 #n1 #Ht12 * #_ #H1r
/2 width=3 by dbfs_inv_pxr_sx/
qed-.

(* Main inversions **********************************************************)

theorem dbfs_mono (t0) (t1) (t2) (r):
        t0 ➡𝐝𝐛𝐟[r] t1 → t0 ➡𝐝𝐛𝐟[r] t2 → t1 ⇔ t2.
#t0 #t1 #t2 #r #Ht01
* #p #b #q #n #Hr #Ht02
lapply (dbfs_inv_pcxr_sx … Ht01 Hr) -Ht01 -Hr #Ht01
@(subset_eq_canc_sx … Ht01 … Ht02)
qed-.
