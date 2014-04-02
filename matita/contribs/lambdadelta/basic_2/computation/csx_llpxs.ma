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

include "basic_2/computation/csx_llpx.ma".
include "basic_2/computation/llpxs.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERMS ********************)

(* Properties on lazy sn extended computation for local environments ********)

lemma csx_llpxs_conf: ∀h,g,G,L1,T. ⦃G, L1⦄ ⊢ ⬊*[h, g] T →
                      ∀L2.  ⦃G, L1⦄ ⊢ ➡*[h, g, T, 0] L2 → ⦃G, L2⦄ ⊢ ⬊*[h, g] T.
#h #g #G #L1 #T #HT #L2 #H @(llpxs_ind … H) -L2 /3 by llpxs_strap1, csx_llpx_conf/
qed-.
