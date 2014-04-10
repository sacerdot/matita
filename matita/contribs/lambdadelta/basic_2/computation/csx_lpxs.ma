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

include "basic_2/computation/csx_lpx.ma".
include "basic_2/computation/lpxs.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERMS ********************)

(* Properties on sn extended parallel computation for local environments ****)

lemma csx_lpxs_conf: ∀h,g,G,L1,L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 →
                     ∀T. ⦃G, L1⦄ ⊢ ⬊*[h, g] T → ⦃G, L2⦄ ⊢ ⬊*[h, g] T.
#h #g #G #L1 #L2 #H @(lpxs_ind … H) -L2 /3 by lpxs_strap1, csx_lpx_conf/
qed-.
