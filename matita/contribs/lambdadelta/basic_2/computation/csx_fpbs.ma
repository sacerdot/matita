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

include "basic_2/computation/lpxs.ma".
include "basic_2/computation/csx_lpx.ma".

(* CONTEXT-SENSITIVE EXTENDED STRONGLY NORMALIZING TERMS ********************)

(* Advanced properties ******************************************************)

lemma csx_lpxs_conf: ∀h,g,G,L1. ∀T:term. ⦃G, L1⦄ ⊢ ⬊*[h, g] T →
                     ∀L2. ⦃G, L1⦄ ⊢ ➡*[h, g] L2 → ⦃G, L2⦄ ⊢ ⬊*[h, g] T.
#h #g #G #L1 #T #HT #L2 #H @(lpxs_ind … H) -L2 /2 width=3 by csx_lpx_conf/
qed-.
