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

include "basic_2/dynamic/cnv_fsb.ma".
include "basic_2/dynamic/nta.ma".

(* NATIVE TYPE ASSIGNMENT FOR TERMS *****************************************)

(* Forward lemmas with strongly rst-normalizing closures ********************)

(* Note: this is an extended stong normalization property *)
(* Note: this might use fsb_inv_cast (still to be proved) *)
(* Basic_1: uses: ty3_sn3 *)
(* Basic_2A1: uses: nta_fwd_csn *)
theorem nta_fwd_fsb (h) (a) (G) (L):
        ∀T,U. ⦃G,L⦄ ⊢ T :[h,a] U →
        ∧∧ ≥[h] 𝐒⦃G,L,T⦄ & ≥[h] 𝐒⦃G,L,U⦄.
#h #a #G #L #T #U #H
elim (cnv_inv_cast … H) #X #HU #HT #_ #_ -X
/3 width=2 by cnv_fwd_fsb, conj/
qed-.
