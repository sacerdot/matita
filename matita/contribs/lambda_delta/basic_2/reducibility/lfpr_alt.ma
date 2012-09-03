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

include "basic_2/grammar/lenv_px_bi.ma".
include "basic_2/reducibility/fpr.ma".

(* FOCALIZED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS **********************)

(* alternative definition *)
definition lfpra: relation lenv ≝ lpx_bi fpr.

interpretation
  "focalized parallel reduction (environment) alternative"
  'FocalizedPRedAlt L1 L2 = (lfpra L1 L2).

(* Basic properties *********************************************************)

lemma lfpra_refl: reflexive … lfpra.
/2 width=1/ qed.

(* Basic inversion lemmas ***************************************************)

lemma lfpra_inv_atom1: ∀L2. ⦃⋆⦄ ➡➡ ⦃L2⦄ → L2 = ⋆.
/2 width=2 by lpx_bi_inv_atom1/ qed-.

lemma lfpra_inv_pair1: ∀K1,I,V1,L2. ⦃K1. ⓑ{I} V1⦄ ➡➡ ⦃L2⦄ →
                       ∃∃K2,V2. ⦃K1⦄ ➡➡ ⦃K2⦄ & ⦃K1, V1⦄ ➡ ⦃K2, V2⦄ &
                                L2 = K2. ⓑ{I} V2.
/2 width=1 by lpx_bi_inv_pair1/ qed-.

lemma lfpra_inv_atom2: ∀L1. ⦃L1⦄ ➡➡ ⦃⋆⦄ → L1 = ⋆.
/2 width=2 by lpx_bi_inv_atom2/ qed-.

lemma lfpra_inv_pair2: ∀L1,K2,I,V2. ⦃L1⦄ ➡➡ ⦃K2. ⓑ{I} V2⦄ →
                       ∃∃K1,V1. ⦃K1⦄ ➡➡ ⦃K2⦄ & ⦃K1, V1⦄ ➡ ⦃K2, V2⦄ &
                                L1 = K1. ⓑ{I} V1.
/2 width=1 by lpx_bi_inv_pair2/ qed-.

(* Basic forward lemmas *****************************************************)

lemma lfpra_fwd_length: ∀L1,L2. ⦃L1⦄ ➡➡ ⦃L2⦄ → |L1| = |L2|.
/2 width=2 by lpx_bi_fwd_length/ qed-.

(****************************************************************************)

lemma fpr_lfpra: ∀L1,T1,L2,T2. ⦃L1, T1⦄ ➡ ⦃L2, T2⦄ → ⦃L1⦄ ➡➡ ⦃L2⦄.
#L1 #T1 @(cw_wf_ind … L1 T1) -L1 -T1 *
[ #T1 #_ #L2 #T2 #H
  elim (fpr_inv_atom1 … H) -H #_ #H destruct //
| #L1 #I #V1 #T1 #IH #Y #X #H
  elim (fpr_inv_pair1 … H) -H #L2 #V2 #HL12 #H destruct
  @lpx_bi_pair 
  [ @(IH … HL12) 
  | @IH 
  
  /3 width=4/

lemma fpr_lfpra: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ➡ ⦃L2, T2⦄ → ⦃L1⦄ ➡➡ ⦃L2⦄.
#L1 elim L1 -L1
[ #L2 #T1 #T2 #H
  elim (fpr_inv_atom1 … H) -H #_ #H destruct //
| #L1 #I #V1 #IH #L2 #T1 #T2 #H
  elim (fpr_inv_pair1 … H) -H #L #V #HL1 #H destruct
  @lpx_bi_pair /2 width=3/ 
  
  /4 width=3/

(*
include "basic_2/reducibility/lcpr.ma".

lemma lcpr_pair2: ∀L1,L2. L1 ⊢ ➡ L2 → ∀V1,V2. ⦃L1, V1⦄ ➡ ⦃L2, V2⦄ →
                  ∀I. L1. ⓑ{I} V1 ⊢ ➡ L2. ⓑ{I} V2.
#L1 #L2 * #L #HL1 #HL2 #V1 #V2 *
#H1 #H2 #I
@(ex2_1_intro … (L.ⓑ{I}V1)) /2 width=1/
@tpss_

(*
<(ltpss_fwd_length … HL2) /4 width=5/
qed.
*)
*)