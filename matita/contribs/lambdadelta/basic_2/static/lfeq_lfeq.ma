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

include "basic_2/relocation/lreq_lreq.ma".
include "basic_2/static/frees_frees.ma".
include "basic_2/static/lfxs_lfxs.ma".
include "basic_2/static/lfeq_lreq.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS ON REFERRED ENTRIES *******************)

(* Main properties **********************************************************)

theorem lfeq_bind: ∀p,I,L1,L2,V1,V2,T.
                   L1 ≡[V1] L2 → L1.ⓑ{I}V1 ≡[T] L2.ⓑ{I}V2 →
                   L1 ≡[ⓑ{p,I}V1.T] L2.
/2 width=2 by lfxs_bind/ qed.

theorem lfeq_flat: ∀I,L1,L2,V,T. L1 ≡[V] L2 → L1 ≡[T] L2 →
                   L1 ≡[ⓕ{I}V.T] L2.
/2 width=1 by lfxs_flat/ qed.

(* Note: /2 width=3 by lfeq_lfxs_trans/ *)
theorem lfeq_trans: ∀T. Transitive … (lfeq T).
#T #L1 #L * #f1 #Hf1 #HL1 #L2 * #f2 #Hf2 #HL2
lapply (frees_lreq_conf … Hf1 … HL1) #H0
lapply (frees_mono … Hf2 … H0) -Hf2 -H0
/4 width=7 by lreq_trans, lexs_eq_repl_back, ex2_intro/
qed-.

theorem lfeq_canc_sn: ∀T. left_cancellable … (lfeq T).
/3 width=3 by lfeq_trans, lfeq_sym/ qed-.

theorem lfeq_canc_dx: ∀T. right_cancellable … (lfeq T).
/3 width=3 by lfeq_trans, lfeq_sym/ qed-.

(* Advanced properies on negated lazy equivalence *****************************)

(* Note: for use in auto, works with /4 width=8/ so lfeq_canc_sn is preferred *) 
lemma lfeq_nlfeq_trans: ∀T,L1,L. L1 ≡[T] L →
                        ∀L2. (L ≡[T] L2 → ⊥) → (L1 ≡[T] L2 → ⊥).
/3 width=3 by lfeq_canc_sn/ qed-.

lemma nlfeq_lfeq_div: ∀T,L2,L. L2 ≡[T] L →
                      ∀L1. (L1 ≡[T] L → ⊥) → (L1 ≡[T] L2 → ⊥).
/3 width=3 by lfeq_trans/ qed-.
