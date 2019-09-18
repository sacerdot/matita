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

include "basic_2/dynamic/cnv_eval.ma".
include "basic_2/dynamic/nta_preserve.ma".

(* NATIVE TYPE ASSIGNMENT FOR TERMS *****************************************)

(* Properties with evaluations for rt-transition on terms *******************)

lemma nta_typecheck_dec (h) (a) (G) (L): ac_props a →
      ∀T,U. Decidable … (⦃G,L⦄ ⊢ T :[h,a] U).
/2 width=1 by cnv_dec/ qed-.

(* Basic_1: uses: ty3_inference *)
lemma nta_inference_dec (h) (a) (G) (L) (T): ac_props a →
      Decidable (∃U. ⦃G,L⦄ ⊢ T :[h,a] U).
#h #a #G #L #T #Ha
elim (cnv_dec h … G L T Ha) -Ha #HT
[ /3 width=1 by cnv_nta_sn, or_introl/
| @or_intror * #U #HTU
  /3 width=2 by nta_fwd_cnv_sn/
]
qed-.
