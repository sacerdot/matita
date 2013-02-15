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

include "basic_2/unwind/sstas_aaa.ma".
include "basic_2/computation/cprs_aaa.ma".
include "basic_2/computation/dxprs.ma".

(* DECOMPOSED EXTENDED PARALLEL COMPUTATION ON TERMS ************************)

(* Properties on atomic arity assignment for terms **************************)

lemma dxprs_aaa: ∀h,g,L,T,A. L ⊢ T ⁝ A → ∀U. ⦃h, L⦄ ⊢ T •*➡*[g] U → L ⊢ U ⁝ A.
#h #g #L #T #A #HT #U * /3 width=5/
qed.
