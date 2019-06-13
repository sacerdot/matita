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

(* STRONGLY NORMALIZING TERM VECTORS FOR UNBOUND PARALLEL RT-TRANSITION *****)

include "basic_2/rt_computation/cpxs_theq_vector.ma".
include "basic_2/rt_computation/csx_simple_theq.ma".
include "basic_2/rt_computation/csx_cnx.ma".
include "basic_2/rt_computation/csx_cpxs.ma".
include "basic_2/rt_computation/csx_vector.ma".

(* Properties with normal terms for unbound parallel rt-transition **********)

(* Basic_1: was just: sn3_appls_lref *)
lemma csx_applv_cnx: ∀h,G,L,T. 𝐒⦃T⦄ → ⦃G,L⦄ ⊢ ⬈[h] 𝐍⦃T⦄ →
                     ∀Vs. ⦃G,L⦄ ⊢ ⬈*[h] 𝐒⦃Vs⦄ → ⦃G,L⦄ ⊢ ⬈*[h] 𝐒⦃ⒶVs.T⦄.
#h #G #L #T #H1T #H2T #Vs elim Vs -Vs
[ #_ normalize in ⊢ (????%); /2 width=1 by cnx_csx/
| #V #Vs #IHV #H
  elim (csxv_inv_cons … H) -H #HV #HVs
  @csx_appl_simple_theq /2 width=1 by applv_simple/ -IHV -HV -HVs
  #X #H #H0
  lapply (cpxs_fwd_cnx_vector … H) -H // -H1T -H2T #H
  elim (H0) -H0 //
]
qed.

(* Advanced properties ******************************************************)

lemma csx_applv_sort: ∀h,G,L,s,Vs. ⦃G,L⦄ ⊢ ⬈*[h] 𝐒⦃Vs⦄ → ⦃G,L⦄ ⊢ ⬈*[h] 𝐒⦃ⒶVs.⋆s⦄.
/3 width=6 by csx_applv_cnx, cnx_sort, simple_atom/ qed.
