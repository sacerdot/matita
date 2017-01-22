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

include "basic_2/substitution/llpx_sn_ldrop.ma".

(* LAZY SN POINTWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS ****)

(* Properties about transitive closure **************************************)

lemma llpx_sn_TC_pair_dx: ∀R. (∀I,L. reflexive … (R I L)) →
                          ∀I,L,V1,V2,T. LTC … (R I) L V1 V2 →
                          LTC … (llpx_sn R 0) T (L.ⓑ{I}V1) (L.ⓑ{I}V2).
#R #HR #I #L #V1 #V2 #T #H @(TC_star_ind … V2 H) -V2
/4 width=9 by llpx_sn_bind_repl_O, llpx_sn_refl, step, inj/
qed.
