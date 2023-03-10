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

include "basic_2A/multiple/llpx_sn_drop.ma".

(* LAZY SN POINTWISE EXTENSION OF A CONTEXT-SENSITIVE REALTION FOR TERMS ****)

(* Properties about transitive closure **************************************)

lemma llpx_sn_TC_pair_dx: ∀R. (∀L. reflexive … (R L)) →
                          ∀I,L,V1,V2,T. CTC … R L V1 V2 →
                          CTC … (llpx_sn R 0) T (L.ⓑ{I}V1) (L.ⓑ{I}V2).
#R #HR #I #L #V1 #V2 #T #H @(TC_star_ind … V2 H) -V2
/4 width=9 by llpx_sn_bind_repl_O, llpx_sn_refl, step, inj/
qed.
