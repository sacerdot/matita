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

(* STRONGLY NORMALIZING TERMS FOR UNBOUND PARALLEL RT-TRANSITION ************)

include "basic_2/rt_transition/cnx.ma".
include "basic_2/rt_computation/csx.ma".

(* Properties with normal terms for unbound parallel rt-transition **********)

(* Basic_1: was just: sn3_nf2 *)
lemma cnx_csx (h) (G) (L):
      ∀T. ❪G,L❫ ⊢ ⬈𝐍[h] T → ❪G,L❫ ⊢ ⬈*𝐒[h] T.
/2 width=1 by NF_to_SN/ qed.

(* Advanced properties ******************************************************)

lemma csx_sort (h) (G) (L):
      ∀s. ❪G,L❫ ⊢ ⬈*𝐒[h] ⋆s.
/3 width=4 by cnx_csx, cnx_sort/ qed.
