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

include "basic_2/rt_transition/cnx.ma".
include "basic_2/rt_computation/csx.ma".

(* STRONGLY NORMALIZING TERMS FOR EXTENDED PARALLEL RT-TRANSITION ***********)

(* Properties with normal terms for extended parallel rt-transition *********)

(* Basic_1: was just: sn3_nf2 *)
lemma cnx_csx (G) (L):
      ∀T. ❪G,L❫ ⊢ ⬈𝐍 T → ❪G,L❫ ⊢ ⬈*𝐒 T.
/2 width=1 by NF_to_SN/ qed.

(* Advanced properties ******************************************************)

lemma csx_sort (G) (L):
      ∀s. ❪G,L❫ ⊢ ⬈*𝐒 ⋆s.
/3 width=4 by cnx_csx, cnx_sort/ qed.
