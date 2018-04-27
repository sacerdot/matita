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
lemma cnx_csx: ∀h,o,G,L,T. ⦃G, L⦄ ⊢ ⬈[h, o] 𝐍⦃T⦄ → ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃T⦄.
/2 width=1 by NF_to_SN/ qed.

(* Advanced properties ******************************************************)

lemma csx_sort: ∀h,o,G,L,s. ⦃G, L⦄ ⊢ ⬈*[h, o] 𝐒⦃⋆s⦄.
#h #o #G #L #s elim (deg_total h o s)
#d generalize in match s; -s elim d -d
[ /3 width=3 by cnx_csx, cnx_sort/
| #d #IH #s #Hsd lapply (deg_next_SO … Hsd) -Hsd
  #Hsd @csx_intro #X #H #HX
  elim (cpx_inv_sort1 … H) -H #H destruct /2 width=1 by/
  elim HX -HX //
]
qed.
