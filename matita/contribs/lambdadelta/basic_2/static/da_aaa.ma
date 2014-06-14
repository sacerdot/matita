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

include "basic_2/static/da_sta.ma".
include "basic_2/static/sta_aaa.ma".

(* DEGREE ASSIGNMENT FOR TERMS **********************************************)

(* Properties on atomic arity assignment for terms **************************)

lemma aaa_da: ∀h,g,G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ∃l. ⦃G, L⦄ ⊢ T ▪[h, g] l.
#h #g #G #L #T #A #H elim (aaa_sta h … H) -A /2 width=2 by sta_da/
qed-.
