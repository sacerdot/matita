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

include "terms/pointer.ma".

(* POINTER LIST *************************************************************)

(* Policy: pointer list metavariables: r, s *)
definition ptrl: Type[0] ≝ list ptr.

(* Note: a "whd" computation contracts just redexes in the whd *)
definition is_whd: predicate ptrl ≝ All … in_whd.

lemma is_whd_dx: ∀s. is_whd s → is_whd (dx:::s).
#s elim s -s //
#p #s #IHs * /3 width=1/ 
qed.

lemma is_whd_append: ∀r. is_whd r → ∀s. is_whd s → is_whd (r@s).
#r elim r -r //
#q #r #IHr * /3 width=1/
qed.

definition ho_compatible_rc: predicate (ptrl→relation term) ≝ λR.
                             ∀s,A1,A2. R s A1 A2 → R (rc:::s) (𝛌.A1) (𝛌.A2).

definition ho_compatible_sn: predicate (ptrl→relation term) ≝ λR.
                             ∀s,B1,B2,A. R s B1 B2 → R (sn:::s) (@B1.A) (@B2.A).

definition ho_compatible_dx: predicate (ptrl→relation term) ≝ λR.
                             ∀s,B,A1,A2. R s A1 A2 → R (dx:::s) (@B.A1) (@B.A2).

lemma lstar_compatible_rc: ∀R. compatible_rc R → ho_compatible_rc (lstar … R).
#R #HR #s #A1 #A2 #H @(lstar_ind_l ????????? H) -s -A1 // /3 width=3/
qed.

lemma lstar_compatible_sn: ∀R. compatible_sn R → ho_compatible_sn (lstar … R).
#R #HR #s #B1 #B2 #A #H @(lstar_ind_l ????????? H) -s -B1 // /3 width=3/
qed.

lemma lstar_compatible_dx: ∀R. compatible_dx R → ho_compatible_dx (lstar … R).
#R #HR #s #B #A1 #A2 #H @(lstar_ind_l ????????? H) -s -A1 // /3 width=3/
qed.
