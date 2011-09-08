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

include "Basic-2/reduction/tpr_tpr.ma".
include "Basic-2/reduction/cpr.ma".

(* CONTEXT-SENSITIVE PARALLEL REDUCTION ON TERMS ****************************)

(* Main properties **********************************************************)
(*
(* Basic-1: was: pr2_confluence *)
theorem cpr_conf: ∀L,U0,T1,T2. L ⊢ U0 ⇒ T1 → L ⊢ U0 ⇒ T2 →
                  ∃∃T. L ⊢ T1 ⇒ T & L ⊢ T2 ⇒ T.
#L #U0 #T1 #T2 * #U1 #HU01 #HUT1 * #U2 #HU02 #HUT2
elim (tpr_conf … HU01 HU02) -U0 #U #HU1 #HU2 
qed.
*)
