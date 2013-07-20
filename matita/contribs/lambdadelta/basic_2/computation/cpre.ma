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

include "basic_2/computation/cprs.ma".
include "basic_2/computation/csn.ma".

(* CONTEXT-SENSITIVE PARALLEL EVALUATION ON TERMS **************************)

definition cpre: lenv → relation term ≝
                 λL,T1,T2. L ⊢ T1 ➡* T2 ∧ L ⊢ 𝐍⦃T2⦄.

interpretation "context-sensitive parallel evaluation (term)"
   'PEval L T1 T2 = (cpre L T1 T2).

(* Basic_properties *********************************************************)

(* Basic_1: was just: nf2_sn3 *)
axiom csn_cpre: ∀h,g,L,T1. ⦃h, L⦄ ⊢ ⬊*[g] T1 → ∃T2. L ⊢ T1 ➡* 𝐍⦃T2⦄.
(*
#h #g #L #T1 #H @(csn_ind … H) -T1
#T1 #_ #IHT1
elim (cnr_dec L T1) /3 width=3/
* #T #H1T1 #H2T1
elim (IHT1 … H2T1) -IHT1 -H2T1 [2: /2 width=2/ ] #T2 * /4 width=3/
qed.
*)
