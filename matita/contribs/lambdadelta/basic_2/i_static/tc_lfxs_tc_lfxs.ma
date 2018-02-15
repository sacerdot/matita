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

include "basic_2/static/lfxs_lfxs.ma".
include "basic_2/i_static/tc_lfxs.ma".

(* ITERATED EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ***)

(* Advanced properties ******************************************************)

lemma tc_lfxs_sym: ∀R. lfxs_fle_compatible R →
                   (∀L1,L2,T1,T2. R L1 T1 T2 → R L2 T2 T1) →
                   ∀T. symmetric … (tc_lfxs R T).
#R #H1R #H2R #T #L1 #L2 #H elim H -L2
/4 width=3 by lfxs_sym, tc_lfxs_step_sn, inj/
qed-.

(* Main properties **********************************************************)

theorem tc_lfxs_trans: ∀R,T. Transitive … (tc_lfxs R T).
#R #T #L1 #L #HL1 #L2 #HL2 @(trans_TC … HL1 HL2) (**) (* auto fails *)
qed-.
