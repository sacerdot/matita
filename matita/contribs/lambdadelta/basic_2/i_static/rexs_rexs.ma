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

include "basic_2/static/rex_fsle.ma".
include "basic_2/i_static/rexs.ma".

(* ITERATED EXTENSION ON REFERRED ENTRIES OF A CONTEXT-SENSITIVE REALTION ***)

(* Advanced properties ******************************************************)

lemma rexs_sym: ∀R. rex_fsge_compatible R →
                (∀L1,L2,T1,T2. R L1 T1 T2 → R L2 T2 T1) →
                ∀T. symmetric … (rexs R T).
#R #H1R #H2R #T #L1 #L2 #H elim H -L2
/4 width=3 by rex_sym, rexs_step_sn, inj/
qed-.

(* Main properties **********************************************************)

theorem rexs_trans: ∀R,T. Transitive … (rexs R T).
#R #T #L1 #L #HL1 #L2 #HL2 @(trans_TC … HL1 HL2) (**) (* auto fails *)
qed-.
