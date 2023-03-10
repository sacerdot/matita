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

include "basic_2A/substitution/drop_lreq.ma".
include "basic_2A/multiple/frees.ma".

(* CONTEXT-SENSITIVE FREE VARIABLES *****************************************)

(* Properties on equivalence for local environments *************************)

lemma lreq_frees_trans: āL2,U,l,i. L2 ā¢ i Ļµ š*[l]ā¦Uā¦ ā
                        āL1. L1 ā©¬[l, ā] L2 ā L1 ā¢ i Ļµ š*[l]ā¦Uā¦.
#L2 #U #l #i #H elim H -L2 -U -l -i /3 width=2 by frees_eq/
#I2 #L2 #K2 #U #W2 #l #i #j #Hlj #Hji #HnU #HLK2 #_ #IHW2 #L1 #HL12
elim (lreq_drop_trans_be ā¦ HL12 ā¦ HLK2) -L2 // >yminus_Y_inj #K1 #HK12 #HLK1
lapply (lreq_inv_O_Y ā¦ HK12) -HK12 #H destruct /3 width=9 by frees_be/
qed-.

lemma frees_lreq_conf: āL1,U,l,i. L1 ā¢ i Ļµ š*[l]ā¦Uā¦ ā
                       āL2. L1 ā©¬[l, ā] L2 ā L2 ā¢ i Ļµ š*[l]ā¦Uā¦.
/3 width=3 by lreq_sym, lreq_frees_trans/ qed-.
