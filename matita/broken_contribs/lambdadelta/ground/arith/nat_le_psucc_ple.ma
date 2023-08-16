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

include "ground/arith/nat_le.ma".
include "ground/arith/nat_psucc.ma".
include "ground/arith/pnat_le.ma".

(* ORDER FOR NON-NEGATIVE INTEGERS ******************************************)

(* Inversions with psucc and ple ********************************************)

lemma ple_npsucc_bi (n1) (n2):
      n1 ≤ n2 → npsucc n1 ≤ npsucc n2.
#n1 #n2 #Hn elim Hn -n2 //
#n2 #IH #Hn
/2 width=1 by ple_succ_dx/
qed-.
