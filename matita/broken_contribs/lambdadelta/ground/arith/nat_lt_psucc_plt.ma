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

include "ground/arith/pnat_lt.ma".
include "ground/arith/nat_le_ple.ma".
include "ground/arith/nat_lt.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS ***********************************)

(* Inversions with psucc and plt ********************************************)

lemma plt_npsucc_bi (n1) (n2):
      n1 < n2 → npsucc n1 < npsucc n2.
/2 width=1 by ple_npsucc_bi/
qed-.
