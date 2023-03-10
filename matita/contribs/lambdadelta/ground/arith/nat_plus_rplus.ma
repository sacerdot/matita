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

include "ground/arith/nat_rplus_succ.ma".
include "ground/arith/nat_plus.ma".

(* ADDITION FOR NON-NEGATIVE INTEGERS ***************************************)

(* Constructions with nrplus ************************************************)

lemma nrplus_inj_sn (p) (n):
      ninj (p + n) = ninj p + n.
#p #n @(nat_ind_succ … n) -n //
#n #IH <nplus_succ_dx <IH //
qed.

(* Constructions with nrplus and npsucc *************************************)

lemma nrplus_npsucc_sn (m) (n):
      npsucc (m + n) = npsucc m + n.
#m @(nat_ind_succ … m) -m //
#m #IH #n <npsucc_succ <nrplus_succ_sn //
qed.
