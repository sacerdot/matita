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

(* Constructions with nrplus and npsucc *************************************)

lemma nrplus_npsucc_sx (m:ℕ) (n):
      ↑(m + n) = (↑m) + n.
#m @(nat_ind_succ … m) -m //
qed.

(* Constructions with nrplus ************************************************)

lemma nplus_pos_sx (p) (n):
      (⁤(p + n)) = (⁤p) + n.
#p #n @(nat_ind_succ … n) -n //
qed.

lemma nrplus_plus_assoc (p:ℕ⁺) (n) (m):
      p+m+n = p+(m+n).
#p #n @(nat_ind_succ … n) -n //
#n #IH #m
<nrplus_succ_dx <nplus_succ_dx >IH -IH //
qed.
