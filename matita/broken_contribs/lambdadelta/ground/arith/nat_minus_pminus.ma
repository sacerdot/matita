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

include "ground/arith/pnat_minus.ma".
include "ground/arith/pnat_lt.ma".
include "ground/arith/nat_minus.ma".

(* SUBTRACTION FOR NON-NEGATIVE INTEGERS ************************************)

(* Constructions with pminus ************************************************)

lemma nminus_inj_bi (p1) (p2):
      p2 < p1 →
      npos (p1 - p2) = npos p1 - npos p2.
#p2 #p1 #H0 @(plt_ind_alt … H0) -p1 -p2 //
qed-.
