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

include "ground/arith/nat_plus.ma".
include "ground/lib/list_append.ma".
include "ground/lib/list_singleton.ma".

(* SINGLETON FOR LISTS ******************************************************)

(* Constructions with list_append *******************************************)

lemma list_singleton_append (A) (a) (m) (n):
      a^(m+n) = a^n ⨁{A} a^m.
#A #a #m #n @(nat_ind_succ … n) -n [ // | #n #IH ]
<nplus_succ_dx <list_singleton_succ_lcons >IH -IH //
qed.
