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

include "ground/lib/list_length.ma".
include "ground/lib/list_append.ma".
include "ground/arith/nat_plus.ma".

(* LENGTH FOR LISTS *********************************************************)

(* Constructions with list_append *******************************************)

lemma list_length_append (A) (l1) (l2):
      ❘l1❘+❘l2❘ = ❘l1⨁{A}l2❘.
#A #l1 elim l1 -l1 //
#a #l1 #IH #l2
<list_append_lcons_sn <list_length_lcons <list_length_lcons //
qed.
