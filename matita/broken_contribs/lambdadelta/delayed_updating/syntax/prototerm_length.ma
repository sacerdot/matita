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

include "ground/lib/list_length_append.ma".
include "delayed_updating/syntax/prototerm.ma".

(* PROTOTERM ****************************************************************)

(* Inversions with list_length **********************************************)

lemma term_slice_eq_inv_length_bi (p1) (p2):
      p1 ϵ↑ p2 → ❘p1❘ = ❘p2❘ → p1 = p2.
#p1 #p2 * #q #H0 #Hp destruct
<list_length_append in Hp; #Hp
lapply (nplus_refl_dx … (sym_eq … Hp)) -Hp #Hq
<(list_length_inv_zero_sn … Hq) -q //
qed-.
