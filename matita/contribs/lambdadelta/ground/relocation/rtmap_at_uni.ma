(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.tcs.unibo.it                            *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "ground/arith/nat_rplus_succ.ma".
include "ground/relocation/rtmap_uni.ma".
include "ground/relocation/rtmap_at.ma".

(* RELOCATION MAP ***********************************************************)

(* Properties with uniform relocations **************************************)

lemma at_uni: ∀n,i. @❪i,𝐔❨n❩❫ ≘ i+n.
#n @(nat_ind_succ … n) -n /2 width=5 by at_next/
qed.

(* Inversion lemmas with uniform relocations ********************************)

lemma at_inv_uni: ∀n,i,j. @❪i,𝐔❨n❩❫ ≘ j → j = i+n.
/2 width=4 by at_mono/ qed-.
