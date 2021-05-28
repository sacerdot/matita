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

include "ground/relocation/gr_tls.ma".
include "ground/relocation/gr_isi_tl.ma".

(* IDENTITY CONDITION FOR GENERIC RELOCATION MAPS ***********************************************************)

(* Properties with iterated tail ********************************************)

(*** isid_tls *)
lemma gr_isi_tls (n) (f): 𝐈❪f❫ → 𝐈❪⫱*[n]f❫.
#n @(nat_ind_succ … n) -n /3 width=1 by gr_isi_tl/
qed.
