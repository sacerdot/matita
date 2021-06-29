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
include "ground/relocation/gr_ist.ma".

(* TOTALITY CONDITION FOR GENERIC RELOCATION MAPS ***************************)

(* Constructions with gr_tls ************************************************)

(*** istot_tls *)
lemma gr_ist_tls (n) (f): 𝐓❪f❫ → 𝐓❪⫰*[n]f❫.
#n @(nat_ind_succ … n) -n //
#n #IH #f #Hf <gr_tls_succ
/3 width=1 by gr_ist_tl/
qed.
