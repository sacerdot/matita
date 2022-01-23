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
include "ground/relocation/tr_pushs.ma".
include "ground/relocation/tr_pap_pn.ma".

(* POSITIVE APPLICATION FOR TOTAL RELOCATION MAPS ***************************)

(* Constructions with tr_pushs **********************************************)

lemma tr_pap_pushs_le (n) (p) (f):
      p < ↑n → p = (⫯*[n]f)@❨p❩.
#n @(nat_ind_succ … n) -n
[ #p #f #H0
  elim (plt_inv_unit_dx … H0)
| #n #IH *
  [ #f #H0 <tr_pushs_succ //
  | #p #f <npsucc_succ #H0
    lapply (plt_inv_succ_bi … H0) -H0 #H0
    lapply (IH … f H0) -IH -H0 #H0
    <tr_pushs_succ <tr_pap_push //
  ]
]
qed-.
