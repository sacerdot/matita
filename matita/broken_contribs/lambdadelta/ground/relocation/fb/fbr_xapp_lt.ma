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

include "ground/relocation/fb/fbr_xapp.ma".
include "ground/relocation/fb/fbr_dapp_lt.ma".
include "ground/arith/nat_lt_psucc_plt.ma".
include "ground/arith/nat_lt_plt.ma".

(* EXTENDED DEPTH APPLICATION FOR FINITE RELOCATION MAPS WITH BOOLEANS ******)

(* Constructions with nlt ***************************************************)

lemma fbr_xapp_increasing (f) (n1) (n2):
      n1 < n2 → f＠❨n1❩ < f＠❨n2❩.
#f #n1 #n2 #Hn
@(nlt_ind_alt … Hn) -n1 -n2 //
#n1 #n2 #Hn #_
/4 width=1 by fbr_dapp_increasing, plt_npsucc_bi, nlt_pos_bi/
qed.

(* Constructions with nle ***************************************************)

lemma fbr_xapp_le (f) (n):
      n ≤ f＠❨n❩.
#f *
/2 width=1 by nle_pos_bi/
qed.

(* Advanced inversions ******************************************************)

lemma eq_inv_fbr_xapp_bi (f):
      injective_2_fwd … (eq …) (eq …) (λn.f＠❨n❩).
#f #n1 #n2 #Hn
elim (nat_split_lt_eq_gt n1 n2) // #H0
lapply (fbr_xapp_increasing f … H0) -H0 #H0
elim (nlt_ge_false … H0) -H0 //
qed-.
