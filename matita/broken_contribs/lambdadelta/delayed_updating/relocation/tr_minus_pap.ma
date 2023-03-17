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

include "delayed_updating/relocation/tr_minus_pn.ma".
include "ground/relocation/tr_pap_pn.ma".
include "ground/relocation/tr_pap_lt.ma".
include "ground/arith/pnat_le_nrminus_nrplus.ma".

(* RIGHT SUBTRACTION FOR TOTAL RELOCATION MAPS ******************************)

(* Constructions with tr_pap ************************************************)

lemma tr_pap_minus_le (n) (p) (f):
      f＠⧣❨p❩ ≤ p + n →
      p = (f-n)＠⧣❨p❩.
#n @(nat_ind_succ … n) -n [| #n #IHn ]
[ #p #f #H1f
  lapply (tr_pap_increasing f p) #H2f
  >(ple_antisym … H2f H1f) in ⊢ (??%?); -H1f -H2f //
| #p elim p -p [| #p #IHp ]
  #f elim (tr_map_split f) * #g #H0 destruct
  [ //
  |2,4:
    <tr_pap_next <nrplus_succ_dx #Hf
    lapply (ple_inv_succ_bi … Hf) -Hf #Hf
    <tr_minus_next_succ /2 width=1 by/
  | <tr_minus_push_succ <tr_pap_push <tr_pap_push <nrplus_succ_sn #Hf
    lapply (ple_inv_succ_bi … Hf) -Hf #Hf
    <IHp -IHp //
  ]
]
qed-.

lemma tr_pap_minus_ge (n) (p) (f):
      p + n ≤ f＠⧣❨p❩ →
      f＠⧣❨p❩-n = (f-n)＠⧣❨p❩.
#n @(nat_ind_succ … n) -n [| #n #IHn ]
[ #p #f #_ //
| #p elim p -p [| #p #IHp ]
  #f elim (tr_map_split f) * #g #H0 destruct
  [ <tr_cons_pap_unit <nrplus_unit_sn #H0
    elim (ple_inv_succ_unit … H0)
  |2,4:
    <tr_pap_next <nrplus_succ_dx #Hg
    lapply (ple_inv_succ_bi … Hg) -Hg #Hg
    <tr_minus_next_succ <nrminus_succ_bi /2 width=1 by/
  | <tr_minus_push_succ <tr_pap_push <tr_pap_push <nrplus_succ_sn #Hg
    lapply (ple_inv_succ_bi … Hg) -Hg #Hg
    <IHp -IHp -IHn // <nrminus_succ_bi <nrminus_succ_dx
    elim (pnat_split_unit_pos (g＠⧣❨p❩-n)) // #H0
    <nrplus_succ_shift in Hg; #Hg
    lapply (pnat_le_nrminus_dx … Hg) <H0 -n -g #H0
    elim (ple_inv_succ_unit … H0)
  ]
]
qed-.
