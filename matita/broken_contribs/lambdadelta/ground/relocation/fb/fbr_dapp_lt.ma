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

include "ground/relocation/fb/fbr_dapp.ma".
include "ground/arith/pnat_lt.ma".
include "ground/lib/functions.ma".

(* DEPTH APPLICATION FOR FINITE RELOCATION MAPS WITH BOOLEANS **************)

(* Constructions with plt ***************************************************)

lemma fbr_dapp_increasing (f) (p1) (p2):
      p1 < p2 → f＠⧣❨p1❩ < f＠⧣❨p2❩.
#f elim f -f [| * #f #IH ] #p1 #p2 #Hp
[ //
| /3 width=1 by plt_succ_bi/
| @(plt_ind_alt … Hp) -p1 -p2 //
  /3 width=1 by plt_succ_bi/
]
qed.

(* Constructions with ple ***************************************************)

lemma fbr_dapp_le (f) (p):
      p ≤ f＠⧣❨p❩.
#f #p elim p -p
/4 width=3 by fbr_dapp_increasing, ple_trans, ple_succ_bi/
qed.

(* Advanced constructions ***************************************************)

lemma is_fbr_dapp_dec (f) (p2):
      Decidable (∃p1. p2 = f＠⧣❨p1❩).
#f #p2
lapply (dec_plt (λp1. p2 = f＠⧣❨p1❩) … (↑p2)) [| * ]
[ /2 width=1 by eq_pnat_dec/
| * /3 width=2 by ex_intro, or_introl/
| #H0 @or_intror * #i1 #Hi12 destruct
  /3 width=3 by fbr_dapp_le, plt_succ_dx, ex2_intro/
]
qed-.

(* Advanced inversions ******************************************************)

lemma eq_inv_fbr_dapp_bi (f):
      injective_2_fwd … (eq …) (eq …) (λp.f＠⧣❨p❩).
#f #p1 #p2 #Hp
elim (pnat_split_lt_eq_gt p1 p2) // #H0
lapply (fbr_dapp_increasing f … H0) -H0 #H0
elim (plt_ge_false … H0) -H0 //
qed-.
