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

include "static_2/relocation/drops.ma".
include "static_2/s_computation/fqup.ma".

(* PLUS-ITERATED SUPCLOSURE *************************************************)

(* Properties with generic slicing for local environments *******************)

lemma fqup_drops_succ: ∀b,G,K,T,i,L,U. ⇩*[↑i] L ≘ K → ⇧*[↑i] T ≘ U →
                       ⦃G,L,U⦄ ⬂+[b] ⦃G,K,T⦄.
#b #G #K #T #i elim i -i
[ #L #U #HLK #HTU elim (drops_inv_succ … HLK) -HLK
  #I #Y #HY #H destruct <(drops_fwd_isid … HY) -K //
  /3 width=2 by fqu_fqup, fqu_drop/
| #l #IH #L #U #HLK #HTU elim (drops_inv_succ … HLK) -HLK
  #I #Y #HY #H destruct
  elim (lifts_split_trans … HTU … (𝐔❴↑l❵) (𝐔❴1❵)) -HTU
  /4 width=5 by fqup_strap2, fqu_drop/
]
qed.

lemma fqup_drops_strap1: ∀b,G1,G2,L1,K1,K2,T1,T2,U1,i. ⇩*[i] L1 ≘ K1 → ⇧*[i] T1 ≘ U1 →
                         ⦃G1,K1,T1⦄ ⬂[b] ⦃G2,K2,T2⦄ → ⦃G1,L1,U1⦄ ⬂+[b] ⦃G2,K2,T2⦄.
#b #G1 #G2 #L1 #K1 #K2 #T1 #T2 #U1 *
[ #HLK1 #HTU1 #HT12
  >(drops_fwd_isid … HLK1) -L1 //
  <(lifts_fwd_isid … HTU1) -U1 /2 width=1 by fqu_fqup/
| /3 width=5 by fqup_strap1, fqup_drops_succ/
]
qed-.

lemma fqup_lref: ∀b,I,G,L,K,V,i. ⇩*[i] L ≘ K.ⓑ{I}V → ⦃G,L,#i⦄ ⬂+[b] ⦃G,K,V⦄.
/2 width=6 by fqup_drops_strap1/ qed.
