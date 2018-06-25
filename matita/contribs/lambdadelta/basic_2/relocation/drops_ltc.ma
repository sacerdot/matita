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

include "ground_2/lib/ltc.ma".
include "basic_2/relocation/seq_seq.ma".

(* GENERIC SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Properties with labeled transitive closure *******************************)

lemma d2_liftable_sn_ltc: ∀A,f. associative … f →
                          ∀C,S,R. (∀n. d_liftable2_sn C S (λL. R L n)) →
                          ∀n. d_liftable2_sn C S (λL. ltc A f … (R L) n).
#A #g #Hg #C #S #R #HR #n #K #T1 #T2 #H
@(ltc_ind_dx … Hg ???? H) -n -T2
[ #n #T2 #HT12 #b #g #L #HLK #U1 #HTU1
  elim (HR … HT12 … HLK … HTU1) -b -K -T1 -HR
  /3 width=3 by ltc_rc, ex2_intro/
| #n1 #n2 #T #T2 #_ #IHT1 #HT2 #b #f #L #HLK #U1 #HTU1
  elim (IHT1 … HLK … HTU1) -T1 #U #HTU #HU1
  elim (HR … HT2 … HLK … HTU) -HR -K -T
  /3 width=5 by ltc_dx, ex2_intro/
]
qed-.

lemma d2_deliftable_sn_ltc: ∀A,f. associative … f →
                            ∀C,S,R. (∀n. d_deliftable2_sn C S (λL. R L n)) →
                            ∀n. d_deliftable2_sn C S (λL. ltc A f … (R L) n).
#A #g #Hg #C #S #R #HR #n #L #U1 #U2 #H
@(ltc_ind_dx … Hg ???? H) -n -U2
[ #n #U2 #HU12 #b #g #K #HLK #T1 #HTU1
  elim (HR … HU12 … HLK … HTU1) -b -L -U1 -HR
  /3 width=3 by ltc_rc, ex2_intro/
| #n1 #n2 #U #U2 #_ #IHU1 #HU2 #b #f #K #HLK #T1 #HTU1
  elim (IHU1 … HLK … HTU1) -IHU1 -U1 #T #HTU #HT1
  elim (HR … HU2 … HLK … HTU) -L -U -HR
  /3 width=5 by ltc_dx, ex2_intro/
]
qed-.

lemma co_dropable_sn_ltc: ∀A,f. associative … f →
                          ∀R. (∀n. co_dropable_sn (λL. R L n)) →
                          ∀n. co_dropable_sn (λL. ltc A f … (R L) n).
#A #g #Hg #R #HR #n #b #f #L1 #K1 #HLK1 #Hf #f2 #L2 #H
@(ltc_ind_dx … Hg ???? H) -n -L2
[ #n #L2 #HL12 #g1 #H
  elim (HR … HLK1 … Hf … HL12 … H) -f2 -L1 -HR -Hf
  /3 width=3 by ltc_rc, ex2_intro/
| #n1 #n2 #L #L2 #_ #IH #HL2 #f1 #H
  elim (IH … H) -IH #K #HK1 #HLK
  elim (HR … HLK … HL2 … H) -f2 -L -HR
  /3 width=3 by ltc_dx, ex2_intro/
]
qed-.

lemma co_dropable_dx_ltc: ∀A,f. associative … f →
                          ∀R. (∀n. co_dropable_dx (λL. R L n)) →
                          ∀n. co_dropable_dx (λL. ltc A f … (R L) n).
#A #g #Hg #R #HR #n #f2 #L1 #L2 #H
@(ltc_ind_dx … Hg ???? H) -n -L2
[ #n #L2 #HL12 #b #f #K2 #HLK2 #Hf #f1 #Hf2
  elim (HR … HL12 … HLK2 … Hf … Hf2) -f2 -L2 -HR -Hf
  /3 width=3 by ltc_rc, ex2_intro/
| #n1 #n2 #L #L2 #_ #IHL1 #HL2 #b #f #K2 #HLK2 #Hf #f1 #Hf2
  elim (HR … HL2 … HLK2 … Hf … Hf2) -L2 -HR #K #HLK #HK2
  elim (IHL1 … HLK … Hf … Hf2) -Hf -f2 -L
  /3 width=5 by ltc_dx, ex2_intro/
]
qed-.

lemma co_dedropable_sn_ltc: ∀A,f. associative … f →
                            ∀R. (∀n. co_dedropable_sn (λL. R L n)) →
                            ∀n. co_dedropable_sn (λL. ltc A f … (R L) n).
#A #g #Hg #R #HR #n #b #f #L1 #K1 #HLK1 #f1 #K2 #H
@(ltc_ind_dx … Hg ???? H) -n -K2
[ #n #K2 #HK12 #f2 #Hf
  elim (HR … HLK1 … HK12 … Hf) -f1 -K1 -HR
  /3 width=4 by ltc_rc, ex3_intro/
| #n1 #n2 #K #K2 #_ #IH #HK2 #f2 #Hf
  elim (IH … Hf) -K1 -IH #L #H1L1 #HLK #H2L1
  elim (HR … HLK … HK2 … Hf) -f1 -K -HR
  /3 width=6 by seq_trans, ltc_dx, ex3_intro/
]
qed-.
