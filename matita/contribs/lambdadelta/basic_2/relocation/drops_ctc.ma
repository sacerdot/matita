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

include "ground_2/lib/star.ma".
include "basic_2/relocation/lreq_lreq.ma".

(* GENERIC SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Properties with contextual transitive closure ****************************)

(* Basic_2A1: was: d_liftable_LTC *)
lemma d2_liftable_sn_CTC: ∀C,S,R. d_liftable2_sn C S R → d_liftable2_sn C S (CTC … R).
#C #S #R #HR #K #T1 #T2 #H elim H -T2
[ #T2 #HT12 #b #f #L #HLK #U1 #HTU1
  elim (HR … HT12 … HLK … HTU1) /3 width=3 by inj, ex2_intro/
| #T #T2 #_ #HT2 #IHT1 #b #f #L #HLK #U1 #HTU1
  elim (IHT1 … HLK … HTU1) -T1 #U #HTU #HU1
  elim (HR … HT2 … HLK … HTU) -HR -K -T /3 width=5 by step, ex2_intro/
]
qed-.

(* Basic_2A1: was: d_deliftable_sn_LTC *)
lemma d2_deliftable_sn_CTC: ∀C,S,R. d_deliftable2_sn C S R → d_deliftable2_sn C S (CTC … R).
#C #S #R #HR #L #U1 #U2 #H elim H -U2
[ #U2 #HU12 #b #f #K #HLK #T1 #HTU1
  elim (HR … HU12 … HLK … HTU1) -HR -L -U1 /3 width=3 by inj, ex2_intro/
| #U #U2 #_ #HU2 #IHU1 #b #f #K #HLK #T1 #HTU1
  elim (IHU1 … HLK … HTU1) -IHU1 -U1 #T #HTU #HT1
  elim (HR … HU2 … HLK … HTU) -HR -L -U /3 width=5 by step, ex2_intro/
]
qed-.

lemma co_dropable_sn_CTC: ∀R. co_dropable_sn R → co_dropable_sn (CTC … R).
#R #HR #b #f #L1 #K1 #HLK1 #Hf #f2 #L2 #H elim H -L2
[ #L2 #HL12 #f1 #H elim (HR … HLK1 … Hf … HL12 … H) -HR -Hf -f2 -L1
  /3 width=3 by inj, ex2_intro/
| #L #L2 #_ #HL2 #IH #f1 #H elim (IH … H) -IH
  #K #HK1 #HLK elim (HR … HLK … HL2 … H) -HR -f2 -L
  /3 width=3 by step, ex2_intro/
]
qed-.

lemma co_dropable_dx_CTC: ∀R. co_dropable_dx R → co_dropable_dx (CTC … R).
#R #HR #f2 #L1 #L2 #H elim H -L2
[ #L2 #HL12 #b #f #K2 #HLK2 #Hf #f1 #Hf2 elim (HR … HL12 … HLK2 … Hf … Hf2) -HR -Hf -f2 -L2
  /3 width=3 by inj, ex2_intro/
| #L #L2 #_ #HL2 #IHL1 #b #f #K2 #HLK2 #Hf #f1 #Hf2 elim (HR … HL2 … HLK2 … Hf … Hf2) -HR -L2
  #K #HLK #HK2 elim (IHL1 … HLK … Hf … Hf2) -Hf -f2 -L
  /3 width=5 by step, ex2_intro/
]
qed-.

lemma co_dedropable_sn_CTC: ∀R. co_dedropable_sn R → co_dedropable_sn (CTC … R).
#R #HR #b #f #L1 #K1 #HLK1 #f1 #K2 #H elim H -K2
[ #K2 #HK12 #f2 #Hf elim (HR … HLK1 … HK12 … Hf) -HR -f1 -K1
  /3 width=4 by inj, ex3_intro/
| #K #K2 #_ #HK2 #IH #f2 #Hf elim (IH … Hf) -IH -K1
  #L #H1L1 #HLK #H2L1 elim (HR … HLK … HK2 … Hf) -HR -f1 -K
  /3 width=6 by lreq_trans, step, ex3_intro/
]
qed-.
