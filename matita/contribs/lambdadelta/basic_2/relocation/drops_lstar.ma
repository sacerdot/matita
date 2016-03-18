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

include "ground_2/lib/lstar.ma".
include "basic_2/relocation/lreq_lreq.ma".
include "basic_2/relocation/drops.ma".

(* GENERAL SLICING FOR LOCAL ENVIRONMENTS ***********************************)

(* Properties on reflexive and transitive closure ***************************)

(* Basic_2A1: was: d_liftable_LTC *)
lemma d2_liftable_LTC: ∀R. d_liftable2 R → d_liftable2 (LTC … R).
#R #HR #K #T1 #T2 #H elim H -T2
[ #T2 #HT12 #L #c #f #HLK #U1 #HTU1
  elim (HR … HT12 … HLK … HTU1) /3 width=3 by inj, ex2_intro/
| #T #T2 #_ #HT2 #IHT1 #L #c #f #HLK #U1 #HTU1
  elim (IHT1 … HLK … HTU1) -T1 #U #HTU #HU1
  elim (HR … HT2 … HLK … HTU) -HR -K -T /3 width=5 by step, ex2_intro/
]
qed-.

(* Basic_2A1: was: d_deliftable_sn_LTC *)
lemma d2_deliftable_sn_LTC: ∀R. d_deliftable2_sn R → d_deliftable2_sn (LTC … R).
#R #HR #L #U1 #U2 #H elim H -U2
[ #U2 #HU12 #K #c #f #HLK #T1 #HTU1
  elim (HR … HU12 … HLK … HTU1) -HR -L -U1 /3 width=3 by inj, ex2_intro/
| #U #U2 #_ #HU2 #IHU1 #K #c #f #HLK #T1 #HTU1
  elim (IHU1 … HLK … HTU1) -IHU1 -U1 #T #HTU #HT1
  elim (HR … HU2 … HLK … HTU) -HR -L -U /3 width=5 by step, ex2_intro/
]
qed-.

lemma dropable_sn_TC: ∀R. dropable_sn R → dropable_sn (LTC … R).
#R #HR #L1 #K1 #c #f #HLK1 #L2 #f2 #H elim H -L2
[ #L2 #HL12 #f1 #H elim (HR … HLK1 … HL12 … H) -HR -L1 -f2
  /3 width=3 by inj, ex2_intro/
| #L #L2 #_ #HL2 #IH #f1 #H elim (IH … H) -IH
  #K #HK1 #HLK elim (HR … HLK … HL2 … H) -HR -L -f2
  /3 width=3 by step, ex2_intro/
]
qed-.

(* Basic_2A1: was: d_liftable_llstar *)
lemma d2_liftable_llstar: ∀R. d_liftable2 R → ∀d. d_liftable2 (llstar … R d).
#R #HR #d #K #T1 #T2 #H @(lstar_ind_r … d T2 H) -d -T2
[ #L #c #f #_ #U1 #HTU1 -HR -K -c /2 width=3 by ex2_intro/
| #d #T #T2 #_ #HT2 #IHT1 #L #c #f #HLK #U1 #HTU1
  elim (IHT1 … HLK … HTU1) -T1 #U #HTU #HU1
  elim (HR … HT2 … HLK … HTU) -T /3 width=5 by lstar_dx, ex2_intro/
]
qed-.

(* Basic_2A1: was: d_deliftable_sn_llstar *)
lemma d2_deliftable_sn_llstar: ∀R. d_deliftable2_sn R →
                               ∀d. d_deliftable2_sn (llstar … R d).
#R #HR #d #L #U1 #U2 #H @(lstar_ind_r … d U2 H) -d -U2
[ /2 width=3 by lstar_O, ex2_intro/
| #d #U #U2 #_ #HU2 #IHU1 #K #c #f #HLK #T1 #HTU1
  elim (IHU1 … HLK … HTU1) -IHU1 -U1 #T #HTU #HT1
  elim (HR … HU2 … HLK … HTU) -HR -L -U /3 width=5 by lstar_dx, ex2_intro/
]
qed-.

lemma dropable_dx_TC: ∀R. dropable_dx R → dropable_dx (LTC … R).
#R #HR #L1 #L2 #f2 #H elim H -L2
[ #L2 #HL12 #K2 #c #f #HLK2 #Hf #f1 #Hf2 elim (HR … HL12 … HLK2 … Hf … Hf2) -HR -L2 -f2 -Hf
  /3 width=3 by inj, ex2_intro/
| #L #L2 #_ #HL2 #IHL1 #K2 #c #f #HLK2 #Hf #f1 #Hf2 elim (HR … HL2 … HLK2 … Hf … Hf2) -HR -L2
  #K #HLK #HK2 elim (IHL1 … HLK … Hf … Hf2) -L -f2 -Hf
  /3 width=5 by step, ex2_intro/
]
qed-.

lemma dedropable_sn_TC: ∀R. dedropable_sn R → dedropable_sn (LTC … R).
#R #HR #L1 #K1 #c #f #HLK1 #K2 #f1 #H elim H -K2
[ #K2 #HK12 #f2 #Hf elim (HR … HLK1 … HK12 … Hf) -HR -K1 -f1
  /3 width=4 by inj, ex3_intro/
| #K #K2 #_ #HK2 #IH #f2 #Hf elim (IH … Hf) -IH -K1
  #L #H1L1 #HLK #H2L1 elim (HR … HLK … HK2 … Hf) -HR -K -f1
  /3 width=6 by lreq_trans, step, ex3_intro/
]
qed-.
