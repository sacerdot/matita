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

include "ground_2A/lib/lstar.ma".
include "basic_2A/notation/relations/rdrop_5.ma".
include "basic_2A/notation/relations/rdrop_4.ma".
include "basic_2A/notation/relations/rdrop_3.ma".
include "basic_2A/grammar/lenv_length.ma".
include "basic_2A/grammar/cl_restricted_weight.ma".
include "basic_2A/substitution/lift.ma".

(* BASIC SLICING FOR LOCAL ENVIRONMENTS *************************************)

(* Basic_1: includes: drop_skip_bind *)
inductive drop (s:bool): relation4 nat nat lenv lenv ≝
| drop_atom: ∀l,m. (s = Ⓕ → m = 0) → drop s l m (⋆) (⋆)
| drop_pair: ∀I,L,V. drop s 0 0 (L.ⓑ{I}V) (L.ⓑ{I}V)
| drop_drop: ∀I,L1,L2,V,m. drop s 0 m L1 L2 → drop s 0 (m+1) (L1.ⓑ{I}V) L2
| drop_skip: ∀I,L1,L2,V1,V2,l,m.
             drop s l m L1 L2 → ⬆[l, m] V2 ≡ V1 →
             drop s (l+1) m (L1.ⓑ{I}V1) (L2.ⓑ{I}V2)
.

interpretation
   "basic slicing (local environment) abstract"
   'RDrop s l m L1 L2 = (drop s l m L1 L2).
(*
interpretation
   "basic slicing (local environment) general"
   'RDrop d e L1 L2 = (drop true d e L1 L2).
*)
interpretation
   "basic slicing (local environment) lget"
   'RDrop m L1 L2 = (drop false O m L1 L2).

definition d_liftable: predicate (lenv → relation term) ≝
                       λR. ∀K,T1,T2. R K T1 T2 → ∀L,s,l,m. ⬇[s, l, m] L ≡ K →
                       ∀U1. ⬆[l, m] T1 ≡ U1 → ∀U2. ⬆[l, m] T2 ≡ U2 → R L U1 U2.

definition d_deliftable_sn: predicate (lenv → relation term) ≝
                            λR. ∀L,U1,U2. R L U1 U2 → ∀K,s,l,m. ⬇[s, l, m] L ≡ K →
                            ∀T1. ⬆[l, m] T1 ≡ U1 →
                            ∃∃T2. ⬆[l, m] T2 ≡ U2 & R K T1 T2.

definition dropable_sn: predicate (relation lenv) ≝
                        λR. ∀L1,K1,s,l,m. ⬇[s, l, m] L1 ≡ K1 → ∀L2. R L1 L2 →
                        ∃∃K2. R K1 K2 & ⬇[s, l, m] L2 ≡ K2.

definition dropable_dx: predicate (relation lenv) ≝
                        λR. ∀L1,L2. R L1 L2 → ∀K2,s,m. ⬇[s, 0, m] L2 ≡ K2 →
                        ∃∃K1. ⬇[s, 0, m] L1 ≡ K1 & R K1 K2.

(* Basic inversion lemmas ***************************************************)

fact drop_inv_atom1_aux: ∀L1,L2,s,l,m. ⬇[s, l, m] L1 ≡ L2 → L1 = ⋆ →
                         L2 = ⋆ ∧ (s = Ⓕ → m = 0).
#L1 #L2 #s #l #m * -L1 -L2 -l -m
[ /3 width=1 by conj/
| #I #L #V #H destruct
| #I #L1 #L2 #V #m #_ #H destruct
| #I #L1 #L2 #V1 #V2 #l #m #_ #_ #H destruct
]
qed-.

(* Basic_1: was: drop_gen_sort *)
lemma drop_inv_atom1: ∀L2,s,l,m. ⬇[s, l, m] ⋆ ≡ L2 → L2 = ⋆ ∧ (s = Ⓕ → m = 0).
/2 width=4 by drop_inv_atom1_aux/ qed-.

fact drop_inv_O1_pair1_aux: ∀L1,L2,s,l,m. ⬇[s, l, m] L1 ≡ L2 → l = 0 →
                            ∀K,I,V. L1 = K.ⓑ{I}V →
                            (m = 0 ∧ L2 = K.ⓑ{I}V) ∨
                            (0 < m ∧ ⬇[s, l, m-1] K ≡ L2).
#L1 #L2 #s #l #m * -L1 -L2 -l -m
[ #l #m #_ #_ #K #J #W #H destruct
| #I #L #V #_ #K #J #W #HX destruct /3 width=1 by or_introl, conj/
| #I #L1 #L2 #V #m #HL12 #_ #K #J #W #H destruct /3 width=1 by or_intror, conj/
| #I #L1 #L2 #V1 #V2 #l #m #_ #_ >commutative_plus normalize #H destruct
]
qed-.

lemma drop_inv_O1_pair1: ∀I,K,L2,V,s,m. ⬇[s, 0, m] K. ⓑ{I} V ≡ L2 →
                         (m = 0 ∧ L2 = K.ⓑ{I}V) ∨
                         (0 < m ∧ ⬇[s, 0, m-1] K ≡ L2).
/2 width=3 by drop_inv_O1_pair1_aux/ qed-.

lemma drop_inv_pair1: ∀I,K,L2,V,s. ⬇[s, 0, 0] K.ⓑ{I}V ≡ L2 → L2 = K.ⓑ{I}V.
#I #K #L2 #V #s #H
elim (drop_inv_O1_pair1 … H) -H * // #H destruct
elim (lt_refl_false … H)
qed-.

(* Basic_1: was: drop_gen_drop *)
lemma drop_inv_drop1_lt: ∀I,K,L2,V,s,m.
                         ⬇[s, 0, m] K.ⓑ{I}V ≡ L2 → 0 < m → ⬇[s, 0, m-1] K ≡ L2.
#I #K #L2 #V #s #m #H #Hm
elim (drop_inv_O1_pair1 … H) -H * // #H destruct
elim (lt_refl_false … Hm)
qed-.

lemma drop_inv_drop1: ∀I,K,L2,V,s,m.
                      ⬇[s, 0, m+1] K.ⓑ{I}V ≡ L2 → ⬇[s, 0, m] K ≡ L2.
#I #K #L2 #V #s #m #H lapply (drop_inv_drop1_lt … H ?) -H //
qed-.

fact drop_inv_skip1_aux: ∀L1,L2,s,l,m. ⬇[s, l, m] L1 ≡ L2 → 0 < l →
                         ∀I,K1,V1. L1 = K1.ⓑ{I}V1 →
                         ∃∃K2,V2. ⬇[s, l-1, m] K1 ≡ K2 &
                                  ⬆[l-1, m] V2 ≡ V1 &
                                   L2 = K2.ⓑ{I}V2.
#L1 #L2 #s #l #m * -L1 -L2 -l -m
[ #l #m #_ #_ #J #K1 #W1 #H destruct
| #I #L #V #H elim (lt_refl_false … H)
| #I #L1 #L2 #V #m #_ #H elim (lt_refl_false … H)
| #I #L1 #L2 #V1 #V2 #l #m #HL12 #HV21 #_ #J #K1 #W1 #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_1: was: drop_gen_skip_l *)
lemma drop_inv_skip1: ∀I,K1,V1,L2,s,l,m. ⬇[s, l, m] K1.ⓑ{I}V1 ≡ L2 → 0 < l →
                      ∃∃K2,V2. ⬇[s, l-1, m] K1 ≡ K2 &
                               ⬆[l-1, m] V2 ≡ V1 &
                               L2 = K2.ⓑ{I}V2.
/2 width=3 by drop_inv_skip1_aux/ qed-.

lemma drop_inv_O1_pair2: ∀I,K,V,s,m,L1. ⬇[s, 0, m] L1 ≡ K.ⓑ{I}V →
                         (m = 0 ∧ L1 = K.ⓑ{I}V) ∨
                         ∃∃I1,K1,V1. ⬇[s, 0, m-1] K1 ≡ K.ⓑ{I}V & L1 = K1.ⓑ{I1}V1 & 0 < m.
#I #K #V #s #m *
[ #H elim (drop_inv_atom1 … H) -H #H destruct
| #L1 #I1 #V1 #H
  elim (drop_inv_O1_pair1 … H) -H *
  [ #H1 #H2 destruct /3 width=1 by or_introl, conj/
  | /3 width=5 by ex3_3_intro, or_intror/
  ]
]
qed-.

fact drop_inv_skip2_aux: ∀L1,L2,s,l,m. ⬇[s, l, m] L1 ≡ L2 → 0 < l →
                         ∀I,K2,V2. L2 = K2.ⓑ{I}V2 →
                         ∃∃K1,V1. ⬇[s, l-1, m] K1 ≡ K2 &
                                  ⬆[l-1, m] V2 ≡ V1 &
                                  L1 = K1.ⓑ{I}V1.
#L1 #L2 #s #l #m * -L1 -L2 -l -m
[ #l #m #_ #_ #J #K2 #W2 #H destruct
| #I #L #V #H elim (lt_refl_false … H)
| #I #L1 #L2 #V #m #_ #H elim (lt_refl_false … H)
| #I #L1 #L2 #V1 #V2 #l #m #HL12 #HV21 #_ #J #K2 #W2 #H destruct /2 width=5 by ex3_2_intro/
]
qed-.

(* Basic_1: was: drop_gen_skip_r *)
lemma drop_inv_skip2: ∀I,L1,K2,V2,s,l,m. ⬇[s, l, m] L1 ≡ K2.ⓑ{I}V2 → 0 < l →
                      ∃∃K1,V1. ⬇[s, l-1, m] K1 ≡ K2 & ⬆[l-1, m] V2 ≡ V1 &
                               L1 = K1.ⓑ{I}V1.
/2 width=3 by drop_inv_skip2_aux/ qed-.

lemma drop_inv_O1_gt: ∀L,K,m,s. ⬇[s, 0, m] L ≡ K → |L| < m →
                      s = Ⓣ ∧ K = ⋆.
#L elim L -L [| #L #Z #X #IHL ] #K #m #s #H normalize in ⊢ (?%?→?); #H1m
[ elim (drop_inv_atom1 … H) -H elim s -s /2 width=1 by conj/
  #_ #Hs lapply (Hs ?) // -Hs #H destruct elim (lt_zero_false … H1m)
| elim (drop_inv_O1_pair1 … H) -H * #H2m #HLK destruct
  [ elim (lt_zero_false … H1m)
  | elim (IHL … HLK) -IHL -HLK /2 width=1 by lt_plus_to_minus_r, conj/
  ]
]
qed-.

(* Basic properties *********************************************************)

lemma drop_refl_atom_O2: ∀s,l. ⬇[s, l, O] ⋆ ≡ ⋆.
/2 width=1 by drop_atom/ qed.

(* Basic_1: was by definition: drop_refl *)
lemma drop_refl: ∀L,l,s. ⬇[s, l, 0] L ≡ L.
#L elim L -L //
#L #I #V #IHL #l #s @(nat_ind_plus … l) -l /2 width=1 by drop_pair, drop_skip/
qed.

lemma drop_drop_lt: ∀I,L1,L2,V,s,m.
                    ⬇[s, 0, m-1] L1 ≡ L2 → 0 < m → ⬇[s, 0, m] L1.ⓑ{I}V ≡ L2.
#I #L1 #L2 #V #s #m #HL12 #Hm >(plus_minus_m_m m 1) /2 width=1 by drop_drop/
qed.

lemma drop_skip_lt: ∀I,L1,L2,V1,V2,s,l,m.
                    ⬇[s, l-1, m] L1 ≡ L2 → ⬆[l-1, m] V2 ≡ V1 → 0 < l →
                    ⬇[s, l, m] L1. ⓑ{I} V1 ≡ L2.ⓑ{I}V2.
#I #L1 #L2 #V1 #V2 #s #l #m #HL12 #HV21 #Hl >(plus_minus_m_m l 1) /2 width=1 by drop_skip/
qed.

lemma drop_O1_le: ∀s,m,L. m ≤ |L| → ∃K. ⬇[s, 0, m] L ≡ K.
#s #m @(nat_ind_plus … m) -m /2 width=2 by ex_intro/
#m #IHm *
[ #H elim (le_plus_xSy_O_false … H)
| #L #I #V normalize #H elim (IHm L) -IHm /3 width=2 by drop_drop, monotonic_pred, ex_intro/
]
qed-.

lemma drop_O1_lt: ∀s,L,m. m < |L| → ∃∃I,K,V. ⬇[s, 0, m] L ≡ K.ⓑ{I}V.
#s #L elim L -L
[ #m #H elim (lt_zero_false … H)
| #L #I #V #IHL #m @(nat_ind_plus … m) -m /2 width=4 by drop_pair, ex1_3_intro/
  #m #_ normalize #H elim (IHL m) -IHL /3 width=4 by drop_drop, lt_plus_to_minus_r, lt_plus_to_lt_l, ex1_3_intro/
]
qed-.

lemma drop_O1_pair: ∀L,K,m,s. ⬇[s, 0, m] L ≡ K → m ≤ |L| → ∀I,V.
                    ∃∃J,W. ⬇[s, 0, m] L.ⓑ{I}V ≡ K.ⓑ{J}W.
#L elim L -L [| #L #Z #X #IHL ] #K #m #s #H normalize #Hm #I #V
[ elim (drop_inv_atom1 … H) -H #H <(le_n_O_to_eq … Hm) -m
  #Hs destruct /2 width=3 by ex1_2_intro/
| elim (drop_inv_O1_pair1 … H) -H * #Hm #HLK destruct /2 width=3 by ex1_2_intro/
  elim (IHL … HLK … Z X) -IHL -HLK
  /3 width=3 by drop_drop_lt, le_plus_to_minus, ex1_2_intro/
]
qed-.

lemma drop_O1_ge: ∀L,m. |L| ≤ m → ⬇[Ⓣ, 0, m] L ≡ ⋆.
#L elim L -L [ #m #_ @drop_atom #H destruct ]
#L #I #V #IHL #m @(nat_ind_plus … m) -m [ #H elim (le_plus_xSy_O_false … H) ]
normalize /4 width=1 by drop_drop, monotonic_pred/
qed.

lemma drop_O1_eq: ∀L,s. ⬇[s, 0, |L|] L ≡ ⋆.
#L elim L -L /2 width=1 by drop_drop, drop_atom/
qed.

lemma drop_split: ∀L1,L2,l,m2,s. ⬇[s, l, m2] L1 ≡ L2 → ∀m1. m1 ≤ m2 →
                  ∃∃L. ⬇[s, l, m2 - m1] L1 ≡ L & ⬇[s, l, m1] L ≡ L2.
#L1 #L2 #l #m2 #s #H elim H -L1 -L2 -l -m2
[ #l #m2 #Hs #m1 #Hm12 @(ex2_intro … (⋆))
  @drop_atom #H lapply (Hs H) -s #H destruct /2 width=1 by le_n_O_to_eq/
| #I #L1 #V #m1 #Hm1 lapply (le_n_O_to_eq … Hm1) -Hm1
  #H destruct /2 width=3 by ex2_intro/
| #I #L1 #L2 #V #m2 #HL12 #IHL12 #m1 @(nat_ind_plus … m1) -m1
  [ /3 width=3 by drop_drop, ex2_intro/
  | -HL12 #m1 #_ #Hm12 lapply (le_plus_to_le_r … Hm12) -Hm12
    #Hm12 elim (IHL12 … Hm12) -IHL12 >minus_plus_plus_l
    #L #HL1 #HL2 elim (lt_or_ge (|L1|) (m2-m1)) #H0
    [ elim (drop_inv_O1_gt … HL1 H0) -HL1 #H1 #H2 destruct
      elim (drop_inv_atom1 … HL2) -HL2 #H #_ destruct
      @(ex2_intro … (⋆)) [ @drop_O1_ge normalize // ]
      @drop_atom #H destruct
    | elim (drop_O1_pair … HL1 H0 I V) -HL1 -H0 /3 width=5 by drop_drop, ex2_intro/
    ]
  ]
| #I #L1 #L2 #V1 #V2 #l #m2 #_ #HV21 #IHL12 #m1 #Hm12 elim (IHL12 … Hm12) -IHL12
  #L #HL1 #HL2 elim (lift_split … HV21 l m1) -HV21 /3 width=5 by drop_skip, ex2_intro/
]
qed-.

lemma drop_FT: ∀L1,L2,l,m. ⬇[Ⓕ, l, m] L1 ≡ L2 → ⬇[Ⓣ, l, m] L1 ≡ L2.
#L1 #L2 #l #m #H elim H -L1 -L2 -l -m
/3 width=1 by drop_atom, drop_drop, drop_skip/
qed.

lemma drop_gen: ∀L1,L2,s,l,m. ⬇[Ⓕ, l, m] L1 ≡ L2 → ⬇[s, l, m] L1 ≡ L2.
#L1 #L2 * /2 width=1 by drop_FT/
qed-.

lemma drop_T: ∀L1,L2,s,l,m. ⬇[s, l, m] L1 ≡ L2 → ⬇[Ⓣ, l, m] L1 ≡ L2.
#L1 #L2 * /2 width=1 by drop_FT/
qed-.

lemma d_liftable_LTC: ∀R. d_liftable R → d_liftable (LTC … R).
#R #HR #K #T1 #T2 #H elim H -T2
[ /3 width=10 by inj/
| #T #T2 #_ #HT2 #IHT1 #L #s #l #m #HLK #U1 #HTU1 #U2 #HTU2
  elim (lift_total T l m) /4 width=12 by step/
]
qed-.

lemma d_deliftable_sn_LTC: ∀R. d_deliftable_sn R → d_deliftable_sn (LTC … R).
#R #HR #L #U1 #U2 #H elim H -U2
[ #U2 #HU12 #K #s #l #m #HLK #T1 #HTU1
  elim (HR … HU12 … HLK … HTU1) -HR -L -U1 /3 width=3 by inj, ex2_intro/
| #U #U2 #_ #HU2 #IHU1 #K #s #l #m #HLK #T1 #HTU1
  elim (IHU1 … HLK … HTU1) -IHU1 -U1 #T #HTU #HT1
  elim (HR … HU2 … HLK … HTU) -HR -L -U /3 width=5 by step, ex2_intro/
]
qed-.

lemma dropable_sn_TC: ∀R. dropable_sn R → dropable_sn (TC … R).
#R #HR #L1 #K1 #s #l #m #HLK1 #L2 #H elim H -L2
[ #L2 #HL12 elim (HR … HLK1 … HL12) -HR -L1
  /3 width=3 by inj, ex2_intro/
| #L #L2 #_ #HL2 * #K #HK1 #HLK elim (HR … HLK … HL2) -HR -L
  /3 width=3 by step, ex2_intro/
]
qed-.

lemma dropable_dx_TC: ∀R. dropable_dx R → dropable_dx (TC … R).
#R #HR #L1 #L2 #H elim H -L2
[ #L2 #HL12 #K2 #s #m #HLK2 elim (HR … HL12 … HLK2) -HR -L2
  /3 width=3 by inj, ex2_intro/
| #L #L2 #_ #HL2 #IHL1 #K2 #s #m #HLK2 elim (HR … HL2 … HLK2) -HR -L2
  #K #HLK #HK2 elim (IHL1 … HLK) -L
  /3 width=5 by step, ex2_intro/
]
qed-.

lemma d_deliftable_sn_llstar: ∀R. d_deliftable_sn R →
                              ∀d. d_deliftable_sn (llstar … R d).
#R #HR #d #L #U1 #U2 #H @(lstar_ind_r … d U2 H) -d -U2
[ /2 width=3 by lstar_O, ex2_intro/
| #d #U #U2 #_ #HU2 #IHU1 #K #s #l #m #HLK #T1 #HTU1
  elim (IHU1 … HLK … HTU1) -IHU1 -U1 #T #HTU #HT1
  elim (HR … HU2 … HLK … HTU) -HR -L -U /3 width=5 by lstar_dx, ex2_intro/
]
qed-.

(* Basic forward lemmas *****************************************************)

(* Basic_1: was: drop_S *)
lemma drop_fwd_drop2: ∀L1,I2,K2,V2,s,m. ⬇[s, O, m] L1 ≡ K2. ⓑ{I2} V2 →
                      ⬇[s, O, m + 1] L1 ≡ K2.
#L1 elim L1 -L1
[ #I2 #K2 #V2 #s #m #H lapply (drop_inv_atom1 … H) -H * #H destruct
| #K1 #I1 #V1 #IHL1 #I2 #K2 #V2 #s #m #H
  elim (drop_inv_O1_pair1 … H) -H * #Hm #H
  [ -IHL1 destruct /2 width=1 by drop_drop/
  | @drop_drop >(plus_minus_m_m m 1) /2 width=3 by/
  ]
]
qed-.

lemma drop_fwd_length_ge: ∀L1,L2,l,m,s. ⬇[s, l, m] L1 ≡ L2 → |L1| ≤ l → |L2| = |L1|.
#L1 #L2 #l #m #s #H elim H -L1 -L2 -l -m // normalize
[ #I #L1 #L2 #V #m #_ #_ #H elim (le_plus_xSy_O_false … H)
| /4 width=2 by le_plus_to_le_r, eq_f/
]
qed-.

lemma drop_fwd_length_le_le: ∀L1,L2,l,m,s. ⬇[s, l, m] L1 ≡ L2 → l ≤ |L1| → m ≤ |L1| - l → |L2| = |L1| - m.
#L1 #L2 #l #m #s #H elim H -L1 -L2 -l -m // normalize
[ /3 width=2 by le_plus_to_le_r/
| #I #L1 #L2 #V1 #V2 #l #m #_ #_ #IHL12 >minus_plus_plus_l
  #Hl #Hm lapply (le_plus_to_le_r … Hl) -Hl
  #Hl >IHL12 // -L2 >plus_minus /2 width=3 by transitive_le/
]
qed-.

lemma drop_fwd_length_le_ge: ∀L1,L2,l,m,s. ⬇[s, l, m] L1 ≡ L2 → l ≤ |L1| → |L1| - l ≤ m → |L2| = l.
#L1 #L2 #l #m #s #H elim H -L1 -L2 -l -m normalize
[ /2 width=1 by le_n_O_to_eq/
| #I #L #V #_ <minus_n_O #H elim (le_plus_xSy_O_false … H)
| /3 width=2 by le_plus_to_le_r/
| /4 width=2 by le_plus_to_le_r, eq_f/
]
qed-.

lemma drop_fwd_length: ∀L1,L2,l,m. ⬇[Ⓕ, l, m] L1 ≡ L2 → |L1| = |L2| + m.
#L1 #L2 #l #m #H elim H -L1 -L2 -l -m // normalize /2 width=1 by/
qed-.

lemma drop_fwd_length_minus2: ∀L1,L2,l,m. ⬇[Ⓕ, l, m] L1 ≡ L2 → |L2| = |L1| - m.
#L1 #L2 #l #m #H lapply (drop_fwd_length … H) -H /2 width=1 by plus_minus, le_n/
qed-.

lemma drop_fwd_length_minus4: ∀L1,L2,l,m. ⬇[Ⓕ, l, m] L1 ≡ L2 → m = |L1| - |L2|.
#L1 #L2 #l #m #H lapply (drop_fwd_length … H) -H //
qed-.

lemma drop_fwd_length_le2: ∀L1,L2,l,m. ⬇[Ⓕ, l, m] L1 ≡ L2 → m ≤ |L1|.
#L1 #L2 #l #m #H lapply (drop_fwd_length … H) -H //
qed-.

lemma drop_fwd_length_le4: ∀L1,L2,l,m. ⬇[Ⓕ, l, m] L1 ≡ L2 → |L2| ≤ |L1|.
#L1 #L2 #l #m #H lapply (drop_fwd_length … H) -H //
qed-.

lemma drop_fwd_length_lt2: ∀L1,I2,K2,V2,l,m.
                           ⬇[Ⓕ, l, m] L1 ≡ K2. ⓑ{I2} V2 → m < |L1|.
#L1 #I2 #K2 #V2 #l #m #H
lapply (drop_fwd_length … H) normalize in ⊢ (%→?); -I2 -V2 //
qed-.

lemma drop_fwd_length_lt4: ∀L1,L2,l,m. ⬇[Ⓕ, l, m] L1 ≡ L2 → 0 < m → |L2| < |L1|.
#L1 #L2 #l #m #H lapply (drop_fwd_length … H) -H /2 width=1 by lt_minus_to_plus_r/
qed-.

lemma drop_fwd_length_eq1: ∀L1,L2,K1,K2,l,m. ⬇[Ⓕ, l, m] L1 ≡ K1 → ⬇[Ⓕ, l, m] L2 ≡ K2 →
                           |L1| = |L2| → |K1| = |K2|.
#L1 #L2 #K1 #K2 #l #m #HLK1 #HLK2 #HL12
lapply (drop_fwd_length … HLK1) -HLK1
lapply (drop_fwd_length … HLK2) -HLK2
/2 width=2 by injective_plus_r/
qed-.

lemma drop_fwd_length_eq2: ∀L1,L2,K1,K2,l,m. ⬇[Ⓕ, l, m] L1 ≡ K1 → ⬇[Ⓕ, l, m] L2 ≡ K2 →
                           |K1| = |K2| → |L1| = |L2|.
#L1 #L2 #K1 #K2 #l #m #HLK1 #HLK2 #HL12
lapply (drop_fwd_length … HLK1) -HLK1
lapply (drop_fwd_length … HLK2) -HLK2 //
qed-.

lemma drop_fwd_lw: ∀L1,L2,s,l,m. ⬇[s, l, m] L1 ≡ L2 → ♯{L2} ≤ ♯{L1}.
#L1 #L2 #s #l #m #H elim H -L1 -L2 -l -m // normalize
[ /2 width=3 by transitive_le/
| #I #L1 #L2 #V1 #V2 #l #m #_ #HV21 #IHL12
  >(lift_fwd_tw … HV21) -HV21 /2 width=1 by monotonic_le_plus_l/
]
qed-.

lemma drop_fwd_lw_lt: ∀L1,L2,l,m. ⬇[Ⓕ, l, m] L1 ≡ L2 → 0 < m → ♯{L2} < ♯{L1}.
#L1 #L2 #l #m #H elim H -L1 -L2 -l -m
[ #l #m #H >H -H //
| #I #L #V #H elim (lt_refl_false … H)
| #I #L1 #L2 #V #m #HL12 #_ #_
  lapply (drop_fwd_lw … HL12) -HL12 #HL12
  @(le_to_lt_to_lt … HL12) -HL12 //
| #I #L1 #L2 #V1 #V2 #l #m #_ #HV21 #IHL12 #H normalize in ⊢ (?%%); -I
  >(lift_fwd_tw … HV21) -V2 /3 by lt_minus_to_plus/
]
qed-.

lemma drop_fwd_rfw: ∀I,L,K,V,i. ⬇[i] L ≡ K.ⓑ{I}V → ∀T. ♯{K, V} < ♯{L, T}.
#I #L #K #V #i #HLK lapply (drop_fwd_lw … HLK) -HLK
normalize in ⊢ (%→?→?%%); /3 width=3 by le_to_lt_to_lt/
qed-.

(* Advanced inversion lemmas ************************************************)

fact drop_inv_O2_aux: ∀L1,L2,s,l,m. ⬇[s, l, m] L1 ≡ L2 → m = 0 → L1 = L2.
#L1 #L2 #s #l #m #H elim H -L1 -L2 -l -m
[ //
| //
| #I #L1 #L2 #V #m #_ #_ >commutative_plus normalize #H destruct
| #I #L1 #L2 #V1 #V2 #l #m #_ #HV21 #IHL12 #H
  >(IHL12 H) -L1 >(lift_inv_O2_aux … HV21 … H) -V2 -l -m //
]
qed-.

(* Basic_1: was: drop_gen_refl *)
lemma drop_inv_O2: ∀L1,L2,s,l. ⬇[s, l, 0] L1 ≡ L2 → L1 = L2.
/2 width=5 by drop_inv_O2_aux/ qed-.

lemma drop_inv_length_eq: ∀L1,L2,l,m. ⬇[Ⓕ, l, m] L1 ≡ L2 → |L1| = |L2| → m = 0.
#L1 #L2 #l #m #H #HL12 lapply (drop_fwd_length_minus4 … H) //
qed-.

lemma drop_inv_refl: ∀L,l,m. ⬇[Ⓕ, l, m] L ≡ L → m = 0.
/2 width=5 by drop_inv_length_eq/ qed-.

fact drop_inv_FT_aux: ∀L1,L2,s,l,m. ⬇[s, l, m] L1 ≡ L2 →
                      ∀I,K,V. L2 = K.ⓑ{I}V → s = Ⓣ → l = 0 →
                      ⬇[Ⓕ, l, m] L1 ≡ K.ⓑ{I}V.
#L1 #L2 #s #l #m #H elim H -L1 -L2 -l -m
[ #l #m #_ #J #K #W #H destruct
| #I #L #V #J #K #W #H destruct //
| #I #L1 #L2 #V #m #_ #IHL12 #J #K #W #H1 #H2 destruct
  /3 width=1 by drop_drop/
| #I #L1 #L2 #V1 #V2 #l #m #_ #_ #_ #J #K #W #_ #_
  <plus_n_Sm #H destruct
]
qed-.

lemma drop_inv_FT: ∀I,L,K,V,m. ⬇[Ⓣ, 0, m] L ≡ K.ⓑ{I}V → ⬇[m] L ≡ K.ⓑ{I}V.
/2 width=5 by drop_inv_FT_aux/ qed.

lemma drop_inv_gen: ∀I,L,K,V,s,m. ⬇[s, 0, m] L ≡ K.ⓑ{I}V → ⬇[m] L ≡ K.ⓑ{I}V.
#I #L #K #V * /2 width=1 by drop_inv_FT/
qed-.

lemma drop_inv_T: ∀I,L,K,V,s,m. ⬇[Ⓣ, 0, m] L ≡ K.ⓑ{I}V → ⬇[s, 0, m] L ≡ K.ⓑ{I}V.
#I #L #K #V * /2 width=1 by drop_inv_FT/
qed-.

(* Basic_1: removed theorems 50:
            drop_ctail drop_skip_flat
            cimp_flat_sx cimp_flat_dx cimp_bind cimp_getl_conf
            drop_clear drop_clear_O drop_clear_S
            clear_gen_sort clear_gen_bind clear_gen_flat clear_gen_flat_r
            clear_gen_all clear_clear clear_mono clear_trans clear_ctail clear_cle
            getl_ctail_clen getl_gen_tail clear_getl_trans getl_clear_trans
            getl_clear_bind getl_clear_conf getl_dec getl_drop getl_drop_conf_lt
            getl_drop_conf_ge getl_conf_ge_drop getl_drop_conf_rev
            drop_getl_trans_lt drop_getl_trans_le drop_getl_trans_ge
            getl_drop_trans getl_flt getl_gen_all getl_gen_sort getl_gen_O
            getl_gen_S getl_gen_2 getl_gen_flat getl_gen_bind getl_conf_le
            getl_trans getl_refl getl_head getl_flat getl_ctail getl_mono
*)
