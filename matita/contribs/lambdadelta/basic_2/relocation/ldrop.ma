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

include "basic_2/grammar/lenv_length.ma".
include "basic_2/grammar/lenv_weight.ma".
include "basic_2/relocation/lift.ma".

(* LOCAL ENVIRONMENT SLICING ************************************************)

(* Basic_1: includes: drop_skip_bind *)
inductive ldrop: nat → nat → relation lenv ≝
| ldrop_atom : ∀d,e. ldrop d e (⋆) (⋆)
| ldrop_pair : ∀L,I,V. ldrop 0 0 (L. ⓑ{I} V) (L. ⓑ{I} V)
| ldrop_ldrop: ∀L1,L2,I,V,e. ldrop 0 e L1 L2 → ldrop 0 (e + 1) (L1. ⓑ{I} V) L2
| ldrop_skip : ∀L1,L2,I,V1,V2,d,e.
               ldrop d e L1 L2 → ⇧[d,e] V2 ≡ V1 →
               ldrop (d + 1) e (L1. ⓑ{I} V1) (L2. ⓑ{I} V2)
.

interpretation "local slicing" 'RDrop d e L1 L2 = (ldrop d e L1 L2).

definition l_liftable: predicate (lenv → relation term) ≝
                       λR. ∀K,T1,T2. R K T1 T2 → ∀L,d,e. ⇩[d, e] L ≡ K →
                       ∀U1. ⇧[d, e] T1 ≡ U1 → ∀U2. ⇧[d, e] T2 ≡ U2 → R L U1 U2.

definition l_deliftable_sn: predicate (lenv → relation term) ≝
                            λR. ∀L,U1,U2. R L U1 U2 → ∀K,d,e. ⇩[d, e] L ≡ K →
                            ∀T1. ⇧[d, e] T1 ≡ U1 →
                            ∃∃T2. ⇧[d, e] T2 ≡ U2 & R K T1 T2.

definition dropable_sn: predicate (relation lenv) ≝
                        λR. ∀L1,K1,d,e. ⇩[d, e] L1 ≡ K1 → ∀L2. R L1 L2 →
                        ∃∃K2. R K1 K2 & ⇩[d, e] L2 ≡ K2.

definition dedropable_sn: predicate (relation lenv) ≝
                          λR. ∀L1,K1,d,e. ⇩[d, e] L1 ≡ K1 → ∀K2. R K1 K2 →
                          ∃∃L2. R L1 L2 & ⇩[d, e] L2 ≡ K2.

definition dropable_dx: predicate (relation lenv) ≝
                        λR. ∀L1,L2. R L1 L2 → ∀K2,e. ⇩[0, e] L2 ≡ K2 →
                        ∃∃K1. ⇩[0, e] L1 ≡ K1 & R K1 K2.

(* Basic inversion lemmas ***************************************************)

fact ldrop_inv_refl_aux: ∀d,e,L1,L2. ⇩[d, e] L1 ≡ L2 → d = 0 → e = 0 → L1 = L2.
#d #e #L1 #L2 * -d -e -L1 -L2
[ //
| //
| #L1 #L2 #I #V #e #_ #_ >commutative_plus normalize #H destruct
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ >commutative_plus normalize #H destruct
]
qed.

(* Basic_1: was: drop_gen_refl *)
lemma ldrop_inv_refl: ∀L1,L2. ⇩[0, 0] L1 ≡ L2 → L1 = L2.
/2 width=5/ qed-.

fact ldrop_inv_atom1_aux: ∀d,e,L1,L2. ⇩[d, e] L1 ≡ L2 → L1 = ⋆ →
                          L2 = ⋆.
#d #e #L1 #L2 * -d -e -L1 -L2
[ //
| #L #I #V #H destruct
| #L1 #L2 #I #V #e #_ #H destruct
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ #H destruct
]
qed.

(* Basic_1: was: drop_gen_sort *)
lemma ldrop_inv_atom1: ∀d,e,L2. ⇩[d, e] ⋆ ≡ L2 → L2 = ⋆.
/2 width=5/ qed-.

fact ldrop_inv_O1_aux: ∀d,e,L1,L2. ⇩[d, e] L1 ≡ L2 → d = 0 →
                       ∀K,I,V. L1 = K. ⓑ{I} V →
                       (e = 0 ∧ L2 = K. ⓑ{I} V) ∨
                       (0 < e ∧ ⇩[d, e - 1] K ≡ L2).
#d #e #L1 #L2 * -d -e -L1 -L2
[ #d #e #_ #K #I #V #H destruct
| #L #I #V #_ #K #J #W #HX destruct /3 width=1/
| #L1 #L2 #I #V #e #HL12 #_ #K #J #W #H destruct /3 width=1/
| #L1 #L2 #I #V1 #V2 #d #e #_ #_ >commutative_plus normalize #H destruct
]
qed.

lemma ldrop_inv_O1: ∀e,K,I,V,L2. ⇩[0, e] K. ⓑ{I} V ≡ L2 →
                    (e = 0 ∧ L2 = K. ⓑ{I} V) ∨
                    (0 < e ∧ ⇩[0, e - 1] K ≡ L2).
/2 width=3/ qed-.

lemma ldrop_inv_pair1: ∀K,I,V,L2. ⇩[0, 0] K. ⓑ{I} V ≡ L2 → L2 = K. ⓑ{I} V.
#K #I #V #L2 #H
elim (ldrop_inv_O1 … H) -H * // #H destruct
elim (lt_refl_false … H)
qed-.

(* Basic_1: was: drop_gen_drop *)
lemma ldrop_inv_ldrop1: ∀e,K,I,V,L2.
                        ⇩[0, e] K. ⓑ{I} V ≡ L2 → 0 < e → ⇩[0, e - 1] K ≡ L2.
#e #K #I #V #L2 #H #He
elim (ldrop_inv_O1 … H) -H * // #H destruct
elim (lt_refl_false … He)
qed-.

fact ldrop_inv_skip1_aux: ∀d,e,L1,L2. ⇩[d, e] L1 ≡ L2 → 0 < d →
                          ∀I,K1,V1. L1 = K1. ⓑ{I} V1 →
                          ∃∃K2,V2. ⇩[d - 1, e] K1 ≡ K2 &
                                   ⇧[d - 1, e] V2 ≡ V1 &
                                   L2 = K2. ⓑ{I} V2.
#d #e #L1 #L2 * -d -e -L1 -L2
[ #d #e #_ #I #K #V #H destruct
| #L #I #V #H elim (lt_refl_false … H)
| #L1 #L2 #I #V #e #_ #H elim (lt_refl_false … H)
| #X #L2 #Y #Z #V2 #d #e #HL12 #HV12 #_ #I #L1 #V1 #H destruct /2 width=5/
]
qed.

(* Basic_1: was: drop_gen_skip_l *)
lemma ldrop_inv_skip1: ∀d,e,I,K1,V1,L2. ⇩[d, e] K1. ⓑ{I} V1 ≡ L2 → 0 < d →
                       ∃∃K2,V2. ⇩[d - 1, e] K1 ≡ K2 &
                                ⇧[d - 1, e] V2 ≡ V1 &
                                L2 = K2. ⓑ{I} V2.
/2 width=3/ qed-.

lemma ldrop_inv_O1_pair2: ∀I,K,V,e,L1. ⇩[0, e] L1 ≡ K. ⓑ{I} V →
                          (e = 0 ∧ L1 = K. ⓑ{I} V) ∨
                          ∃∃I1,K1,V1. ⇩[0, e - 1] K1 ≡ K. ⓑ{I} V & L1 = K1.ⓑ{I1}V1 & 0 < e.
#I #K #V #e *
[ #H lapply (ldrop_inv_atom1 … H) -H #H destruct
| #L1 #I1 #V1 #H
  elim (ldrop_inv_O1 … H) -H *
  [ #H1 #H2 destruct /3 width=1/
  | /3 width=5/
  ]
]
qed-.

fact ldrop_inv_skip2_aux: ∀d,e,L1,L2. ⇩[d, e] L1 ≡ L2 → 0 < d →
                          ∀I,K2,V2. L2 = K2. ⓑ{I} V2 →
                          ∃∃K1,V1. ⇩[d - 1, e] K1 ≡ K2 &
                                   ⇧[d - 1, e] V2 ≡ V1 &
                                   L1 = K1. ⓑ{I} V1.
#d #e #L1 #L2 * -d -e -L1 -L2
[ #d #e #_ #I #K #V #H destruct
| #L #I #V #H elim (lt_refl_false … H)
| #L1 #L2 #I #V #e #_ #H elim (lt_refl_false … H)
| #L1 #X #Y #V1 #Z #d #e #HL12 #HV12 #_ #I #L2 #V2 #H destruct /2 width=5/
]
qed.

(* Basic_1: was: drop_gen_skip_r *)
lemma ldrop_inv_skip2: ∀d,e,I,L1,K2,V2. ⇩[d, e] L1 ≡ K2. ⓑ{I} V2 → 0 < d →
                       ∃∃K1,V1. ⇩[d - 1, e] K1 ≡ K2 & ⇧[d - 1, e] V2 ≡ V1 &
                                L1 = K1. ⓑ{I} V1.
/2 width=3/ qed-.

(* Basic properties *********************************************************)

(* Basic_1: was by definition: drop_refl *)
lemma ldrop_refl: ∀L. ⇩[0, 0] L ≡ L.
#L elim L -L //
qed.

lemma ldrop_ldrop_lt: ∀L1,L2,I,V,e.
                      ⇩[0, e - 1] L1 ≡ L2 → 0 < e → ⇩[0, e] L1. ⓑ{I} V ≡ L2.
#L1 #L2 #I #V #e #HL12 #He >(plus_minus_m_m e 1) // /2 width=1/
qed.

lemma ldrop_skip_lt: ∀L1,L2,I,V1,V2,d,e.
                     ⇩[d - 1, e] L1 ≡ L2 → ⇧[d - 1, e] V2 ≡ V1 → 0 < d →
                     ⇩[d, e] L1. ⓑ{I} V1 ≡ L2. ⓑ{I} V2.
#L1 #L2 #I #V1 #V2 #d #e #HL12 #HV21 #Hd >(plus_minus_m_m d 1) // /2 width=1/
qed.

lemma ldrop_O1_le: ∀i,L. i ≤ |L| → ∃K. ⇩[0, i] L ≡ K.
#i @(nat_ind_plus … i) -i /2 width=2/
#i #IHi *
[ #H lapply (le_n_O_to_eq … H) -H >commutative_plus normalize #H destruct
| #L #I #V normalize #H
  elim (IHi L ?) -IHi /2 width=1/ -H /3 width=2/
]
qed.

lemma ldrop_O1_lt: ∀L,i. i < |L| → ∃∃I,K,V. ⇩[0, i] L ≡ K.ⓑ{I}V.
#L elim L -L
[ #i #H elim (lt_zero_false … H)
| #L #I #V #IHL #i @(nat_ind_plus … i) -i /2 width=4/
  #i #_ normalize #H
  elim (IHL i ? ) -IHL /2 width=1/ -H /3 width=4/
]
qed.

lemma l_liftable_LTC: ∀R. l_liftable R → l_liftable (LTC … R).
#R #HR #K #T1 #T2 #H elim H -T2
[ /3 width=9/
| #T #T2 #_ #HT2 #IHT1 #L #d #e #HLK #U1 #HTU1 #U2 #HTU2
  elim (lift_total T d e) /4 width=11 by step/ (**) (* auto too slow without trace *)
]
qed.

lemma l_deliftable_sn_LTC: ∀R. l_deliftable_sn R → l_deliftable_sn (LTC … R).
#R #HR #L #U1 #U2 #H elim H -U2
[ #U2 #HU12 #K #d #e #HLK #T1 #HTU1
  elim (HR … HU12 … HLK … HTU1) -HR -L -U1 /3 width=3/
| #U #U2 #_ #HU2 #IHU1 #K #d #e #HLK #T1 #HTU1
  elim (IHU1 … HLK … HTU1) -IHU1 -U1 #T #HTU #HT1
  elim (HR … HU2 … HLK … HTU) -HR -L -U /3 width=5/
]
qed.

lemma dropable_sn_TC: ∀R. dropable_sn R → dropable_sn (TC … R).
#R #HR #L1 #K1 #d #e #HLK1 #L2 #H elim H -L2
[ #L2 #HL12
  elim (HR … HLK1 … HL12) -HR -L1 /3 width=3/
| #L #L2 #_ #HL2 * #K #HK1 #HLK
  elim (HR … HLK … HL2) -HR -L /3 width=3/
]
qed.

lemma dedropable_sn_TC: ∀R. dedropable_sn R → dedropable_sn (TC … R).
#R #HR #L1 #K1 #d #e #HLK1 #K2 #H elim H -K2
[ #K2 #HK12
  elim (HR … HLK1 … HK12) -HR -K1 /3 width=3/
| #K #K2 #_ #HK2 * #L #HL1 #HLK
  elim (HR … HLK … HK2) -HR -K /3 width=3/
]
qed.

lemma dropable_dx_TC: ∀R. dropable_dx R → dropable_dx (TC … R).
#R #HR #L1 #L2 #H elim H -L2
[ #L2 #HL12 #K2 #e #HLK2
  elim (HR … HL12 … HLK2) -HR -L2 /3 width=3/
| #L #L2 #_ #HL2 #IHL1 #K2 #e #HLK2
  elim (HR … HL2 … HLK2) -HR -L2 #K #HLK #HK2
  elim (IHL1 … HLK) -L /3 width=5/
]
qed.

(* Basic forvard lemmas *****************************************************)

lemma ldrop_fwd_lw: ∀L1,L2,d,e. ⇩[d, e] L1 ≡ L2 → ♯{L2} ≤ ♯{L1}.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e // normalize
[ /2 width=3/
| #L1 #L2 #I #V1 #V2 #d #e #_ #HV21 #IHL12
  >(lift_fwd_tw … HV21) -HV21 /2 width=1/
]
qed-.

(* Basic_1: was: drop_S *)
lemma ldrop_fwd_ldrop2: ∀L1,I2,K2,V2,e. ⇩[O, e] L1 ≡ K2. ⓑ{I2} V2 →
                        ⇩[O, e + 1] L1 ≡ K2.
#L1 elim L1 -L1
[ #I2 #K2 #V2 #e #H lapply (ldrop_inv_atom1 … H) -H #H destruct
| #K1 #I1 #V1 #IHL1 #I2 #K2 #V2 #e #H
  elim (ldrop_inv_O1 … H) -H * #He #H
  [ -IHL1 destruct /2 width=1/
  | @ldrop_ldrop >(plus_minus_m_m e 1) // /2 width=3/
  ]
]
qed-.

lemma ldrop_fwd_length: ∀L1,L2,d,e. ⇩[d, e] L1 ≡ L2 → |L2| ≤ |L1|.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e // normalize /2 width=1/
qed-.

lemma ldrop_fwd_ldrop2_length: ∀L1,I2,K2,V2,e.
                               ⇩[0, e] L1 ≡ K2. ⓑ{I2} V2 → e < |L1|.
#L1 elim L1 -L1
[ #I2 #K2 #V2 #e #H lapply (ldrop_inv_atom1 … H) -H #H destruct
| #K1 #I1 #V1 #IHL1 #I2 #K2 #V2 #e #H
  elim (ldrop_inv_O1 … H) -H * #He #H
  [ -IHL1 destruct //
  | lapply (IHL1 … H) -IHL1 -H #HeK1 whd in ⊢ (? ? %); /2 width=1/
  ]
]
qed-.

lemma ldrop_fwd_O1_length: ∀L1,L2,e. ⇩[0, e] L1 ≡ L2 → |L2| = |L1| - e.
#L1 elim L1 -L1
[ #L2 #e #H >(ldrop_inv_atom1 … H) -H //
| #K1 #I1 #V1 #IHL1 #L2 #e #H
  elim (ldrop_inv_O1 … H) -H * #He #H
  [ -IHL1 destruct //
  | lapply (IHL1 … H) -IHL1 -H #H >H -H normalize
    >minus_le_minus_minus_comm //
  ]
]
qed-.

lemma ldrop_fwd_lw_eq: ∀L1,L2,d,e. ⇩[d, e] L1 ≡ L2 →
                       |L1| = |L2| → ♯{L2} = ♯{L1}.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e //
[ #L1 #L2 #I #V #e #HL12 #_
  lapply (ldrop_fwd_O1_length … HL12) -HL12 #HL21 >HL21 -HL21 normalize #H -I
  lapply (discr_plus_xy_minus_xz … H) -e #H destruct
| #L1 #L2 #I #V1 #V2 #d #e #_ #HV21 #HL12 normalize in ⊢ (??%%→??%%); #H -I 
  >(lift_fwd_tw … HV21) -V2 /3 width=1 by eq_f2/ (**) (* auto is a bit slow without trace *)
]
qed-.

lemma ldrop_fwd_lw_lt: ∀L1,L2,d,e. ⇩[d, e] L1 ≡ L2 →
                      |L2| < |L1| → ♯{L2} < ♯{L1}.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e //
[ #L #I #V #H elim (lt_refl_false … H)
| #L1 #L2 #I #V #e #HL12 #_ #_
  lapply (ldrop_fwd_lw … HL12) -HL12 #HL12
  @(le_to_lt_to_lt … HL12) -HL12 //
| #L1 #L2 #I #V1 #V2 #d #e #_ #HV21 #IHL12 normalize in ⊢ (?%%→?%%); #H -I
  >(lift_fwd_tw … HV21) -V2 /4 width=2 by lt_minus_to_plus, lt_plus_to_lt_l/ (**) (* auto too slow without trace *)
]
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
