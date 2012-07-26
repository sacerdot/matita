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

include "basic_2/grammar/cl_weight.ma".
include "basic_2/substitution/lift.ma".
include "basic_2/substitution/lsubs.ma".

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

lemma ldrop_lsubs_ldrop2_abbr: ∀L1,L2,d,e. L1 ≼ [d, e] L2 →
                               ∀K2,V,i. ⇩[0, i] L2 ≡ K2. ⓓV →
                               d ≤ i → i < d + e →
                               ∃∃K1. K1 ≼ [0, d + e - i - 1] K2 &
                                     ⇩[0, i] L1 ≡ K1. ⓓV.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e
[ #d #e #K1 #V #i #H
  lapply (ldrop_inv_atom1 … H) -H #H destruct
| #L1 #L2 #K1 #V #i #_ #_ #H
  elim (lt_zero_false … H)
| #L1 #L2 #V #e #HL12 #IHL12 #K1 #W #i #H #_ #Hie
  elim (ldrop_inv_O1 … H) -H * #Hi #HLK1
  [ -IHL12 -Hie destruct
    <minus_n_O <minus_plus_m_m // /2 width=3/
  | -HL12
    elim (IHL12 … HLK1 ? ?) -IHL12 -HLK1 // /2 width=1/ -Hie >minus_minus_comm >arith_b1 // /4 width=3/
  ]
| #L1 #L2 #I #V1 #V2 #e #_ #IHL12 #K1 #W #i #H #_ #Hie
  elim (ldrop_inv_O1 … H) -H * #Hi #HLK1
  [ -IHL12 -Hie -Hi destruct
  | elim (IHL12 … HLK1 ? ?) -IHL12 -HLK1 // /2 width=1/ -Hie >minus_minus_comm >arith_b1 // /3 width=3/
  ]
| #L1 #L2 #I1 #I2 #V1 #V2 #d #e #_ #IHL12 #K1 #V #i #H #Hdi >plus_plus_comm_23 #Hide
  elim (le_inv_plus_l … Hdi) #Hdim #Hi
  lapply (ldrop_inv_ldrop1 … H ?) -H // #HLK1
  elim (IHL12 … HLK1 ? ?) -IHL12 -HLK1 // /2 width=1/ -Hdi -Hide >minus_minus_comm >arith_b1 // /3 width=3/
]
qed.

(* Basic forvard lemmas *****************************************************)

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

lemma ldrop_fwd_lw: ∀L1,L2,d,e. ⇩[d, e] L1 ≡ L2 → #{L2} ≤ #{L1}.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e // normalize
[ /2 width=3/
| #L1 #L2 #I #V1 #V2 #d #e #_ #HV21 #IHL12
  >(tw_lift … HV21) -HV21 /2 width=1/
]
qed-. 

lemma ldrop_pair2_fwd_cw: ∀I,L,K,V,d,e. ⇩[d, e] L ≡ K. ⓑ{I} V →
                          ∀T. #{K, V} < #{L, T}.
#I #L #K #V #d #e #H #T
lapply (ldrop_fwd_lw … H) -H #H
@(le_to_lt_to_lt … H) -H /3 width=1/
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
