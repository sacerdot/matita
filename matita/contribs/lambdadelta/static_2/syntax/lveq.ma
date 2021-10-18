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

include "ground/xoa/ex_3_1.ma".
include "ground/xoa/ex_3_4.ma".
include "ground/xoa/ex_4_1.ma".
include "ground/arith/nat_succ.ma".
include "static_2/notation/relations/voidstareq_4.ma".
include "static_2/syntax/lenv.ma".

(* EQUIVALENCE FOR LOCAL ENVIRONMENTS UP TO EXCLUSION BINDERS ***************)

inductive lveq: bi_relation nat lenv ≝
| lveq_atom   : lveq 𝟎 (⋆) 𝟎 (⋆)
| lveq_bind   : ∀I1,I2,K1,K2. lveq 𝟎 K1 𝟎 K2 →
                lveq 𝟎 (K1.ⓘ[I1]) 𝟎 (K2.ⓘ[I2])
| lveq_void_sn: ∀K1,K2,n1. lveq n1 K1 𝟎 K2 →
                lveq (↑n1) (K1.ⓧ) 𝟎 K2
| lveq_void_dx: ∀K1,K2,n2. lveq 𝟎 K1 n2 K2 →
                lveq 𝟎 K1 (↑n2) (K2.ⓧ)
.

interpretation "equivalence up to exclusion binders (local environment)"
   'VoidStarEq L1 n1 n2 L2 = (lveq n1 L1 n2 L2).

(* Basic properties *********************************************************)

lemma lveq_refl: ∀L. L ≋ⓧ*[𝟎,𝟎] L.
#L elim L -L /2 width=1 by lveq_atom, lveq_bind/
qed.

lemma lveq_sym: bi_symmetric … lveq.
#n1 #n2 #L1 #L2 #H elim H -L1 -L2 -n1 -n2
/2 width=1 by lveq_atom, lveq_bind, lveq_void_sn, lveq_void_dx/
qed-.

(* Basic inversion lemmas ***************************************************)

fact lveq_inv_zero_aux: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1,n2] L2 →
                        (𝟎 = n1) → 𝟎 = n2 →
                        ∨∨ ∧∧ ⋆ = L1 & ⋆ = L2
                         | ∃∃I1,I2,K1,K2. K1 ≋ⓧ*[𝟎,𝟎] K2 & K1.ⓘ[I1] = L1 & K2.ⓘ[I2] = L2.
#L1 #L2 #n1 #n2 * -L1 -L2 -n1 -n2
[1: /3 width=1 by or_introl, conj/
|2: /3 width=7 by ex3_4_intro, or_intror/
|*: #K1 #K2 #n #_ [ #H #_ | #_ #H ]
    elim (eq_inv_zero_nsucc … H)
]
qed-.

lemma lveq_inv_zero: ∀L1,L2. L1 ≋ⓧ*[𝟎,𝟎] L2 →
                     ∨∨ ∧∧ ⋆ = L1 & ⋆ = L2
                      | ∃∃I1,I2,K1,K2. K1 ≋ⓧ*[𝟎,𝟎] K2 & K1.ⓘ[I1] = L1 & K2.ⓘ[I2] = L2.
/2 width=5 by lveq_inv_zero_aux/ qed-.

fact lveq_inv_succ_sn_aux: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1,n2] L2 →
                           ∀m1. ↑m1 = n1 →
                           ∃∃K1. K1 ≋ⓧ*[m1,𝟎] L2 & K1.ⓧ = L1 & 𝟎 = n2.
#L1 #L2 #n1 #n2 * -L1 -L2 -n1 -n2
[1: #m #H elim (eq_inv_nsucc_zero … H)
|2: #I1 #I2 #K1 #K2 #_ #m #H elim (eq_inv_nsucc_zero … H)
|*: #K1 #K2 #n #HK #m #H
    [ >(eq_inv_nsucc_bi … H) -m /2 width=3 by ex3_intro/
    | elim (eq_inv_nsucc_zero … H)
    ]
]
qed-.

lemma lveq_inv_succ_sn: ∀L1,K2,n1,n2. L1 ≋ⓧ*[↑n1,n2] K2 →
                        ∃∃K1. K1 ≋ⓧ*[n1,𝟎] K2 & K1.ⓧ = L1 & 𝟎 = n2.
/2 width=3 by lveq_inv_succ_sn_aux/ qed-.

lemma lveq_inv_succ_dx: ∀K1,L2,n1,n2. K1 ≋ⓧ*[n1,↑n2] L2 →
                        ∃∃K2. K1 ≋ⓧ*[𝟎,n2] K2 & K2.ⓧ = L2 & 𝟎 = n1.
#K1 #L2 #n1 #n2 #H
lapply (lveq_sym … H) -H #H
elim (lveq_inv_succ_sn … H) -H /3 width=3 by lveq_sym, ex3_intro/
qed-.

fact lveq_inv_succ_aux: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1,n2] L2 →
                        ∀m1,m2. ↑m1 = n1 → ↑m2 = n2 → ⊥.
#L1 #L2 #n1 #n2 * -L1 -L2 -n1 -n2
[1: #m1 #m2 #H #_ elim (eq_inv_nsucc_zero … H)
|2: #I1 #I2 #K1 #K2 #_ #m1 #m2 #H #_ elim (eq_inv_nsucc_zero … H)
|*: #K1 #K2 #n #_ #m1 #m2 [ #_ #H | #H #_ ]
    elim (eq_inv_nsucc_zero … H)
]
qed-.

lemma lveq_inv_succ: ∀L1,L2,n1,n2. L1 ≋ⓧ*[↑n1,↑n2] L2 → ⊥.
/2 width=9 by lveq_inv_succ_aux/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma lveq_inv_bind_O: ∀I1,I2,K1,K2. K1.ⓘ[I1] ≋ⓧ*[𝟎,𝟎] K2.ⓘ[I2] → K1 ≋ⓧ*[𝟎,𝟎] K2.
#I1 #I2 #K1 #K2 #H
elim (lveq_inv_zero … H) -H * [| #Z1 #Z2 #Y1 #Y2 #HY ] #H1 #H2 destruct //
qed-.

lemma lveq_inv_atom_atom: ∀n1,n2. ⋆ ≋ⓧ*[n1,n2] ⋆ → ∧∧ 𝟎 = n1 & 𝟎 = n2.
#n1 @(nat_ind_succ …  n1) -n1 [2: #n1 #_ ]
#n2 @(nat_ind_succ …  n2) -n2 [2,4: #n2 #_ ]
#H
[ elim (lveq_inv_succ … H)
| elim (lveq_inv_succ_dx … H) -H #Y #_ #H1 #H2 destruct
| elim (lveq_inv_succ_sn … H) -H #Y #_ #H1 #H2 destruct
| /2 width=1 by conj/
]
qed-.

lemma lveq_inv_bind_atom: ∀I1,K1,n1,n2. K1.ⓘ[I1] ≋ⓧ*[n1,n2] ⋆ →
                          ∃∃m1. K1 ≋ⓧ*[m1,𝟎] ⋆ & BUnit Void = I1 & ↑m1 = n1 & 𝟎 = n2.
#I1 #K1
#n1 @(nat_ind_succ …  n1) -n1 [2: #n1 #_ ]
#n2 @(nat_ind_succ …  n2) -n2 [2,4: #n2 #_ ]
#H
[ elim (lveq_inv_succ … H)
| elim (lveq_inv_succ_dx … H) -H #Y #_ #H1 #H2 destruct
| elim (lveq_inv_succ_sn … H) -H #Y #HY #H1 #H2 destruct /2 width=3 by ex4_intro/
| elim (lveq_inv_zero … H) -H *
  [ #H1 #H2 destruct
  | #Z1 #Z2 #Y1 #Y2 #_ #H1 #H2 destruct
  ]
]
qed-.

lemma lveq_inv_atom_bind: ∀I2,K2,n1,n2. ⋆ ≋ⓧ*[n1,n2] K2.ⓘ[I2] →
                          ∃∃m2. ⋆ ≋ⓧ*[𝟎,m2] K2 & BUnit Void = I2 & 𝟎 = n1 & ↑m2 = n2.
#I2 #K2 #n1 #n2 #H
lapply (lveq_sym … H) -H #H
elim (lveq_inv_bind_atom … H) -H
/3 width=3 by lveq_sym, ex4_intro/
qed-.

lemma lveq_inv_pair_pair: ∀I1,I2,K1,K2,V1,V2,n1,n2. K1.ⓑ[I1]V1 ≋ⓧ*[n1,n2] K2.ⓑ[I2]V2 →
                          ∧∧ K1 ≋ⓧ*[𝟎,𝟎] K2 & 𝟎 = n1 & 𝟎 = n2.
#I1 #I2 #K1 #K2 #V1 #V2
#n1 @(nat_ind_succ …  n1) -n1 [2: #n1 #_ ]
#n2 @(nat_ind_succ …  n2) -n2 [2,4: #n2 #_ ]
#H
[ elim (lveq_inv_succ … H)
| elim (lveq_inv_succ_dx … H) -H #Y #_ #H1 #H2 destruct
| elim (lveq_inv_succ_sn … H) -H #Y #_ #H1 #H2 destruct
| elim (lveq_inv_zero … H) -H *
  [ #H1 #H2 destruct
  | #Z1 #Z2 #Y1 #Y2 #HY #H1 #H2 destruct /3 width=1 by and3_intro/
  ]
]
qed-.

lemma lveq_inv_void_succ_sn: ∀L1,L2,n1,n2. L1.ⓧ ≋ⓧ*[↑n1,n2] L2 →
                             ∧∧ L1 ≋ ⓧ*[n1,𝟎] L2 & 𝟎 = n2.
#L1 #L2 #n1 #n2 #H
elim (lveq_inv_succ_sn … H) -H #Y #HY #H1 #H2 destruct /2 width=1 by conj/
qed-.

lemma lveq_inv_void_succ_dx: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1,↑n2] L2.ⓧ →
                             ∧∧ L1 ≋ ⓧ*[𝟎,n2] L2 & 𝟎 = n1.
#L1 #L2 #n1 #n2 #H
lapply (lveq_sym … H) -H #H
elim (lveq_inv_void_succ_sn … H) -H
/3 width=1 by lveq_sym, conj/
qed-.

(* Advanced forward lemmas **************************************************)

lemma lveq_fwd_gen: ∀L1,L2,n1,n2. L1 ≋ⓧ*[n1,n2] L2 →
                    ∨∨ 𝟎 = n1 | 𝟎 = n2.
#L1 #L2
#n1 @(nat_ind_succ …  n1) -n1 [2: #n1 #_ ]
#n2 @(nat_ind_succ …  n2) -n2 [2,4: #n2 #_ ]
#H
[ elim (lveq_inv_succ … H) ]
/2 width=1 by or_introl, or_intror/
qed-.

lemma lveq_fwd_pair_sn:
      ∀I1,K1,L2,V1,n1,n2. K1.ⓑ[I1]V1 ≋ⓧ*[n1,n2] L2 → 𝟎 = n1.
#I1 #K1 #L2 #V1
#n1 @(nat_ind_succ …  n1) -n1 [2: #n1 #_ ] //
#n2 @(nat_ind_succ …  n2) -n2 [2: #n2 #_ ] #H
[ elim (lveq_inv_succ … H)
| elim (lveq_inv_succ_sn … H) -H #Y #_ #H1 #H2 destruct
]
qed-.

lemma lveq_fwd_pair_dx:
      ∀I2,L1,K2,V2,n1,n2. L1 ≋ⓧ*[n1,n2] K2.ⓑ[I2]V2 → 𝟎 = n2.
/3 width=6 by lveq_fwd_pair_sn, lveq_sym/ qed-.
