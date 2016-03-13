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

include "basic_2/static/sh.ma".

(* SORT DEGREE **************************************************************)

(* sort degree specification *)
record sd (h:sh): Type[0] ≝ {
   deg      : relation nat;                            (* degree of the sort *)
   deg_total: ∀k. ∃d. deg k d;                         (* functional relation axioms *)
   deg_mono : ∀k,d1,d2. deg k d1 → deg k d2 → d1 = d2;
   deg_next : ∀k,d. deg k d → deg (next h k) (d - 1)   (* compatibility condition *)
}.

(* Notable specifications ***************************************************)

definition deg_O: relation nat ≝ λk,d. d = 0.

definition sd_O: ∀h. sd h ≝ λh. mk_sd h deg_O ….
/2 width=2 by le_n_O_to_eq, le_n, ex_intro/ defined.

inductive deg_SO (h:sh) (k:nat) (k0:nat): predicate nat ≝
| deg_SO_pos : ∀d0. (next h)^d0 k0 = k → deg_SO h k k0 (d0 + 1)
| deg_SO_zero: ((∃d0. (next h)^d0 k0 = k) → ⊥) → deg_SO h k k0 0
.

fact deg_SO_inv_pos_aux: ∀h,k,k0,d0. deg_SO h k k0 d0 → ∀d. d0 = d + 1 →
                         (next h)^d k0 = k.
#h #k #k0 #d0 * -d0
[ #d0 #Hd0 #d #H
  lapply (injective_plus_l … H) -H #H destruct //
| #_ #d0 <plus_n_Sm #H destruct
]
qed.

lemma deg_SO_inv_pos: ∀h,k,k0,d0. deg_SO h k k0 (d0 + 1) → (next h)^d0 k0 = k.
/2 width=3 by deg_SO_inv_pos_aux/ qed-.

lemma deg_SO_refl: ∀h,k. deg_SO h k k 1.
#h #k @(deg_SO_pos … 0 ?) //
qed.

lemma deg_SO_gt: ∀h,k1,k2. k1 < k2 → deg_SO h k1 k2 0.
#h #k1 #k2 #HK12 @deg_SO_zero * #d elim d -d normalize
[ #H destruct
  elim (lt_refl_false … HK12)
| #d #_ #H
  lapply (next_lt h ((next h)^d k2)) >H -H #H
  lapply (transitive_lt … H HK12) -k1 #H1
  lapply (nexts_le h k2 d) #H2
  lapply (le_to_lt_to_lt … H2 H1) -h -d #H
  elim (lt_refl_false … H)
]
qed.

definition sd_SO: ∀h. nat → sd h ≝ λh,k. mk_sd h (deg_SO h k) ….
[ #k0
  lapply (nexts_dec h k0 k) *
  [ * /3 width=2 by deg_SO_pos, ex_intro/ | /4 width=2 by deg_SO_zero, ex_intro/ ]
| #K0 #d1 #d2 * [ #d01 ] #H1 * [1,3: #d02 ] #H2 //
  [ < H2 in H1; -H2 #H
    lapply (nexts_inj … H) -H #H destruct //
  | elim H1 /2 width=2 by ex_intro/
  | elim H2 /2 width=2 by ex_intro/
  ]
| #k0 #d0 *
  [ #d #H destruct elim d -d normalize
    /2 width=1 by deg_SO_gt, deg_SO_pos, next_lt/
  | #H1 @deg_SO_zero * #d #H2 destruct
    @H1 -H1 @(ex_intro … (S d)) /2 width=1 by sym_eq/ (**) (* explicit constructor *)
  ]
]
defined.

rec definition sd_d (h:sh) (k:nat) (d:nat) on d : sd h ≝
   match d with
   [ O   ⇒ sd_O h
   | S d ⇒ match d with
           [ O ⇒ sd_SO h k
           | _ ⇒ sd_d h (next h k) d
           ]
   ].

(* Basic inversion lemmas ***************************************************)

lemma deg_inv_pred: ∀h,g,k,d. deg h g (next h k) (d+1) → deg h g k (d+2).
#h #g #k #d #H1
elim (deg_total h g k) #d0 #H0
lapply (deg_next … H0) #H2
lapply (deg_mono … H1 H2) -H1 -H2 #H
<(associative_plus d 1 1) >H <plus_minus_m_m /2 width=3 by transitive_le/
qed-.

lemma deg_inv_prec: ∀h,g,k,d,d0. deg h g ((next h)^d k) (d0+1) → deg h g k (d+d0+1).
#h #g #k #d @(nat_ind_plus … d) -d //
#d #IHd #d0 >iter_SO #H
lapply (deg_inv_pred … H) -H <(associative_plus d0 1 1) #H
lapply (IHd … H) -IHd -H //
qed-.

(* Basic properties *********************************************************)

lemma deg_iter: ∀h,g,k,d1,d2. deg h g k d1 → deg h g ((next h)^d2 k) (d1-d2).
#h #g #k #d1 #d2 @(nat_ind_plus … d2) -d2  [ <minus_n_O // ]
#d2 #IHd2 #Hkd1 >iter_SO <minus_plus /3 width=1 by deg_next/
qed.

lemma deg_next_SO: ∀h,g,k,d. deg h g k (d+1) → deg h g (next h k) d.
#h #g #k #d #Hkd
lapply (deg_next … Hkd) -Hkd <minus_plus_m_m //
qed-.

lemma sd_d_SS: ∀h,k,d. sd_d h k (d + 2) = sd_d h (next h k) (d + 1).
#h #k #d <plus_n_Sm <plus_n_Sm //
qed.

lemma sd_d_correct: ∀h,d,k. deg h (sd_d h k d) k d.
#h #d @(nat_ind_plus … d) -d // #d @(nat_ind_plus … d) -d /3 width=1 by deg_inv_pred/
qed.
