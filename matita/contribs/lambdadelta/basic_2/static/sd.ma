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
   deg_total: ∀k. ∃l. deg k l;                         (* functional relation axioms *)
   deg_mono : ∀k,l1,l2. deg k l1 → deg k l2 → l1 = l2;
   deg_next : ∀k,l. deg k l → deg (next h k) (l - 1)   (* compatibility condition *)
}.

(* Notable specifications ***************************************************)

definition deg_O: relation nat ≝ λk,l. l = 0.

definition sd_O: ∀h. sd h ≝ λh. mk_sd h deg_O ….
// /2 width=1/ /2 width=2/ qed.

inductive deg_SO (h:sh) (k:nat) (k0:nat): predicate nat ≝
| deg_SO_pos : ∀l0. (next h)^l0 k0 = k → deg_SO h k k0 (l0 + 1)
| deg_SO_zero: ((∃l0. (next h)^l0 k0 = k) → ⊥) → deg_SO h k k0 0
.

fact deg_SO_inv_pos_aux: ∀h,k,k0,l0. deg_SO h k k0 l0 → ∀l. l0 = l + 1 →
                         (next h)^l k0 = k.
#h #k #k0 #l0 * -l0
[ #l0 #Hl0 #l #H
  lapply (injective_plus_l … H) -H #H destruct //
| #_ #l0 <plus_n_Sm #H destruct
]
qed.

lemma deg_SO_inv_pos: ∀h,k,k0,l0. deg_SO h k k0 (l0 + 1) → (next h)^l0 k0 = k.
/2 width=3/ qed-.

lemma deg_SO_refl: ∀h,k. deg_SO h k k 1.
#h #k @(deg_SO_pos … 0 ?) //
qed.

lemma deg_SO_gt: ∀h,k1,k2. k1 < k2 → deg_SO h k1 k2 0.
#h #k1 #k2 #HK12 @deg_SO_zero * #l elim l -l normalize
[ #H destruct
  elim (lt_refl_false … HK12)
| #l #_ #H
  lapply (next_lt h ((next h)^l k2)) >H -H #H
  lapply (transitive_lt … H HK12) -k1 #H1
  lapply (nexts_le h k2 l) #H2
  lapply (le_to_lt_to_lt … H2 H1) -h -l #H
  elim (lt_refl_false … H)
qed.

definition sd_SO: ∀h. nat → sd h ≝ λh,k. mk_sd h (deg_SO h k) ….
[ #k0
  lapply (nexts_dec h k0 k) * [ * /3 width=2/ | /4 width=2/ ]
| #K0 #l1 #l2 * [ #l01 ] #H1 * [1,3: #l02 ] #H2 //
  [ < H2 in H1; -H2 #H
    lapply (nexts_inj … H) -H #H destruct //
  | elim H1 /2 width=2/
  | elim H2 /2 width=2/
  ]
| #k0 #l0 *
  [ #l #H destruct elim l -l normalize /2 width=1/
  | #H1 @deg_SO_zero * #l #H2 destruct
    @H1 -H1 @(ex_intro … (S l)) /2 width=1/ (**) (* explicit constructor *)
  ]
]
qed.

let rec sd_l (h:sh) (k:nat) (l:nat) on l : sd h ≝
   match l with
   [ O   ⇒ sd_O h
   | S l ⇒ match l with
           [ O ⇒ sd_SO h k
           | _ ⇒ sd_l h (next h k) l
           ]
   ].

(* Basic inversion lemmas ***************************************************)

lemma deg_inv_pred: ∀h,g,k,l. deg h g (next h k) (l+1) → deg h g k (l+2).
#h #g #k #l #H1
elim (deg_total h g k) #l0 #H0
lapply (deg_next … H0) #H2
lapply (deg_mono … H1 H2) -H1 -H2 #H
<(associative_plus l 1 1) >H <plus_minus_m_m // /2 width=3 by transitive_le/
qed-.

lemma deg_inv_prec: ∀h,g,k,l,l0. deg h g ((next h)^l k) (l0+1) → deg h g k (l+l0+1).
#h #g #k #l @(nat_ind_plus … l) -l //
#l #IHl #l0 >iter_SO #H
lapply (deg_inv_pred … H) -H <(associative_plus l0 1 1) #H
lapply (IHl … H) -IHl -H //
qed-.

(* Basic properties *********************************************************)

lemma deg_iter: ∀h,g,k,l1,l2. deg h g k l1 → deg h g ((next h)^l2 k) (l1-l2).
#h #g #k #l1 #l2 @(nat_ind_plus … l2) -l2  [ <minus_n_O // ]
#l2 #IHl2 #Hkl1 >iter_SO <minus_plus /3 width=1/
qed.

lemma deg_next_SO: ∀h,g,k,l. deg h g k (l+1) → deg h g (next h k) l.
#h #g #k #l #Hkl
lapply (deg_next … Hkl) -Hkl <minus_plus_m_m //
qed-.

lemma sd_l_SS: ∀h,k,l. sd_l h k (l + 2) = sd_l h (next h k) (l + 1).
#h #k #l <plus_n_Sm <plus_n_Sm //
qed.

lemma sd_l_correct: ∀h,l,k. deg h (sd_l h k l) k l.
#h #l @(nat_ind_plus … l) -l // #l @(nat_ind_plus … l) -l // /3 width=1 by deg_inv_pred/
qed.
