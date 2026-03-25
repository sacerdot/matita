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

include "ground/xoa/ex_1_2.ma".
include "delayed_updating/syntax/path_help.ma".
include "delayed_updating/syntax/path_root_le.ma".
include "delayed_updating/notation/relations/equiangular_2.ma".
include "delayed_updating/notation/relations/not_equiangular_2.ma".

(* ROOT EQUIVALENCE FOR PATH ************************************************)

definition path_req: relation2 (ℙ) (ℙ) ≝
           λp1,p2. p1 ⊑ p2 ∨ p2 ⊑ p1
.

interpretation
  "root equivalence (path)"
  'Equiangular p1 p2 = (path_req p1 p2).

interpretation
  "negated root equivalence (path)"
  'NotEquiangular p1 p2 = (negation (path_req p1 p2)).

(* Basic constructions ******************************************************)

lemma path_req_mk_le (p1) (p2):
      p1 ⊑ p2 → p1 ≚ p2.
/2 width=1 by or_introl/
qed.

lemma path_req_mk_ge (p1) (p2):
      p2 ⊑ p1 → p1 ≚ p2.
/2 width=1 by or_intror/
qed.

lemma path_req_refl: reflexive … path_req.
/2 width=1 by path_req_mk_ge/
qed.

lemma path_req_sym: symmetric … path_req.
#p1 #p2 * #Hp
/2 width=1 by path_req_mk_le, path_req_mk_ge/
qed.

(* Constructions with path_append *******************************************)

lemma path_req_mk_append (p1) (p2) (q1) (q2):
      p1●q1 =❪ℙ❫ p2●q2 → p1 ≚ p2.
#p1 #p2 #q1 #q2 #H0
elim (eq_inv_list_append_bi … H0) -H0 * #x
[ #_ #H0 | #H0 #_ ] destruct
/3 width=1 by path_req_mk_le, path_req_mk_ge/
qed.

(* Inversions with path_append **********************************************)

lemma path_req_inv_append (p1) (p2):
      p1 ≚ p2 →
      ∃∃q1,q2. p1●q1 =❪ℙ❫ p2●q2.
#p1 #p2 * #H0
elim (term_in_slice_inv_gen … H0) -H0 #q #H0 destruct
/2 width=3 by ex1_2_intro/
qed-.

(* Destructions with path_append ********************************************)

lemma path_req_des_append_bi_dx (p1) (p2) (q1) (q2):
      p1●q1 ≚ p2●q2 → p1 ≚ p2.
#p1 #p2 #q1 #q2 #H0
elim (path_req_inv_append … H0) -H0 #x1 #x2
<list_append_assoc <list_append_assoc #H0
/2 width=3 by path_req_mk_append/
qed-.

(* Constructions with term_root and term_slice ******************************)

lemma path_req_mk_in_root_slice (p1) (p2):
      p2 ϵ ▵↑p1 → p1 ≚ p2.
#p1 #p2 * #q2 #H0
lapply (term_grafted_inv_gen … H0) -H0 #H0
elim (term_in_slice_inv_gen … H0) -H0 #q1 #H0 destruct
/2 width=3 by path_req_mk_append/
qed.

(* Inversions with term_root and term_slice *********************************)

lemma path_req_inv_in_root_slice (p1) (p2):
      p1 ≚ p2 → p2 ϵ ▵↑p1.
#p1 #p2 #H0
elim (path_req_inv_append … H0) -H0 #q1 #q2 #H0
/2 width=2 by term_in_root/
qed-.

(* Advanced constructions ***************************************************)

lemma path_req_weak (p1) (p2) (q1) (q2):
      p1 ⊑ q1 → p2 ⊑ q2 → q1 ≚ q2 → p1 ≚ p2.
#p1 #p2 #q1 #q2 #Hpq1 #Hpq2 #Hq12
elim (term_in_slice_inv_gen … Hpq1) -Hpq1 #x1 #H0 destruct
elim (term_in_slice_inv_gen … Hpq2) -Hpq2 #x2 #H0 destruct
/2 width=3 by path_req_des_append_bi_dx/
qed.

(* Note: this might be removed *)
lemma path_rle_canc_dx (p0) (p1) (p2):
      p1 ⊑ p0 → p2 ⊑ p0 → p1 ≚ p2.
/2 width=5 by path_req_weak/
qed.

(* Note: this does not hold so ≚ is not transitive
lemma path_rle_canc_sx (p0) (p1) (p2):
      p0 ⊑ p1 → p0 ⊑ p2 → p1 ≚ p2.
#p0 #p1 #p2 #H1 #H2
elim (term_in_slice_inv_gen … H2) -H2 #q2 #H0 destruct
elim (term_in_slice_inv_gen … H1) -H1 #q1 #H0 destruct
*)

(* Main constructions *******************************************************)

theorem path_req_dec (p1) (p2):
        Decidable (p1 ≚ p2).
#p1 #p2
elim (path_rle_dec p1 p2) #Hnp12
[ /3 width=1 by path_req_mk_le, or_introl/ ]
elim (path_rle_dec p2 p1) #Hnp12
[ /3 width=1 by path_req_mk_ge, or_introl/ ]
@or_intror * #Hp
/2 width=1 by/
qed-.

(* Main inversions **********************************************************)

theorem path_req_inv_rcons_bi (p1) (p2) (l1) (l2):
        p1◖l1 ≚ p2◖l2 → p2◖l1 ≚ p1◖l2 →
        l1 = l2.
#p1 #p2 #l1 #l2 #H1 #H2
elim (path_req_inv_append … H1) -H1 #q1 #q2 #H1
elim (path_req_inv_append … H2) -H2 #q3 #q4 #H2
elim (eq_inv_list_append_bi … H1) -H1 * #r1 #H1r #H2r
elim (eq_inv_list_append_bi … H2) -H2 * #r2 #H3r #H4r
-q1 -q2 -q3 -q4
[ lapply (path_des_append_help_1 … H2r H4r) -r1 -r2 //
| lapply (path_des_append_help_2 … H2r H3r) -r1 -r2 //
| lapply (path_des_append_help_2 … H1r H4r) -r1 -r2 //
| lapply (path_des_append_help_1 … H1r H3r) -r1 -r2 //
]
qed-.

theorem path_nreq_rcons_AS (p):
        p◖𝗔 ⧸≚ p◖𝗦 .
#p #H0
lapply (path_req_inv_rcons_bi … H0 H0) -H0 #H0 destruct
qed-.
