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

include "ground/relocation/fu/fur_dapp_lt.ma".
include "ground/lib/exteq.ma".
include "ground/lib/functions.ma".
include "ground/notation/relations/doteq_2.ma".

(* EXTENSIONAL EQUIVALENCE FOR FINITE RELOCATION MAPS FOR UNWIND ************)

definition fur_eq: relation2 (𝔽𝕌) (𝔽𝕌) ≝
           λf1,f2. fur_dapp f1 ⊜ fur_dapp f2.

interpretation
  "extensional equivalence (finite relocation maps for unwind)"
  'DotEq f1 f2 = (fur_eq f1 f2).

(* Basic constructions ******************************************************)

lemma fur_eq_refl:
      reflexive … fur_eq.
// qed.

lemma fur_eq_repl:
      replace_2 … fur_eq fur_eq fur_eq.
// qed-.

lemma fur_eq_sym:
      symmetric … fur_eq.
/2 width=1 by fur_eq_repl/
qed-.

lemma fur_eq_trans:
      Transitive … fur_eq.
/2 width=1 by fur_eq_repl/
qed-.

lemma fur_eq_canc_sn:
      left_cancellable … fur_eq.
/2 width=1 by fur_eq_repl/
qed-.

lemma fur_eq_canc_dx:
      right_cancellable … fur_eq.
/2 width=1 by fur_eq_repl/
qed-.

lemma fur_eq_replace_sym (Q):
      replace_1_back … fur_eq Q → replace_1_fwd … fur_eq Q.
/3 width=3 by fur_eq_sym/
qed-.

(* Basic inversions *********************************************************)

lemma fur_dapp_eq_repl (p):
      compatible_2_fwd … fur_eq (eq …) (λf.f＠⧣❨p❩).
// qed-.

(* Advanced constructions ***************************************************)

lemma fur_push_id:
      (𝐢) ≐ ⫯𝐢.
* //
qed.

lemma fur_join_zero (f):
      f ≐ ⮤*[𝟎]f.
//
qed.

lemma fur_push_eq_repl:
      compatible_2_fwd … fur_eq fur_eq (λf.⫯f).
#f1 #f2 #Hf * // #p
<fur_dapp_p_dx_succ <fur_dapp_p_dx_succ
<(fur_dapp_eq_repl … Hf) -Hf //
qed.

lemma fur_join_eq_repl (n):
      compatible_2_fwd … fur_eq fur_eq (λf.⮤*[n]f).
//
qed.

lemma fur_append_eq_repl_sn (g1) (g2) (f):
      g1 ≐ g2 → g1●f ≐ g2●f.
#g1 #g2 #f elim f -f //
* [| #k ] #f #IH #Hg
[ /3 width=1 by fur_push_eq_repl/
| /3 width=1 by fur_join_eq_repl/
]
qed.

lemma fur_p_sn_eq_repl:
      compatible_2_fwd … fur_eq fur_eq (λf.𝗽◗f).
#f1 #f2 #Hf
@fur_eq_canc_sn
[| @(fur_append_eq_repl_sn … (𝐢)) // ]
<list_append_empty_dx
@fur_eq_trans
[|| @(fur_append_eq_repl_sn … (𝐢)) // ]
//
qed.

(* Advanced inversions ******************************************************)

lemma fur_eq_inv_push_bi (f1) (f2):
      (⫯f1) ≐ ⫯f2 → f1 ≐ f2.
#f1 #f2 #Hf #p
@eq_inv_psucc_bi
>fur_dapp_p_dx_succ >fur_dapp_p_dx_succ //
qed-.

lemma fur_eq_inv_id_push (f2):
      (𝐢) ≐ ⫯f2 → (𝐢) ≐ f2.
/2 width=1 by fur_eq_inv_push_bi/
qed-.

lemma fur_eq_inv_push_join (f1) (f2) (n):
      (⫯f1) ≐ ⮤*[n]f2 →
      ∧∧ ⫯f1 ≐ f2 & (𝟎) = n.
#f1 #f2 #n #H0
lapply (H0 (𝟏))
<fur_dapp_p_dx_unit <fur_dapp_j_dx #H1
lapply (fur_dapp_le f2 (𝟏+n)) <H1 -H1 #H1
lapply (ple_inv_unit_dx … H1) -H1 #H1
lapply (eq_inv_refl_nrplus_dx … H1) #H1 destruct
/2 width=1 by conj/
qed-.

lemma fur_eq_inv_id_join (f2) (n):
      (𝐢) ≐ ⮤*[n]f2 →
      ∧∧ (𝐢) ≐ f2 & (𝟎) = n.
#f2 #n #H0
lapply (fur_eq_canc_sn … fur_push_id … H0) -H0 #H0
elim (fur_eq_inv_push_join … H0) -H0
/2 width=1 by conj/
qed-.

(* Advanced eliminations ****************************************************)

lemma fur_eq_ind_id_sn (Q:predicate …):
      (Q (𝐢)) →
      (∀f. (𝐢) ≐ f → Q f → Q (⫯f)) →
      (∀f. (𝐢) ≐ f → Q f → Q (⮤*[𝟎]f)) →
      ∀f. (𝐢) ≐ f → Q f.
#Q #IH1 #IH2 #IH3 #f
elim f -f [| * [| #k ] #f #IH ] #H0
[ //
| /4 width=1 by fur_eq_inv_id_push/
| elim (fur_eq_inv_id_join … H0) -H0 #H1 #H2 destruct
  /3 width=1 by/
]
qed-.

lemma fur_eq_ind_push_sn (f1) (Q:predicate …):
      (f1 ≐ 𝐢 → Q (𝐢)) →
      (∀f2. f1 ≐ f2 → Q (⫯f2)) →
      (∀f2. ⫯f1 ≐ f2 → Q f2 → Q (⮤*[𝟎]f2)) →
      ∀f2. ⫯f1 ≐ f2 → Q f2.
#f1 #Q #IH1 #IH2 #IH3 #f2
elim f2 -f2 [| * [| #k2 ] #f2 #IH ] #H0
[ /3 width=1 by fur_eq_inv_id_push/
| /3 width=1 by fur_eq_inv_push_bi/
| elim (fur_eq_inv_push_join … H0) -H0 #H1 #H2 destruct
  /3 width=1 by/
]
qed-.
