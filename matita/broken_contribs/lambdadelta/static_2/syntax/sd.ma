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

include "ground/arith/nat_plus.ma".
include "ground/arith/nat_minus.ma".
include "ground/arith/nat_lt_pred.ma".
include "static_2/syntax/sh_nexts.ma".

(* SORT DEGREE **************************************************************)

(* sort degree specification *)
record sd: Type[0] ≝ {
(* degree of the sort *)
   deg: relation nat
}.

(* sort degree postulates *)
record sd_props (h) (o): Prop ≝ {
(* functional relation axioms *)
   deg_total: ∀s. ∃d. deg o s d;
   deg_mono : ∀s,d1,d2. deg o s d1 → deg o s d2 → d1 = d2;
(* compatibility condition *)
   deg_next : ∀s,d. deg o s d → deg o (⇡[h]s) (⫰d)
}.

(* Notable specifications ***************************************************)

definition deg_O: relation nat ≝ λs,d. d = 𝟎.

definition sd_O: sd ≝ mk_sd deg_O.

lemma sd_O_props (h): sd_props h sd_O ≝ mk_sd_props ….
/2 width=2 by nle_inv_zero_dx, nle_refl, ex_intro/ qed.

(* Basic inversion lemmas ***************************************************)

lemma deg_inv_pred (h) (o): sd_props h o →
      ∀s,d. deg o (⇡[h]s) (⁤↑d) → deg o s (⁤↑⁤↑d).
#h #o #Ho #s #d #H1
elim (deg_total … Ho s) #d0 #H0
lapply (deg_next … Ho … H0) #H2
lapply (deg_mono … Ho … H1 H2) -H1 -H2 #H >H <nlt_des_gen
/2 width=2 by nlt_des_lt_zero_sn/
qed-.

lemma deg_inv_prec (h) (o): sd_props h o →
      ∀s,n,d. deg o (⇡*[h,n]s) (⁤↑d) → deg o s (⁤↑(d+n)).
#h #o #H0 #s #n @(nat_ind_succ … n) -n [ // ]
#n #IH #d <sh_nexts_succ
#H <nplus_succ_shift
@IH -IH @(deg_inv_pred … H0) // (**) (* auto fails *)
qed-.

(* Basic properties *********************************************************)

lemma deg_iter (h) (o): sd_props h o →
      ∀s,d,n. deg o s d → deg o (⇡*[h,n]s) (d-n).
#h #o #Ho #s #d #n @(nat_ind_succ … n) -n [ // ]
#n #IH #H <nminus_succ_dx <sh_nexts_succ
/3 width=1 by deg_next/
qed.

lemma deg_next_SO (h) (o): sd_props h o →
      ∀s,d. deg o s (⁤↑d) → deg o (⇡[h]s) d.
/2 width=1 by deg_next/ qed-.
