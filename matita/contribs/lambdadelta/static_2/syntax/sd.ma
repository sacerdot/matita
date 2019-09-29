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

include "static_2/syntax/sh.ma".

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
   deg_next : ∀s,d. deg o s d → deg o (⫯[h]s) (↓d)
}.

(* Notable specifications ***************************************************)

definition deg_O: relation nat ≝ λs,d. d = 0.

definition sd_O: sd ≝ mk_sd deg_O.

lemma sd_O_props (h): sd_props h sd_O ≝ mk_sd_props ….
/2 width=2 by le_n_O_to_eq, le_n, ex_intro/ qed.

(* Basic inversion lemmas ***************************************************)

lemma deg_inv_pred (h) (o): sd_props h o →
      ∀s,d. deg o (⫯[h]s) (↑d) → deg o s (↑↑d).
#h #o #Ho #s #d #H1
elim (deg_total … Ho s) #d0 #H0
lapply (deg_next … Ho … H0) #H2
lapply (deg_mono … Ho … H1 H2) -H1 -H2 #H >H >S_pred
/2 width=2 by ltn_to_ltO/
qed-.

lemma deg_inv_prec (h) (o): sd_props h o →
      ∀s,n,d. deg o ((next h)^n s) (↑d) → deg o s (↑(d+n)).
#h #o #H0 #s #n elim n -n normalize /3 width=3 by deg_inv_pred/
qed-.

(* Basic properties *********************************************************)

lemma deg_iter (h) (o): sd_props h o →
      ∀s,d,n. deg o s d → deg o ((next h)^n s) (d-n).
#h #o #Ho #s #d #n elim n -n normalize /3 width=1 by deg_next/
qed.

lemma deg_next_SO (h) (o): sd_props h o →
      ∀s,d. deg o s (↑d) → deg o (next h s) d.
/2 width=1 by deg_next/ qed-.
