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

include "ground_2/notation/relations/isfinite_1.ma".
include "ground_2/relocation/rtmap_fcla.ma".

(* RELOCATION MAP ***********************************************************)

definition isfin: predicate rtmap ≝
                  λf. ∃n. 𝐂❪f❫ ≘ n.

interpretation "test for finite colength (rtmap)"
   'IsFinite f = (isfin f).

(* Basic eliminators ********************************************************)

lemma isfin_ind (R:predicate rtmap): (∀f.  𝐈❪f❫ → R f) →
                                     (∀f. 𝐅❪f❫ → R f → R (⫯f)) →
                                     (∀f. 𝐅❪f❫ → R f → R (↑f)) →
                                     ∀f. 𝐅❪f❫ → R f.
#R #IH1 #IH2 #IH3 #f #H elim H -H
#n #H elim H -f -n /3 width=2 by ex_intro/
qed-.

(* Basic inversion lemmas ***************************************************)

lemma isfin_inv_push: ∀g. 𝐅❪g❫ → ∀f. ⫯f = g → 𝐅❪f❫.
#g * /3 width=4 by fcla_inv_px, ex_intro/
qed-.

lemma isfin_inv_next: ∀g. 𝐅❪g❫ → ∀f. ↑f = g → 𝐅❪f❫.
#g * #n #H #f #H0 elim (fcla_inv_nx … H … H0) -g
/2 width=2 by ex_intro/
qed-.

(* Basic properties *********************************************************)

lemma isfin_eq_repl_back: eq_repl_back … isfin.
#f1 * /3 width=4 by fcla_eq_repl_back, ex_intro/
qed-.

lemma isfin_eq_repl_fwd: eq_repl_fwd … isfin.
/3 width=3 by isfin_eq_repl_back, eq_repl_sym/ qed-.

lemma isfin_isid: ∀f. 𝐈❪f❫ → 𝐅❪f❫.
/3 width=2 by fcla_isid, ex_intro/ qed.

lemma isfin_push: ∀f. 𝐅❪f❫ → 𝐅❪⫯f❫.
#f * /3 width=2 by fcla_push, ex_intro/
qed.

lemma isfin_next: ∀f. 𝐅❪f❫ → 𝐅❪↑f❫.
#f * /3 width=2 by fcla_next, ex_intro/
qed.

(* Properties with iterated push ********************************************)

lemma isfin_pushs: ∀n,f. 𝐅❪f❫ → 𝐅❪⫯*[n]f❫.
#n elim n -n /3 width=3 by isfin_push/
qed.

(* Inversion lemmas with iterated push **************************************)

lemma isfin_inv_pushs: ∀n,g. 𝐅❪⫯*[n]g❫ → 𝐅❪g❫.
#n elim n -n /3 width=3 by isfin_inv_push/
qed.

(* Properties with tail *****************************************************)

lemma isfin_tl: ∀f. 𝐅❪f❫ → 𝐅❪⫱f❫.
#f elim (pn_split f) * #g #H #Hf destruct
/3 width=3 by isfin_inv_push, isfin_inv_next/
qed.

(* Inversion lemmas with tail ***********************************************)

lemma isfin_inv_tl: ∀f. 𝐅❪⫱f❫ → 𝐅❪f❫.
#f elim (pn_split f) * /2 width=1 by isfin_next, isfin_push/
qed-.

(* Inversion lemmas with iterated tail **************************************)

lemma isfin_inv_tls: ∀n,f. 𝐅❪⫱*[n]f❫ → 𝐅❪f❫.
#n elim n -n /3 width=1 by isfin_inv_tl/
qed-.
