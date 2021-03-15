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

include "ground/notation/relations/isidentity_1.ma".
include "ground/relocation/rtmap_tls.ma".

(* RELOCATION MAP ***********************************************************)

coinductive isid: predicate rtmap ≝
| isid_push: ∀f,g. isid f → ⫯f = g → isid g
.

interpretation "test for identity (rtmap)"
   'IsIdentity f = (isid f).

(* Basic inversion lemmas ***************************************************)

lemma isid_inv_gen: ∀g. 𝐈❪g❫ → ∃∃f. 𝐈❪f❫ & ⫯f = g.
#g * -g
#f #g #Hf * /2 width=3 by ex2_intro/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma isid_inv_push: ∀g. 𝐈❪g❫ → ∀f. ⫯f = g → 𝐈❪f❫.
#g #H elim (isid_inv_gen … H) -H
#f #Hf * -g #g #H >(injective_push … H) -H //
qed-.

lemma isid_inv_next: ∀g. 𝐈❪g❫ → ∀f. ↑f = g → ⊥.
#g #H elim (isid_inv_gen … H) -H
#f #Hf * -g #g #H elim (discr_next_push … H)
qed-.

(* Main inversion lemmas ****************************************************)

corec theorem isid_inv_eq_repl: ∀f1,f2. 𝐈❪f1❫ → 𝐈❪f2❫ → f1 ≡ f2.
#f1 #f2 #H1 #H2
cases (isid_inv_gen … H1) -H1
cases (isid_inv_gen … H2) -H2
/3 width=5 by eq_push/
qed-.

(* Basic properties *********************************************************)

corec lemma isid_eq_repl_back: eq_repl_back … isid.
#f1 #H cases (isid_inv_gen … H) -H
#g1 #Hg1 #H1 #f2 #Hf cases (eq_inv_px … Hf … H1) -f1
/3 width=3 by isid_push/
qed-.

lemma isid_eq_repl_fwd: eq_repl_fwd … isid.
/3 width=3 by isid_eq_repl_back, eq_repl_sym/ qed-.

(* Alternative definition ***************************************************)

corec lemma eq_push_isid: ∀f. ⫯f ≡ f → 𝐈❪f❫.
#f #H cases (eq_inv_px … H) -H /4 width=3 by isid_push, eq_trans/
qed.

corec lemma eq_push_inv_isid: ∀f. 𝐈❪f❫ → ⫯f ≡ f.
#f * -f
#f #g #Hf #Hg @(eq_push … Hg) [2: @eq_push_inv_isid // | skip ]
@eq_f //
qed-.

(* Properties with iterated push ********************************************)

lemma isid_pushs: ∀n,f. 𝐈❪f❫ → 𝐈❪⫯*[n]f❫.
#n @(nat_ind_succ … n) -n /3 width=3 by isid_push/
qed.

(* Inversion lemmas with iterated push **************************************)

lemma isid_inv_pushs: ∀n,g. 𝐈❪⫯*[n]g❫ → 𝐈❪g❫.
#n @(nat_ind_succ … n) -n /3 width=3 by isid_inv_push/
qed.

(* Properties with tail *****************************************************)

lemma isid_tl: ∀f. 𝐈❪f❫ → 𝐈❪⫱f❫.
#f cases (pn_split f) * #g * -f #H
[ /2 width=3 by isid_inv_push/
| elim (isid_inv_next … H) -H //
]
qed.

(* Properties with iterated tail ********************************************)

lemma isid_tls: ∀n,g. 𝐈❪g❫ → 𝐈❪⫱*[n]g❫.
#n @(nat_ind_succ … n) -n /3 width=1 by isid_tl/
qed.
