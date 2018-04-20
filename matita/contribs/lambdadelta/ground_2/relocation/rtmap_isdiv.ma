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

include "ground_2/notation/relations/isdivergent_1.ma".
include "ground_2/relocation/rtmap_nexts.ma".
include "ground_2/relocation/rtmap_tls.ma".

(* RELOCATION MAP ***********************************************************)

coinductive isdiv: predicate rtmap ≝
| isdiv_next: ∀f,g. isdiv f → ↑f = g → isdiv g
.

interpretation "test for divergence (rtmap)"
   'IsDivergent f = (isdiv f).

(* Basic inversion lemmas ***************************************************)

lemma isdiv_inv_gen: ∀g. 𝛀⦃g⦄ → ∃∃f. 𝛀⦃f⦄ & ↑f = g.
#g * -g
#f #g #Hf * /2 width=3 by ex2_intro/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma isdiv_inv_next: ∀g. 𝛀⦃g⦄ → ∀f. ↑f = g → 𝛀⦃f⦄.
#g #H elim (isdiv_inv_gen … H) -H
#f #Hf * -g #g #H >(injective_next … H) -H //
qed-.

lemma isdiv_inv_push: ∀g. 𝛀⦃g⦄ → ∀f. ⫯f = g → ⊥.
#g #H elim (isdiv_inv_gen … H) -H
#f #Hf * -g #g #H elim (discr_push_next … H)
qed-.

(* Main inversion lemmas ****************************************************)

corec theorem isdiv_inv_eq_repl: ∀f1,f2. 𝛀⦃f1⦄ → 𝛀⦃f2⦄ → f1 ≡ f2.
#f1 #f2 #H1 #H2
cases (isdiv_inv_gen … H1) -H1
cases (isdiv_inv_gen … H2) -H2
/3 width=5 by eq_next/
qed-.

(* Basic properties *********************************************************)

corec lemma isdiv_eq_repl_back: eq_repl_back … isdiv.
#f1 #H cases (isdiv_inv_gen … H) -H
#g1 #Hg1 #H1 #f2 #Hf cases (eq_inv_nx … Hf … H1) -f1
/3 width=3 by isdiv_next/
qed-.

lemma isdiv_eq_repl_fwd: eq_repl_fwd … isdiv.
/3 width=3 by isdiv_eq_repl_back, eq_repl_sym/ qed-.

(* Alternative definition ***************************************************)

corec lemma eq_next_isdiv: ∀f. ↑f ≡ f → 𝛀⦃f⦄.
#f #H cases (eq_inv_nx … H) -H /4 width=3 by isdiv_next, eq_trans/
qed.

corec lemma eq_next_inv_isdiv: ∀f. 𝛀⦃f⦄ → ↑f ≡ f.
#f * -f
#f #g #Hf #Hg @(eq_next … Hg) [2: @eq_next_inv_isdiv // | skip ]
@eq_f //
qed-.

(* Properties with iterated next ********************************************)

lemma isdiv_nexts: ∀n,f. 𝛀⦃f⦄ → 𝛀⦃↑*[n]f⦄.
#n elim n -n /3 width=3 by isdiv_next/
qed.

(* Inversion lemmas with iterated next **************************************)

lemma isdiv_inv_nexts: ∀n,g. 𝛀⦃↑*[n]g⦄ → 𝛀⦃g⦄.
#n elim n -n /3 width=3 by isdiv_inv_next/
qed.

(* Properties with tail *****************************************************)

lemma isdiv_tl: ∀f. 𝛀⦃f⦄ → 𝛀⦃⫱f⦄.
#f cases (pn_split f) * #g * -f #H
[ elim (isdiv_inv_push … H) -H //
| /2 width=3 by isdiv_inv_next/
]
qed.

(* Properties with iterated tail ********************************************)

lemma isdiv_tls: ∀n,g. 𝛀⦃g⦄ → 𝛀⦃⫱*[n]g⦄.
#n elim n -n /3 width=1 by isdiv_tl/
qed.
