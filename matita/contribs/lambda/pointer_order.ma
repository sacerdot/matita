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

include "pointer.ma".

(* POINTER ORDER ************************************************************)

(* Note: precedence relation on redex pointers: p ≺ q
         to serve as base for the order relations: p < q and p ≤ q *)
inductive pprec: relation ptr ≝
| pprec_nil : ∀c,q.   pprec (◊) (c::q)
| ppprc_cons: ∀p,q.   pprec (dx::p) (sn::q)
| pprec_comp: ∀c,p,q. pprec p q → pprec (c::p) (c::q)
| pprec_skip:         pprec (dx::◊) ◊
.

interpretation "'precedes' on pointers"
   'prec p q = (pprec p q).

(* Note: this should go to core_notation *)
notation "hvbox(a break ≺ b)"
   non associative with precedence 45
   for @{ 'prec $a $b }.

(* Note: this is p < q *)
definition plt: relation ptr ≝ TC … pprec.

interpretation "'less than' on redex pointers"
   'lt p q = (plt p q).

(* Note: this is p ≤ q *)
definition ple: relation ptr ≝ star … pprec.

interpretation "'less or equal to' on redex pointers"
   'leq p q = (ple p q).

lemma pprec_ple: ∀p,q. p ≺ q → p ≤ q.
/2 width=1/
qed.

lemma ple_dx: dx::◊ ≤ ◊.
/2 width=1/
qed.

lemma ple_nil: ∀p. ◊ ≤ p.
* // /2 width=1/
qed.

lemma ple_comp: ∀p1,p2. p1 ≤ p2 → ∀c. (c::p1) ≤ (c::p2).
#p1 #p2 #H elim H -p2 // /3 width=3/
qed.
