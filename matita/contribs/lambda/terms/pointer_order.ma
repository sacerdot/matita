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

include "terms/pointer.ma".

(* POINTER ORDER ************************************************************)

(* Note: precedence relation on redex pointers: p ≺ q
         to serve as base for the order relations: p < q and p ≤ q *)
inductive pprec: relation ptr ≝
| pprec_nil : ∀c,q.   pprec (◊) (c::q)
| ppprc_rc  : ∀p,q.   pprec (dx::p) (rc::q)
| ppprc_sn  : ∀p,q.   pprec (rc::p) (sn::q)
| pprec_comp: ∀c,p,q. pprec p q → pprec (c::p) (c::q)
| pprec_skip:         pprec (dx::◊) ◊
.

interpretation "'precedes' on pointers"
   'prec p q = (pprec p q).

(* Note: this should go to core_notation *)
notation "hvbox(a break ≺ b)"
   non associative with precedence 45
   for @{ 'prec $a $b }.

lemma pprec_fwd_in_whd: ∀p,q. p ≺ q → in_whd q → in_whd p.
#p #q #H elim H -p -q // /2 width=1/
[ #p #q * #H destruct
| #p #q * #H destruct
| #c #p #q #_ #IHpq * #H destruct /3 width=1/
]
qed-.

(* Note: this is p < q *)
definition plt: relation ptr ≝ TC … pprec.

interpretation "'less than' on redex pointers"
   'lt p q = (plt p q).

lemma plt_step_rc: ∀p,q. p ≺ q → p < q.
/2 width=1/
qed.

lemma plt_nil: ∀c,p. ◊ < c::p.
/2 width=1/
qed.

lemma plt_skip: dx::◊ < ◊.
/2 width=1/
qed.

lemma plt_comp: ∀c,p,q. p < q → c::p < c::q.
#c #p #q #H elim H -q /3 width=1/ /3 width=3/
qed.

theorem plt_trans: transitive … plt.
/2 width=3/
qed-.

lemma plt_refl: ∀p. p < p.
#p elim p -p /2 width=1/
@(plt_trans … (dx::◊)) //
qed.

(* Note: this is p ≤ q *)
definition ple: relation ptr ≝ star … pprec.

interpretation "'less or equal to' on redex pointers"
   'leq p q = (ple p q).

lemma ple_step_rc: ∀p,q. p ≺ q → p ≤ q.
/2 width=1/
qed.

lemma ple_step_sn: ∀p1,p,p2. p1 ≺ p → p ≤ p2 → p1 ≤ p2.
/2 width=3/
qed-.

lemma ple_rc: ∀p,q. dx::p ≤ rc::q.
/2 width=1/
qed.

lemma ple_sn: ∀p,q. rc::p ≤ sn::q.
/2 width=1/
qed.

lemma ple_skip: dx::◊ ≤ ◊.
/2 width=1/
qed.

lemma ple_nil: ∀p. ◊ ≤ p.
* // /2 width=1/
qed.

lemma ple_comp: ∀p1,p2. p1 ≤ p2 → ∀c. (c::p1) ≤ (c::p2).
#p1 #p2 #H elim H -p2 // /3 width=3/
qed.

lemma ple_skip_ple: ∀p. p ≤ ◊ → dx::p ≤ ◊.
#p #H @(star_ind_l ??????? H) -p //
#p #q #Hpq #_ #H @(ple_step_sn … H) -H /2 width=1/
qed.

theorem ple_trans: transitive … ple.
/2 width=3/
qed-.

lemma ple_cons: ∀p,q. dx::p ≤ sn::q.
#p #q
@(ple_trans … (rc::q)) /2 width=1/
qed.

lemma ple_dichotomy: ∀p1,p2:ptr. p1 ≤ p2 ∨ p2 ≤ p1.
#p1 elim p1 -p1
[ * /2 width=1/
| #c1 #p1 #IHp1 * /2 width=1/
  * #p2 cases c1 -c1 /2 width=1/
  elim (IHp1 p2) -IHp1 /3 width=1/
]
qed-.

lemma in_whd_ple_nil: ∀p. in_whd p → p ≤ ◊.
#p #H @(in_whd_ind … H) -p // /2 width=1/
qed.

theorem in_whd_ple: ∀p. in_whd p → ∀q. p ≤ q.
#p #H @(in_whd_ind … H) -p //
#p #_ #IHp * /3 width=1/ * #q /2 width=1/
qed.

lemma ple_nil_inv_in_whd: ∀p. p ≤ ◊ → in_whd p.
#p #H @(star_ind_l ??????? H) -p // /2 width=3 by pprec_fwd_in_whd/
qed-.

lemma ple_inv_in_whd: ∀p. (∀q. p ≤ q) → in_whd p.
/2 width=1 by ple_nil_inv_in_whd/
qed-.
