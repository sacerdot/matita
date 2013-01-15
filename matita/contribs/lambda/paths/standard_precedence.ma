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

include "paths/path.ma".

(* STANDARD PRECEDENCE ******************************************************)

(* Note: standard precedence relation on paths: p ≺ q
         to serve as base for the order relations: p < q and p ≤ q *)
inductive sprec: relation path ≝
| sprec_nil : ∀c,q.   sprec (◊) (c::q)
| sprec_rc  : ∀p,q.   sprec (dx::p) (rc::q)
| sprec_sn  : ∀p,q.   sprec (rc::p) (sn::q)
| sprec_comp: ∀c,p,q. sprec p q → sprec (c::p) (c::q)
| sprec_skip:         sprec (dx::◊) ◊
.

interpretation "standard 'precedes' on paths"
   'prec p q = (sprec p q).

lemma sprec_inv_sn: ∀p,q. p ≺ q → ∀p0. sn::p0 = p →
                    ∃∃q0. p0 ≺ q0 & sn::q0 = q.
#p #q * -p -q
[ #c #q #p0 #H destruct
| #p #q #p0 #H destruct
| #p #q #p0 #H destruct
| #c #p #q #Hpq #p0 #H destruct /2 width=3/
| #p0 #H destruct
]
qed-.

lemma sprec_fwd_in_whd: ∀p,q. p ≺ q → in_whd q → in_whd p.
#p #q #H elim H -p -q // /2 width=1/
[ #p #q * #H destruct
| #p #q * #H destruct
| #c #p #q #_ #IHpq * #H destruct /3 width=1/
]
qed-.
