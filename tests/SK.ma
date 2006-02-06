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

set "baseuri" "cic:/matita/SK/".

include "legacy/coq.ma".

alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".
alias id "eq" = "cic:/Coq/Init/Logic/eq.ind#xpointer(1/1)".
alias id "eq_ind" = "cic:/Coq/Init/Logic/eq_ind.con".
alias id "eq_ind_r" = "cic:/Coq/Init/Logic/eq_ind_r.con".
alias id "sym_eq" = "cic:/Coq/Init/Logic/sym_eq.con".

theorem SKK:
  \forall A:Set.
  \forall app: A \to A \to A.
  \forall K:A. 
  \forall S:A.
  \forall H1: (\forall x,y:A.(app (app K x) y) = x).
  \forall H2: (\forall x,y,z:A.
    (app (app (app S x) y) z) = (app (app x z) (app y z))).
  \forall x:A.
    (app (app (app S K) K) x) = x.
intros.auto paramodulation.
qed.

theorem bool1:
  \forall A:Set.
  \forall one:A.
  \forall zero:A.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall inv: A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall c2:(\forall x,y:A.(mult x y) = (mult y x)). 
  \forall d1: (\forall x,y,z:A.
              (add x (mult y z)) = (mult (add x y) (add x z))).
  \forall d2: (\forall x,y,z:A.
              (mult x (add y z)) = (add (mult x y) (mult x z))).  
  \forall i1: (\forall x:A. (add x zero) = x).
  \forall i2: (\forall x:A. (mult x one) = x).   
  \forall inv1: (\forall x:A. (add x (inv x)) = one).  
  \forall inv2: (\forall x:A. (mult x (inv x)) = zero). 
  (inv zero) = one.
intros.auto paramodulation.
qed.
  
theorem bool2:
  \forall A:Set.
  \forall one:A.
  \forall zero:A.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall inv: A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall c2:(\forall x,y:A.(mult x y) = (mult y x)). 
  \forall d1: (\forall x,y,z:A.
              (add x (mult y z)) = (mult (add x y) (add x z))).
  \forall d2: (\forall x,y,z:A.
              (mult x (add y z)) = (add (mult x y) (mult x z))).  
  \forall i1: (\forall x:A. (add x zero) = x).
  \forall i2: (\forall x:A. (mult x one) = x).   
  \forall inv1: (\forall x:A. (add x (inv x)) = one).  
  \forall inv2: (\forall x:A. (mult x (inv x)) = zero).
  \forall x:A. (mult x zero) = zero.
intros.auto paramodulation.
qed.

theorem bool3:
  \forall A:Set.
  \forall one:A.
  \forall zero:A.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall inv: A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall c2:(\forall x,y:A.(mult x y) = (mult y x)). 
  \forall d1: (\forall x,y,z:A.
              (add x (mult y z)) = (mult (add x y) (add x z))).
  \forall d2: (\forall x,y,z:A.
              (mult x (add y z)) = (add (mult x y) (mult x z))).  
  \forall i1: (\forall x:A. (add x zero) = x).
  \forall i2: (\forall x:A. (mult x one) = x).   
  \forall inv1: (\forall x:A. (add x (inv x)) = one).  
  \forall inv2: (\forall x:A. (mult x (inv x)) = zero).
  \forall x:A. (inv (inv x)) = x.
intros.auto paramodulation.
qed.

theorem bool4:
  \forall A:Set.
  \forall one:A.
  \forall zero:A.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall inv: A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall c2:(\forall x,y:A.(mult x y) = (mult y x)). 
  \forall d1: (\forall x,y,z:A.
              (add x (mult y z)) = (mult (add x y) (add x z))).
  \forall d2: (\forall x,y,z:A.
              (mult x (add y z)) = (add (mult x y) (mult x z))).  
  \forall i1: (\forall x:A. (add x zero) = x).
  \forall i2: (\forall x:A. (mult x one) = x).   
  \forall inv1: (\forall x:A. (add x (inv x)) = one).  
  \forall inv2: (\forall x:A. (mult x (inv x)) = zero). 
  \forall x,y,z:A.
    (add x y) = (add (add x (mult y z)) y).
intros.
exact (
  ((eq_ind A (add y (add x (mult y z))) 
 (\lambda x_DemodGoal_193:A.(eq A (add x y) x_DemodGoal_193)) 
 (eq_ind A x 
 (\lambda x_DemodGoal_893:A.(eq A x_DemodGoal_893 (add y (add x (mult y z))))) 
  (eq_ind A y (\lambda x_DemodGoal_894:A.(eq A x x_DemodGoal_894)) 
  (eq_ind A (add y zero) (\lambda x_Demod_554:A.(eq A x x_Demod_554)) 
  (eq_ind_r A (add zero x) (\lambda x_SupR_809:A.(eq A x_SupR_809 (add y zero))) 
  (eq_ind_r A (add y (mult (add zero y) zero)) 
  (\lambda x_Demod_553:A.(eq A (add zero x) x_Demod_553)) 
  (eq_ind A (add (add zero x) zero) 
  (\lambda x_Demod_540:A.(eq A x_Demod_540 (add x (mult (add zero x) zero)))) 
  (eq_ind_r A (mult zero x))
  (\lambda x_Demod_526:A.(eq A (add (add zero x) x_Demod_526) (add x (mult (add zero x) zero)))) 
  (eq_ind_r A (mult (add zero x) (add (add zero x) x)) 
  (\lambda x_SupR_606:A.(eq A (add (add zero x) (mult zero x)) x_SupR_606)) 
  (eq_ind A (add (add zero x) zero) 
  (\lambda x_SupR_296:A.(eq A (add (add zero x) (mult zero x)) (mult x_SupR_296 (add (add zero x) x)))) 
  (H2 (add zero x) zero x) (add zero x) (H4 (add zero x))) (add x (mult (add zero x) zero)) 
  (eq_ind A (add x zero) 
  (\lambda x_SupR_357:A.(eq A (add x (mult (add zero x) zero)) (mult x_SupR_357 (add (add zero x) x)))) 
  (eq_ind A (mult (add (add zero x) x) (add x zero)) 
  (\lambda x_SupR_310:A.(eq A (add x (mult (add zero x) zero)) x_SupR_310)) 
  (eq_ind A (add x (add zero x)) 
  (\lambda x_SupR_302:A.(eq A (add x (mult (add zero x) zero)) (mult x_SupR_302 (add x zero)))) 
  (H2 x (add zero x) zero) (add (add zero x) x) (H x (add zero x))) (mult (add x zero) (add (add zero x) x)) (H1 (add (add zero x) x) (add x zero))) (add zero x) (H x zero))) zero 
  (eq_ind A (mult zero one) 
  (\lambda x_Demod_507:A.(eq A x_Demod_507 (mult zero x))) 
  (eq_ind_r A (add x one) 
  (\lambda x_Demod_506:A.(eq A (mult zero x_Demod_506) (mult zero x))) 
  (eq_ind_r A (inv zero) 
  (\lambda x_SupR_785:A.(eq A (mult zero (add x x_SupR_785)) (mult zero x))) 
  (eq_ind A (add (mult zero x) zero) 
  (\lambda x_Demod_223:A.(eq A (mult zero (add x (inv zero))) x_Demod_223)) 
  (eq_ind A (mult zero (inv zero)) 
  (\lambda x_SupR_337:A.(eq A (mult zero (add x (inv zero))) (add (mult zero x) x_SupR_337))) 
  (H3 zero x (inv zero)) zero (H7 zero)) (mult zero x) (H4 (mult zero x))) one 
  (eq_ind A (add (inv zero) zero) 
  (\lambda x_SupR_463:A.(eq A one x_SupR_463)) 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_SupR_298:A.(eq A x_SupR_298 (add (inv zero) zero))) (H zero (inv zero)) one (H6 zero)) (inv zero) (H4 (inv zero)))) one 
  (eq_ind A (add x (inv x)) 
  (\lambda x_Demod_268:A.(eq A x_Demod_268 (add x one))) 
  (eq_ind A (mult (inv x) one) 
  (\lambda x_SupR_396:A.(eq A (add x x_SupR_396) (add x one))) 
  (eq_ind_r A (mult one (add x one)) 
  (\lambda x_Demod_199:A.(eq A (add x (mult (inv x) one)) x_Demod_199)) 
  (eq_ind A (add x (inv x)) 
  (\lambda x_SupR_268:A.(eq A (add x (mult (inv x) one)) (mult x_SupR_268 (add x one)))) (H2 x (inv x) one) one (H6 x)) (add x one) 
  (eq_ind A (mult (add x one) one) 
  (\lambda x_SupR_271:A.(eq A x_SupR_271 (mult one (add x one)))) 
  (H1 (add x one) one) (add x one) (H5 (add x one)))) (inv x) (H5 (inv x))) one (H6 x))) zero (H5 zero))) (add zero x) (H4 (add zero x))) (add y zero) 
  (eq_ind A (add zero zero) 
  (\lambda x_Demod_543:A.(eq A (add y x_Demod_543) (add y (mult (add zero y) zero)))) 
  (eq_ind_r A (mult zero y) 
  (\lambda x_Demod_524:A.(eq A (add y (add zero x_Demod_524)) (add y (mult (add zero y) zero)))) 
  (eq_ind_r A (mult zero (add zero y)) 
  (\lambda x_SupR_628:A.(eq A (add y x_SupR_628) (add y (mult (add zero y) zero)))) 
  (eq_ind_r A (mult (add y (add zero y)) (add y zero)) 
  (\lambda x_Demod_195:A.(eq A (add y (mult zero (add zero y))) x_Demod_195)) 
  (eq_ind_r A (mult (add y zero) (add y (add zero y))) 
  (\lambda x_SupR_272:A.(eq A x_SupR_272 (mult (add y (add zero y)) (add y zero)))) (H1 (add y zero) (add y (add zero y))) (add y (mult zero (add zero y))) (H2 y zero (add zero y))) (add y (mult (add zero y) zero)) (H2 y (add zero y) zero)) (add zero (mult zero y)) 
  (eq_ind A (add zero zero) 
  (\lambda x_SupR_296:A.(eq A (add zero (mult zero y)) (mult x_SupR_296 (add zero y)))) (H2 zero zero y) zero (H4 zero))) zero 
  (eq_ind A (mult zero one) 
  (\lambda x_Demod_507:A.(eq A x_Demod_507 (mult zero y))) 
  (eq_ind_r A (add y one) 
  (\lambda x_Demod_506:A.(eq A (mult zero x_Demod_506) (mult zero y))) 
  (eq_ind_r A (inv zero) 
  (\lambda x_SupR_785:A.(eq A (mult zero (add y x_SupR_785)) (mult zero y))) 
  (eq_ind A (add (mult zero y) zero) 
  (\lambda x_Demod_223:A.(eq A (mult zero (add y (inv zero))) x_Demod_223)) 
  (eq_ind A (mult zero (inv zero)) 
  (\lambda x_SupR_337:A.(eq A (mult zero (add y (inv zero))) (add (mult zero y) x_SupR_337))) (H3 zero y (inv zero)) zero (H7 zero)) (mult zero y) (H4 (mult zero y))) one 
  (eq_ind A (add (inv zero) zero) 
  (\lambda x_SupR_463:A.(eq A one x_SupR_463)) (eq_ind A (add zero (inv zero)) 
  (\lambda x_SupR_298:A.(eq A x_SupR_298 (add (inv zero) zero))) (H zero (inv zero)) one (H6 zero)) (inv zero) (H4 (inv zero)))) one 
  (eq_ind A (add y (inv y)) 
  (\lambda x_Demod_268:A.(eq A x_Demod_268 (add y one))) 
  (eq_ind A (mult (inv y) one) 
  (\lambda x_SupR_396:A.(eq A (add y x_SupR_396) (add y one))) 
  (eq_ind_r A (mult one (add y one)) 
  (\lambda x_Demod_199:A.(eq A (add y (mult (inv y) one)) x_Demod_199)) 
  (eq_ind A (add y (inv y)) 
  (\lambda x_SupR_268:A.(eq A (add y (mult (inv y) one)) (mult x_SupR_268 (add y one)))) (H2 y (inv y) one) one (H6 y)) (add y one) 
  (eq_ind A (mult (add y one) one) 
  (\lambda x_SupR_271:A.(eq A x_SupR_271 (mult one (add y one)))) (H1 (add y one) one) (add y one) (H5 (add y one)))) (inv y) (H5 (inv y))) one (H6 y))) zero (H5 zero))) zero (H4 zero))) x 
  (eq_ind A (add x zero) 
  (\lambda x_SupR_299:A.(eq A x_SupR_299 (add zero x))) (H x zero) x (H4 x))) y (H4 y)) (add y (add x (mult y z))) 
  (sym_eq\subst[A \Assign A ; x \Assign (add y (add x (mult y z))) ; y \Assign y] 
  (eq_ind_r A (add zero y) 
  (\lambda x_SupR_826:A.(eq A (add y (add x (mult y z))) x_SupR_826)) 
  (eq_ind_r A (add zero (mult (add y zero) y)) 
  (\lambda x_Demod_553:A.(eq A (add y (add x (mult y z))) x_Demod_553)) 
  (eq_ind A (add (add y (add x (mult y z))) zero) 
  (\lambda x_Demod_540:A.(eq A x_Demod_540 (add (add x (mult y z)) (mult (add y (add x (mult y z))) y)))) 
  (eq_ind_r A (mult zero (add x (mult y z))) 
  (\lambda x_Demod_526:A.(eq A (add (add y (add x (mult y z))) x_Demod_526) (add (add x (mult y z)) (mult (add y (add x (mult y z))) y)))) 
  (eq_ind_r A (mult (add y (add x (mult y z))) (add (add y (add x (mult y z))) (add x (mult y z)))) 
  (\lambda x_SupR_606:A.(eq A (add (add y (add x (mult y z))) (mult zero (add x (mult y z)))) x_SupR_606)) 
  (eq_ind A (add (add y (add x (mult y z))) zero) 
  (\lambda x_SupR_296:A.(eq A (add (add y (add x (mult y z))) (mult zero (add x (mult y z)))) (mult x_SupR_296 (add (add y (add x (mult y z))) (add x (mult y z)))))) 
  (H2 (add y (add x (mult y z))) zero (add x (mult y z))) (add y (add x (mult y z))) (H4 (add y (add x (mult y z))))) (add (add x (mult y z)) (mult (add y (add x (mult y z))) y)) 
  (eq_ind A (add (add x (mult y z)) y) 
  (\lambda x_SupR_357:A.(eq A (add (add x (mult y z)) (mult (add y (add x (mult y z))) y)) (mult x_SupR_357 (add (add y (add x (mult y z))) (add x (mult y z)))))) (eq_ind A (mult (add (add y (add x (mult y z))) (add x (mult y z))) (add (add x (mult y z)) y)) 
  (\lambda x_SupR_310:A.(eq A (add (add x (mult y z)) (mult (add y (add x (mult y z))) y)) x_SupR_310)) (eq_ind A (add (add x (mult y z)) (add y (add x (mult y z)))) 
  (\lambda x_SupR_302:A.(eq A (add (add x (mult y z)) (mult (add y (add x (mult y z))) y)) (mult x_SupR_302 (add (add x (mult y z)) y)))) (H2 (add x (mult y z)) (add y (add x (mult y z))) y) (add (add y (add x (mult y z))) (add x (mult y z))) (H (add x (mult y z)) (add y (add x (mult y z))))) (mult (add (add x (mult y z)) y) (add (add y (add x (mult y z))) (add x (mult y z)))) (H1 (add (add y (add x (mult y z))) (add x (mult y z))) (add (add x (mult y z)) y))) (add y (add x (mult y z))) (H (add x (mult y z)) y))) zero (eq_ind A (mult zero one) 
  (\lambda x_Demod_507:A.(eq A x_Demod_507 (mult zero (add x (mult y z))))) 
  (eq_ind_r A (add (add x (mult y z)) one) 
  (\lambda x_Demod_506:A.(eq A (mult zero x_Demod_506) (mult zero (add x (mult y z))))) 
  (eq_ind_r A (inv zero) 
  (\lambda x_SupR_785:A.(eq A (mult zero (add (add x (mult y z)) x_SupR_785)) (mult zero (add x (mult y z))))) 
  (eq_ind A (add (mult zero (add x (mult y z))) zero) 
  (\lambda x_Demod_223:A.(eq A (mult zero (add (add x (mult y z)) (inv zero))) x_Demod_223)) 
  (eq_ind A (mult zero (inv zero)) 
  (\lambda x_SupR_337:A.(eq A (mult zero (add (add x (mult y z)) (inv zero))) (add (mult zero (add x (mult y z))) x_SupR_337))) (H3 zero (add x (mult y z)) (inv zero)) zero (H7 zero)) (mult zero (add x (mult y z))) (H4 (mult zero (add x (mult y z))))) one 
  (eq_ind A (add (inv zero) zero) 
  (\lambda x_SupR_463:A.(eq A one x_SupR_463)) 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_SupR_298:A.(eq A x_SupR_298 (add (inv zero) zero))) (H zero (inv zero)) one (H6 zero)) (inv zero) (H4 (inv zero)))) one 
  (eq_ind A (add (add x (mult y z)) (inv (add x (mult y z)))) 
  (\lambda x_Demod_268:A.(eq A x_Demod_268 (add (add x (mult y z)) one))) 
  (eq_ind A (mult (inv (add x (mult y z))) one) 
  (\lambda x_SupR_396:A.(eq A (add (add x (mult y z)) x_SupR_396) (add (add x (mult y z)) one))) 
  (eq_ind_r A (mult one (add (add x (mult y z)) one)) 
  (\lambda x_Demod_199:A.(eq A (add (add x (mult y z)) (mult (inv (add x (mult y z))) one)) x_Demod_199)) 
  (eq_ind A (add (add x (mult y z)) (inv (add x (mult y z)))) 
  (\lambda x_SupR_268:A.(eq A (add (add x (mult y z)) (mult (inv (add x (mult y z))) one)) (mult x_SupR_268 (add (add x (mult y z)) one)))) (H2 (add x (mult y z)) (inv (add x (mult y z))) one) one (H6 (add x (mult y z)))) (add (add x (mult y z)) one) (eq_ind A (mult (add (add x (mult y z)) one) one) 
  (\lambda x_SupR_271:A.(eq A x_SupR_271 (mult one (add (add x (mult y z)) one)))) (H1 (add (add x (mult y z)) one) one) (add (add x (mult y z)) one) (H5 (add (add x (mult y z)) one)))) (inv (add x (mult y z))) (H5 (inv (add x (mult y z))))) one (H6 (add x (mult y z))))) zero (H5 zero))) (add y (add x (mult y z))) (H4 (add y (add x (mult y z))))) (add zero y) 
  (eq_ind A (add y zero) 
  (\lambda x_Demod_543:A.(eq A (add zero x_Demod_543) (add zero (mult (add y zero) y)))) 
  (eq_ind_r A (mult zero zero) 
  (\lambda x_Demod_524:A.(eq A (add zero (add y x_Demod_524)) (add zero (mult (add y zero) y)))) 
  (eq_ind_r A (mult y (add y zero)) 
  (\lambda x_SupR_628:A.(eq A (add zero x_SupR_628) (add zero (mult (add y zero) y)))) 
  (eq_ind_r A (mult (add zero (add y zero)) (add zero y)) 
  (\lambda x_Demod_195:A.(eq A (add zero (mult y (add y zero))) x_Demod_195)) 
  (eq_ind_r A (mult (add zero y) (add zero (add y zero))) 
  (\lambda x_SupR_272:A.(eq A x_SupR_272 (mult (add zero (add y zero)) (add zero y)))) (H1 (add zero y) (add zero (add y zero))) (add zero (mult y (add y zero))) (H2 zero y (add y zero))) (add zero (mult (add y zero) y)) (H2 zero (add y zero) y)) (add y (mult zero zero)) 
  (eq_ind A (add y zero) 
  (\lambda x_SupR_296:A.(eq A (add y (mult zero zero)) (mult x_SupR_296 (add y zero)))) (H2 y zero zero) y (H4 y))) zero 
  (eq_ind A (mult zero one) 
  (\lambda x_Demod_507:A.(eq A x_Demod_507 (mult zero zero))) 
  (eq_ind_r A (add zero one) 
  (\lambda x_Demod_506:A.(eq A (mult zero x_Demod_506) (mult zero zero))) 
  (eq_ind_r A (inv zero) 
  (\lambda x_SupR_785:A.(eq A (mult zero (add zero x_SupR_785)) (mult zero zero))) 
  (eq_ind A (add (mult zero zero) zero) 
  (\lambda x_Demod_223:A.(eq A (mult zero (add zero (inv zero))) x_Demod_223)) 
  (eq_ind A (mult zero (inv zero)) 
  (\lambda x_SupR_337:A.(eq A (mult zero (add zero (inv zero))) (add (mult zero zero) x_SupR_337))) (H3 zero zero (inv zero)) zero (H7 zero)) (mult zero zero) (H4 (mult zero zero))) one 
  (eq_ind A (add (inv zero) zero) 
  (\lambda x_SupR_463:A.(eq A one x_SupR_463)) 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_SupR_298:A.(eq A x_SupR_298 (add (inv zero) zero))) (H zero (inv zero)) one (H6 zero)) (inv zero) (H4 (inv zero)))) one 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_Demod_268:A.(eq A x_Demod_268 (add zero one))) 
  (eq_ind A (mult (inv zero) one) (\lambda x_SupR_396:A.(eq A (add zero x_SupR_396) (add zero one))) 
  (eq_ind_r A (mult one (add zero one)) 
  (\lambda x_Demod_199:A.(eq A (add zero (mult (inv zero) one)) x_Demod_199)) 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_SupR_268:A.(eq A (add zero (mult (inv zero) one)) (mult x_SupR_268 (add zero one)))) (H2 zero (inv zero) one) one (H6 zero)) (add zero one) 
  (eq_ind A (mult (add zero one) one) 
  (\lambda x_SupR_271:A.(eq A x_SupR_271 (mult one (add zero one)))) (H1 (add zero one) one) (add zero one) (H5 (add zero one)))) (inv zero) (H5 (inv zero))) one (H6 zero))) zero (H5 zero))) y (H4 y))) y 
  (eq_ind A (add y zero) 
  (\lambda x_SupR_299:A.(eq A x_SupR_299 (add zero y))) (H y zero) y (H4 y))))) (add x y) 
  (sym_eq\subst[A \Assign A ; x \Assign (add x y) ; y \Assign x] 
  (eq_ind_r A (add zero x) 
  (\lambda x_SupR_826:A.(eq A (add x y) x_SupR_826)) 
  (eq_ind_r A (add zero (mult (add x zero) x)) 
  (\lambda x_Demod_553:A.(eq A (add x y) x_Demod_553)) 
  (eq_ind A (add (add x y) zero) 
  (\lambda x_Demod_540:A.(eq A x_Demod_540 (add y (mult (add x y) x)))) 
  (eq_ind_r A (mult zero y) 
  (\lambda x_Demod_526:A.(eq A (add (add x y) x_Demod_526) (add y (mult (add x y) x)))) 
  (eq_ind_r A (mult (add x y) (add (add x y) y)) 
  (\lambda x_SupR_606:A.(eq A (add (add x y) (mult zero y)) x_SupR_606)) 
  (eq_ind A (add (add x y) zero) 
  (\lambda x_SupR_296:A.(eq A (add (add x y) (mult zero y)) (mult x_SupR_296 (add (add x y) y)))) (H2 (add x y) zero y) (add x y) (H4 (add x y))) (add y (mult (add x y) x)) 
  (eq_ind A (add y x) 
  (\lambda x_SupR_357:A.(eq A (add y (mult (add x y) x)) (mult x_SupR_357 (add (add x y) y)))) 
  (eq_ind A (mult (add (add x y) y) (add y x)) 
  (\lambda x_SupR_310:A.(eq A (add y (mult (add x y) x)) x_SupR_310)) 
  (eq_ind A (add y (add x y)) 
  (\lambda x_SupR_302:A.(eq A (add y (mult (add x y) x)) (mult x_SupR_302 (add y x)))) (H2 y (add x y) x) (add (add x y) y) (H y (add x y))) (mult (add y x) (add (add x y) y)) (H1 (add (add x y) y) (add y x))) (add x y) (H y x))) zero 
  (eq_ind A (mult zero one) 
  (\lambda x_Demod_507:A.(eq A x_Demod_507 (mult zero y))) 
  (eq_ind_r A (add y one) 
  (\lambda x_Demod_506:A.(eq A (mult zero x_Demod_506) (mult zero y))) 
  (eq_ind_r A (inv zero) 
  (\lambda x_SupR_785:A.(eq A (mult zero (add y x_SupR_785)) (mult zero y))) 
  (eq_ind A (add (mult zero y) zero) 
  (\lambda x_Demod_223:A.(eq A (mult zero (add y (inv zero))) x_Demod_223)) 
  (eq_ind A (mult zero (inv zero)) 
  (\lambda x_SupR_337:A.(eq A (mult zero (add y (inv zero))) (add (mult zero y) x_SupR_337))) (H3 zero y (inv zero)) zero (H7 zero)) (mult zero y) (H4 (mult zero y))) one 
  (eq_ind A (add (inv zero) zero) 
  (\lambda x_SupR_463:A.(eq A one x_SupR_463)) 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_SupR_298:A.(eq A x_SupR_298 (add (inv zero) zero))) (H zero (inv zero)) one (H6 zero)) (inv zero) (H4 (inv zero)))) one 
  (eq_ind A (add y (inv y)) 
  (\lambda x_Demod_268:A.(eq A x_Demod_268 (add y one))) 
  (eq_ind A (mult (inv y) one) 
  (\lambda x_SupR_396:A.(eq A (add y x_SupR_396) (add y one))) 
  (eq_ind_r A (mult one (add y one)) 
  (\lambda x_Demod_199:A.(eq A (add y (mult (inv y) one)) x_Demod_199)) 
  (eq_ind A (add y (inv y)) 
  (\lambda x_SupR_268:A.(eq A (add y (mult (inv y) one)) (mult x_SupR_268 (add y one)))) (H2 y (inv y) one) one (H6 y)) (add y one) 
  (eq_ind A (mult (add y one) one) 
  (\lambda x_SupR_271:A.(eq A x_SupR_271 (mult one (add y one)))) (H1 (add y one) one) (add y one) (H5 (add y one)))) (inv y) (H5 (inv y))) one (H6 y))) zero (H5 zero))) (add x y) (H4 (add x y))) (add zero x) 
  (eq_ind A (add x zero) 
  (\lambda x_Demod_543:A.(eq A (add zero x_Demod_543) (add zero (mult (add x zero) x)))) 
  (eq_ind_r A (mult zero zero) 
  (\lambda x_Demod_524:A.(eq A (add zero (add x x_Demod_524)) (add zero (mult (add x zero) x)))) 
  (eq_ind_r A (mult x (add x zero)) 
  (\lambda x_SupR_628:A.(eq A (add zero x_SupR_628) (add zero (mult (add x zero) x)))) 
  (eq_ind_r A (mult (add zero (add x zero)) (add zero x)) 
  (\lambda x_Demod_195:A.(eq A (add zero (mult x (add x zero))) x_Demod_195)) 
  (eq_ind_r A (mult (add zero x) (add zero (add x zero))) 
  (\lambda x_SupR_272:A.(eq A x_SupR_272 (mult (add zero (add x zero)) (add zero x)))) (H1 (add zero x) (add zero (add x zero))) (add zero (mult x (add x zero))) (H2 zero x (add x zero))) (add zero (mult (add x zero) x)) (H2 zero (add x zero) x)) (add x (mult zero zero)) 
  (eq_ind A (add x zero) 
  (\lambda x_SupR_296:A.(eq A (add x (mult zero zero)) (mult x_SupR_296 (add x zero)))) (H2 x zero zero) x (H4 x))) zero 
  (eq_ind A (mult zero one) 
  (\lambda x_Demod_507:A.(eq A x_Demod_507 (mult zero zero))) 
  (eq_ind_r A (add zero one) 
  (\lambda x_Demod_506:A.(eq A (mult zero x_Demod_506) (mult zero zero))) 
  (eq_ind_r A (inv zero) 
  (\lambda x_SupR_785:A.(eq A (mult zero (add zero x_SupR_785)) (mult zero zero))) 
  (eq_ind A (add (mult zero zero) zero) 
  (\lambda x_Demod_223:A.(eq A (mult zero (add zero (inv zero))) x_Demod_223)) 
  (eq_ind A (mult zero (inv zero)) 
  (\lambda x_SupR_337:A.(eq A (mult zero (add zero (inv zero))) (add (mult zero zero) x_SupR_337))) (H3 zero zero (inv zero)) zero (H7 zero)) (mult zero zero) (H4 (mult zero zero))) one 
  (eq_ind A (add (inv zero) zero) 
  (\lambda x_SupR_463:A.(eq A one x_SupR_463)) 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_SupR_298:A.(eq A x_SupR_298 (add (inv zero) zero))) (H zero (inv zero)) one (H6 zero)) (inv zero) (H4 (inv zero)))) one 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_Demod_268:A.(eq A x_Demod_268 (add zero one))) 
  (eq_ind A (mult (inv zero) one) 
  (\lambda x_SupR_396:A.(eq A (add zero x_SupR_396) (add zero one))) 
  (eq_ind_r A (mult one (add zero one)) 
  (\lambda x_Demod_199:A.(eq A (add zero (mult (inv zero) one)) x_Demod_199)) 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_SupR_268:A.(eq A (add zero (mult (inv zero) one)) (mult x_SupR_268 (add zero one)))) (H2 zero (inv zero) one) one (H6 zero)) (add zero one) 
  (eq_ind A (mult (add zero one) one) 
  (\lambda x_SupR_271:A.(eq A x_SupR_271 (mult one (add zero one)))) (H1 (add zero one) one) (add zero one) (H5 (add zero one)))) (inv zero) (H5 (inv zero))) one (H6 zero))) zero (H5 zero))) x (H4 x))) x 
  (eq_ind A (add x zero) 
  (\lambda x_SupR_299:A.(eq A x_SupR_299 (add zero x))) (H x zero) x (H4 x))))) (add (add x (mult y z)) y) 
  (sym_eq\subst[A \Assign A ; x \Assign (add (add x (mult y z)) y) ; y \Assign (add y (add x (mult y z)))] (H (add x (mult y z)) y)))
). qed.

STOP

auto paramodulation.

qed.

theorem bool4:
  \forall A:Set.
  \forall one:A.
  \forall zero:A.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall inv: A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall c2:(\forall x,y:A.(mult x y) = (mult y x)). 
  \forall d1: (\forall x,y,z:A.
              (add x (mult y z)) = (mult (add x y) (add x z))).
  \forall d2: (\forall x,y,z:A.
              (mult x (add y z)) = (add (mult x y) (mult x z))).  
  \forall i1: (\forall x:A. (add x zero) = x).
  \forall i2: (\forall x:A. (mult x one) = x).   
  \forall inv1: (\forall x:A. (add x (inv x)) = one).  
  \forall inv2: (\forall x:A. (mult x (inv x)) = zero). 
  \forall x,y,z:A.
    (add x y) = (add (add x (mult y z)) y).
intros.
exact 
((eq_ind A (add y (add x (mult y z))) 
 (\lambda x_DemodGoal_193:A.(eq A (add x y) x_DemodGoal_193)) 
 (eq_ind A x 
 (\lambda x_DemodGoal_893:A.(eq A x_DemodGoal_893 (add y (add x (mult y z))))) 
  (eq_ind A y (\lambda x_DemodGoal_894:A.(eq A x x_DemodGoal_894)) 
  (eq_ind A (add y zero) (\lambda x_Demod_554:A.(eq A x x_Demod_554)) 
  (eq_ind_r A (add zero x) (\lambda x_SupR_809:A.(eq A x_SupR_809 (add y zero))) 
  (eq_ind_r A (add y (mult (add zero y) zero)) 
  (\lambda x_Demod_553:A.(eq A (add zero x) x_Demod_553)) 
  (eq_ind A (add (add zero x) zero) 
  (\lambda x_Demod_540:A.(eq A x_Demod_540 (add x (mult (add zero x) zero)))) 
  (eq_ind_r A (mult zero x) 
  (\lambda x_Demod_526:A.(eq A (add (add zero x) x_Demod_526) (add x (mult (add zero x) zero)))) 
  (eq_ind_r A (mult (add zero x) (add (add zero x) x)) 
  (\lambda x_SupR_606:A.(eq A (add (add zero x) (mult zero x)) x_SupR_606)) 
  (eq_ind A (add (add zero x) zero) 
  (\lambda x_SupR_296:A.(eq A (add (add zero x) (mult zero x)) (mult x_SupR_296 (add (add zero x) x)))) 
  (H2 (add zero x) zero x) (add zero x) (H4 (add zero x))) (add x (mult (add zero x) zero)) 
  (eq_ind A (add x zero) 
  (\lambda x_SupR_357:A.(eq A (add x (mult (add zero x) zero)) (mult x_SupR_357 (add (add zero x) x)))) 
  (eq_ind A (mult (add (add zero x) x) (add x zero)) 
  (\lambda x_SupR_310:A.(eq A (add x (mult (add zero x) zero)) x_SupR_310)) 
  (eq_ind A (add x (add zero x)) 
  (\lambda x_SupR_302:A.(eq A (add x (mult (add zero x) zero)) (mult x_SupR_302 (add x zero)))) 
  (H2 x (add zero x) zero) (add (add zero x) x) (H x (add zero x))) (mult (add x zero) (add (add zero x) x)) (H1 (add (add zero x) x) (add x zero))) (add zero x) (H x zero))) zero 
  (eq_ind A (mult zero one) 
  (\lambda x_Demod_507:A.(eq A x_Demod_507 (mult zero x))) 
  (eq_ind_r A (add x one) 
  (\lambda x_Demod_506:A.(eq A (mult zero x_Demod_506) (mult zero x))) 
  (eq_ind_r A (inv zero) 
  (\lambda x_SupR_785:A.(eq A (mult zero (add x x_SupR_785)) (mult zero x))) 
  (eq_ind A (add (mult zero x) zero) 
  (\lambda x_Demod_223:A.(eq A (mult zero (add x (inv zero))) x_Demod_223)) 
  (eq_ind A (mult zero (inv zero)) 
  (\lambda x_SupR_337:A.(eq A (mult zero (add x (inv zero))) (add (mult zero x) x_SupR_337))) 
  (H3 zero x (inv zero)) zero (H7 zero)) (mult zero x) (H4 (mult zero x))) one 
  (eq_ind A (add (inv zero) zero) 
  (\lambda x_SupR_463:A.(eq A one x_SupR_463)) 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_SupR_298:A.(eq A x_SupR_298 (add (inv zero) zero))) (H zero (inv zero)) one (H6 zero)) (inv zero) (H4 (inv zero)))) one 
  (eq_ind A (add x (inv x)) 
  (\lambda x_Demod_268:A.(eq A x_Demod_268 (add x one))) 
  (eq_ind A (mult (inv x) one) 
  (\lambda x_SupR_396:A.(eq A (add x x_SupR_396) (add x one))) 
  (eq_ind_r A (mult one (add x one)) 
  (\lambda x_Demod_199:A.(eq A (add x (mult (inv x) one)) x_Demod_199)) 
  (eq_ind A (add x (inv x)) 
  (\lambda x_SupR_268:A.(eq A (add x (mult (inv x) one)) (mult x_SupR_268 (add x one)))) (H2 x (inv x) one) one (H6 x)) (add x one) 
  (eq_ind A (mult (add x one) one) 
  (\lambda x_SupR_271:A.(eq A x_SupR_271 (mult one (add x one)))) 
  (H1 (add x one) one) (add x one) (H5 (add x one)))) (inv x) (H5 (inv x))) one (H6 x))) zero (H5 zero))) (add zero x) (H4 (add zero x))) (add y zero) 
  (eq_ind A (add zero zero) 
  (\lambda x_Demod_543:A.(eq A (add y x_Demod_543) (add y (mult (add zero y) zero)))) 
  (eq_ind_r A (mult zero y) 
  (\lambda x_Demod_524:A.(eq A (add y (add zero x_Demod_524)) (add y (mult (add zero y) zero)))) 
  (eq_ind_r A (mult zero (add zero y)) 
  (\lambda x_SupR_628:A.(eq A (add y x_SupR_628) (add y (mult (add zero y) zero)))) 
  (eq_ind_r A (mult (add y (add zero y)) (add y zero)) 
  (\lambda x_Demod_195:A.(eq A (add y (mult zero (add zero y))) x_Demod_195)) 
  (eq_ind_r A (mult (add y zero) (add y (add zero y))) 
  (\lambda x_SupR_272:A.(eq A x_SupR_272 (mult (add y (add zero y)) (add y zero)))) (H1 (add y zero) (add y (add zero y))) (add y (mult zero (add zero y))) (H2 y zero (add zero y))) (add y (mult (add zero y) zero)) (H2 y (add zero y) zero)) (add zero (mult zero y)) 
  (eq_ind A (add zero zero) 
  (\lambda x_SupR_296:A.(eq A (add zero (mult zero y)) (mult x_SupR_296 (add zero y)))) (H2 zero zero y) zero (H4 zero))) zero 
  (eq_ind A (mult zero one) 
  (\lambda x_Demod_507:A.(eq A x_Demod_507 (mult zero y))) 
  (eq_ind_r A (add y one) 
  (\lambda x_Demod_506:A.(eq A (mult zero x_Demod_506) (mult zero y))) 
  (eq_ind_r A (inv zero) 
  (\lambda x_SupR_785:A.(eq A (mult zero (add y x_SupR_785)) (mult zero y))) 
  (eq_ind A (add (mult zero y) zero) 
  (\lambda x_Demod_223:A.(eq A (mult zero (add y (inv zero))) x_Demod_223)) 
  (eq_ind A (mult zero (inv zero)) 
  (\lambda x_SupR_337:A.(eq A (mult zero (add y (inv zero))) (add (mult zero y) x_SupR_337))) (H3 zero y (inv zero)) zero (H7 zero)) (mult zero y) (H4 (mult zero y))) one 
  (eq_ind A (add (inv zero) zero) 
  (\lambda x_SupR_463:A.(eq A one x_SupR_463)) (eq_ind A (add zero (inv zero)) 
  (\lambda x_SupR_298:A.(eq A x_SupR_298 (add (inv zero) zero))) (H zero (inv zero)) one (H6 zero)) (inv zero) (H4 (inv zero)))) one 
  (eq_ind A (add y (inv y)) 
  (\lambda x_Demod_268:A.(eq A x_Demod_268 (add y one))) 
  (eq_ind A (mult (inv y) one) 
  (\lambda x_SupR_396:A.(eq A (add y x_SupR_396) (add y one))) 
  (eq_ind_r A (mult one (add y one)) 
  (\lambda x_Demod_199:A.(eq A (add y (mult (inv y) one)) x_Demod_199)) 
  (eq_ind A (add y (inv y)) 
  (\lambda x_SupR_268:A.(eq A (add y (mult (inv y) one)) (mult x_SupR_268 (add y one)))) (H2 y (inv y) one) one (H6 y)) (add y one) 
  (eq_ind A (mult (add y one) one) 
  (\lambda x_SupR_271:A.(eq A x_SupR_271 (mult one (add y one)))) (H1 (add y one) one) (add y one) (H5 (add y one)))) (inv y) (H5 (inv y))) one (H6 y))) zero (H5 zero))) zero (H4 zero))) x 
  (eq_ind A (add x zero) 
  (\lambda x_SupR_299:A.(eq A x_SupR_299 (add zero x))) (H x zero) x (H4 x))) y (H4 y)) (add y (add x (mult y z))) 
  (sym_eq\subst[A \Assign A ; x \Assign (add y (add x (mult y z))) ; y \Assign y] 
  (eq_ind_r A (add zero y) 
  (\lambda x_SupR_826:A.(eq A (add y (add x (mult y z))) x_SupR_826)) 
  (eq_ind_r A (add zero (mult (add y zero) y)) 
  (\lambda x_Demod_553:A.(eq A (add y (add x (mult y z))) x_Demod_553)) 
  (eq_ind A (add (add y (add x (mult y z))) zero) 
  (\lambda x_Demod_540:A.(eq A x_Demod_540 (add (add x (mult y z)) (mult (add y (add x (mult y z))) y)))) 
  (eq_ind_r A (mult zero (add x (mult y z))) 
  (\lambda x_Demod_526:A.(eq A (add (add y (add x (mult y z))) x_Demod_526) (add (add x (mult y z)) (mult (add y (add x (mult y z))) y)))) 
  (eq_ind_r A (mult (add y (add x (mult y z))) (add (add y (add x (mult y z))) (add x (mult y z)))) 
  (\lambda x_SupR_606:A.(eq A (add (add y (add x (mult y z))) (mult zero (add x (mult y z)))) x_SupR_606)) 
  (eq_ind A (add (add y (add x (mult y z))) zero) 
  (\lambda x_SupR_296:A.(eq A (add (add y (add x (mult y z))) (mult zero (add x (mult y z)))) (mult x_SupR_296 (add (add y (add x (mult y z))) (add x (mult y z)))))) 
  (H2 (add y (add x (mult y z))) zero (add x (mult y z))) (add y (add x (mult y z))) (H4 (add y (add x (mult y z))))) (add (add x (mult y z)) (mult (add y (add x (mult y z))) y)) 
  (eq_ind A (add (add x (mult y z)) y) 
  (\lambda x_SupR_357:A.(eq A (add (add x (mult y z)) (mult (add y (add x (mult y z))) y)) (mult x_SupR_357 (add (add y (add x (mult y z))) (add x (mult y z)))))) (eq_ind A (mult (add (add y (add x (mult y z))) (add x (mult y z))) (add (add x (mult y z)) y)) 
  (\lambda x_SupR_310:A.(eq A (add (add x (mult y z)) (mult (add y (add x (mult y z))) y)) x_SupR_310)) (eq_ind A (add (add x (mult y z)) (add y (add x (mult y z)))) 
  (\lambda x_SupR_302:A.(eq A (add (add x (mult y z)) (mult (add y (add x (mult y z))) y)) (mult x_SupR_302 (add (add x (mult y z)) y)))) (H2 (add x (mult y z)) (add y (add x (mult y z))) y) (add (add y (add x (mult y z))) (add x (mult y z))) (H (add x (mult y z)) (add y (add x (mult y z))))) (mult (add (add x (mult y z)) y) (add (add y (add x (mult y z))) (add x (mult y z)))) (H1 (add (add y (add x (mult y z))) (add x (mult y z))) (add (add x (mult y z)) y))) (add y (add x (mult y z))) (H (add x (mult y z)) y))) zero (eq_ind A (mult zero one) 
  (\lambda x_Demod_507:A.(eq A x_Demod_507 (mult zero (add x (mult y z))))) 
  (eq_ind_r A (add (add x (mult y z)) one) 
  (\lambda x_Demod_506:A.(eq A (mult zero x_Demod_506) (mult zero (add x (mult y z))))) 
  (eq_ind_r A (inv zero) 
  (\lambda x_SupR_785:A.(eq A (mult zero (add (add x (mult y z)) x_SupR_785)) (mult zero (add x (mult y z))))) 
  (eq_ind A (add (mult zero (add x (mult y z))) zero) 
  (\lambda x_Demod_223:A.(eq A (mult zero (add (add x (mult y z)) (inv zero))) x_Demod_223)) 
  (eq_ind A (mult zero (inv zero)) 
  (\lambda x_SupR_337:A.(eq A (mult zero (add (add x (mult y z)) (inv zero))) (add (mult zero (add x (mult y z))) x_SupR_337))) (H3 zero (add x (mult y z)) (inv zero)) zero (H7 zero)) (mult zero (add x (mult y z))) (H4 (mult zero (add x (mult y z))))) one 
  (eq_ind A (add (inv zero) zero) 
  (\lambda x_SupR_463:A.(eq A one x_SupR_463)) 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_SupR_298:A.(eq A x_SupR_298 (add (inv zero) zero))) (H zero (inv zero)) one (H6 zero)) (inv zero) (H4 (inv zero)))) one 
  (eq_ind A (add (add x (mult y z)) (inv (add x (mult y z)))) 
  (\lambda x_Demod_268:A.(eq A x_Demod_268 (add (add x (mult y z)) one))) 
  (eq_ind A (mult (inv (add x (mult y z))) one) 
  (\lambda x_SupR_396:A.(eq A (add (add x (mult y z)) x_SupR_396) (add (add x (mult y z)) one))) 
  (eq_ind_r A (mult one (add (add x (mult y z)) one)) 
  (\lambda x_Demod_199:A.(eq A (add (add x (mult y z)) (mult (inv (add x (mult y z))) one)) x_Demod_199)) 
  (eq_ind A (add (add x (mult y z)) (inv (add x (mult y z)))) 
  (\lambda x_SupR_268:A.(eq A (add (add x (mult y z)) (mult (inv (add x (mult y z))) one)) (mult x_SupR_268 (add (add x (mult y z)) one)))) (H2 (add x (mult y z)) (inv (add x (mult y z))) one) one (H6 (add x (mult y z)))) (add (add x (mult y z)) one) (eq_ind A (mult (add (add x (mult y z)) one) one) 
  (\lambda x_SupR_271:A.(eq A x_SupR_271 (mult one (add (add x (mult y z)) one)))) (H1 (add (add x (mult y z)) one) one) (add (add x (mult y z)) one) (H5 (add (add x (mult y z)) one)))) (inv (add x (mult y z))) (H5 (inv (add x (mult y z))))) one (H6 (add x (mult y z))))) zero (H5 zero))) (add y (add x (mult y z))) (H4 (add y (add x (mult y z))))) (add zero y) 
  (eq_ind A (add y zero) 
  (\lambda x_Demod_543:A.(eq A (add zero x_Demod_543) (add zero (mult (add y zero) y)))) 
  (eq_ind_r A (mult zero zero) 
  (\lambda x_Demod_524:A.(eq A (add zero (add y x_Demod_524)) (add zero (mult (add y zero) y)))) 
  (eq_ind_r A (mult y (add y zero)) 
  (\lambda x_SupR_628:A.(eq A (add zero x_SupR_628) (add zero (mult (add y zero) y)))) 
  (eq_ind_r A (mult (add zero (add y zero)) (add zero y)) 
  (\lambda x_Demod_195:A.(eq A (add zero (mult y (add y zero))) x_Demod_195)) 
  (eq_ind_r A (mult (add zero y) (add zero (add y zero))) 
  (\lambda x_SupR_272:A.(eq A x_SupR_272 (mult (add zero (add y zero)) (add zero y)))) (H1 (add zero y) (add zero (add y zero))) (add zero (mult y (add y zero))) (H2 zero y (add y zero))) (add zero (mult (add y zero) y)) (H2 zero (add y zero) y)) (add y (mult zero zero)) 
  (eq_ind A (add y zero) 
  (\lambda x_SupR_296:A.(eq A (add y (mult zero zero)) (mult x_SupR_296 (add y zero)))) (H2 y zero zero) y (H4 y))) zero 
  (eq_ind A (mult zero one) 
  (\lambda x_Demod_507:A.(eq A x_Demod_507 (mult zero zero))) 
  (eq_ind_r A (add zero one) 
  (\lambda x_Demod_506:A.(eq A (mult zero x_Demod_506) (mult zero zero))) 
  (eq_ind_r A (inv zero) 
  (\lambda x_SupR_785:A.(eq A (mult zero (add zero x_SupR_785)) (mult zero zero))) 
  (eq_ind A (add (mult zero zero) zero) 
  (\lambda x_Demod_223:A.(eq A (mult zero (add zero (inv zero))) x_Demod_223)) 
  (eq_ind A (mult zero (inv zero)) 
  (\lambda x_SupR_337:A.(eq A (mult zero (add zero (inv zero))) (add (mult zero zero) x_SupR_337))) (H3 zero zero (inv zero)) zero (H7 zero)) (mult zero zero) (H4 (mult zero zero))) one 
  (eq_ind A (add (inv zero) zero) 
  (\lambda x_SupR_463:A.(eq A one x_SupR_463)) 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_SupR_298:A.(eq A x_SupR_298 (add (inv zero) zero))) (H zero (inv zero)) one (H6 zero)) (inv zero) (H4 (inv zero)))) one 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_Demod_268:A.(eq A x_Demod_268 (add zero one))) 
  (eq_ind A (mult (inv zero) one) (\lambda x_SupR_396:A.(eq A (add zero x_SupR_396) (add zero one))) 
  (eq_ind_r A (mult one (add zero one)) 
  (\lambda x_Demod_199:A.(eq A (add zero (mult (inv zero) one)) x_Demod_199)) 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_SupR_268:A.(eq A (add zero (mult (inv zero) one)) (mult x_SupR_268 (add zero one)))) (H2 zero (inv zero) one) one (H6 zero)) (add zero one) 
  (eq_ind A (mult (add zero one) one) 
  (\lambda x_SupR_271:A.(eq A x_SupR_271 (mult one (add zero one)))) (H1 (add zero one) one) (add zero one) (H5 (add zero one)))) (inv zero) (H5 (inv zero))) one (H6 zero))) zero (H5 zero))) y (H4 y))) y 
  (eq_ind A (add y zero) 
  (\lambda x_SupR_299:A.(eq A x_SupR_299 (add zero y))) (H y zero) y (H4 y))))) (add x y) 
  (sym_eq\subst[A \Assign A ; x \Assign (add x y) ; y \Assign x] 
  (eq_ind_r A (add zero x) 
  (\lambda x_SupR_826:A.(eq A (add x y) x_SupR_826)) 
  (eq_ind_r A (add zero (mult (add x zero) x)) 
  (\lambda x_Demod_553:A.(eq A (add x y) x_Demod_553)) 
  (eq_ind A (add (add x y) zero) 
  (\lambda x_Demod_540:A.(eq A x_Demod_540 (add y (mult (add x y) x)))) 
  (eq_ind_r A (mult zero y) 
  (\lambda x_Demod_526:A.(eq A (add (add x y) x_Demod_526) (add y (mult (add x y) x)))) 
  (eq_ind_r A (mult (add x y) (add (add x y) y)) 
  (\lambda x_SupR_606:A.(eq A (add (add x y) (mult zero y)) x_SupR_606)) 
  (eq_ind A (add (add x y) zero) 
  (\lambda x_SupR_296:A.(eq A (add (add x y) (mult zero y)) (mult x_SupR_296 (add (add x y) y)))) (H2 (add x y) zero y) (add x y) (H4 (add x y))) (add y (mult (add x y) x)) 
  (eq_ind A (add y x) 
  (\lambda x_SupR_357:A.(eq A (add y (mult (add x y) x)) (mult x_SupR_357 (add (add x y) y)))) 
  (eq_ind A (mult (add (add x y) y) (add y x)) 
  (\lambda x_SupR_310:A.(eq A (add y (mult (add x y) x)) x_SupR_310)) 
  (eq_ind A (add y (add x y)) 
  (\lambda x_SupR_302:A.(eq A (add y (mult (add x y) x)) (mult x_SupR_302 (add y x)))) (H2 y (add x y) x) (add (add x y) y) (H y (add x y))) (mult (add y x) (add (add x y) y)) (H1 (add (add x y) y) (add y x))) (add x y) (H y x))) zero 
  (eq_ind A (mult zero one) 
  (\lambda x_Demod_507:A.(eq A x_Demod_507 (mult zero y))) 
  (eq_ind_r A (add y one) 
  (\lambda x_Demod_506:A.(eq A (mult zero x_Demod_506) (mult zero y))) 
  (eq_ind_r A (inv zero) 
  (\lambda x_SupR_785:A.(eq A (mult zero (add y x_SupR_785)) (mult zero y))) 
  (eq_ind A (add (mult zero y) zero) 
  (\lambda x_Demod_223:A.(eq A (mult zero (add y (inv zero))) x_Demod_223)) 
  (eq_ind A (mult zero (inv zero)) 
  (\lambda x_SupR_337:A.(eq A (mult zero (add y (inv zero))) (add (mult zero y) x_SupR_337))) (H3 zero y (inv zero)) zero (H7 zero)) (mult zero y) (H4 (mult zero y))) one 
  (eq_ind A (add (inv zero) zero) 
  (\lambda x_SupR_463:A.(eq A one x_SupR_463)) 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_SupR_298:A.(eq A x_SupR_298 (add (inv zero) zero))) (H zero (inv zero)) one (H6 zero)) (inv zero) (H4 (inv zero)))) one 
  (eq_ind A (add y (inv y)) 
  (\lambda x_Demod_268:A.(eq A x_Demod_268 (add y one))) 
  (eq_ind A (mult (inv y) one) 
  (\lambda x_SupR_396:A.(eq A (add y x_SupR_396) (add y one))) 
  (eq_ind_r A (mult one (add y one)) 
  (\lambda x_Demod_199:A.(eq A (add y (mult (inv y) one)) x_Demod_199)) 
  (eq_ind A (add y (inv y)) 
  (\lambda x_SupR_268:A.(eq A (add y (mult (inv y) one)) (mult x_SupR_268 (add y one)))) (H2 y (inv y) one) one (H6 y)) (add y one) 
  (eq_ind A (mult (add y one) one) 
  (\lambda x_SupR_271:A.(eq A x_SupR_271 (mult one (add y one)))) (H1 (add y one) one) (add y one) (H5 (add y one)))) (inv y) (H5 (inv y))) one (H6 y))) zero (H5 zero))) (add x y) (H4 (add x y))) (add zero x) 
  (eq_ind A (add x zero) 
  (\lambda x_Demod_543:A.(eq A (add zero x_Demod_543) (add zero (mult (add x zero) x)))) 
  (eq_ind_r A (mult zero zero) 
  (\lambda x_Demod_524:A.(eq A (add zero (add x x_Demod_524)) (add zero (mult (add x zero) x)))) 
  (eq_ind_r A (mult x (add x zero)) 
  (\lambda x_SupR_628:A.(eq A (add zero x_SupR_628) (add zero (mult (add x zero) x)))) 
  (eq_ind_r A (mult (add zero (add x zero)) (add zero x)) 
  (\lambda x_Demod_195:A.(eq A (add zero (mult x (add x zero))) x_Demod_195)) 
  (eq_ind_r A (mult (add zero x) (add zero (add x zero))) 
  (\lambda x_SupR_272:A.(eq A x_SupR_272 (mult (add zero (add x zero)) (add zero x)))) (H1 (add zero x) (add zero (add x zero))) (add zero (mult x (add x zero))) (H2 zero x (add x zero))) (add zero (mult (add x zero) x)) (H2 zero (add x zero) x)) (add x (mult zero zero)) 
  (eq_ind A (add x zero) 
  (\lambda x_SupR_296:A.(eq A (add x (mult zero zero)) (mult x_SupR_296 (add x zero)))) (H2 x zero zero) x (H4 x))) zero 
  (eq_ind A (mult zero one) 
  (\lambda x_Demod_507:A.(eq A x_Demod_507 (mult zero zero))) 
  (eq_ind_r A (add zero one) 
  (\lambda x_Demod_506:A.(eq A (mult zero x_Demod_506) (mult zero zero))) 
  (eq_ind_r A (inv zero) 
  (\lambda x_SupR_785:A.(eq A (mult zero (add zero x_SupR_785)) (mult zero zero))) 
  (eq_ind A (add (mult zero zero) zero) 
  (\lambda x_Demod_223:A.(eq A (mult zero (add zero (inv zero))) x_Demod_223)) 
  (eq_ind A (mult zero (inv zero)) 
  (\lambda x_SupR_337:A.(eq A (mult zero (add zero (inv zero))) (add (mult zero zero) x_SupR_337))) (H3 zero zero (inv zero)) zero (H7 zero)) (mult zero zero) (H4 (mult zero zero))) one 
  (eq_ind A (add (inv zero) zero) 
  (\lambda x_SupR_463:A.(eq A one x_SupR_463)) 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_SupR_298:A.(eq A x_SupR_298 (add (inv zero) zero))) (H zero (inv zero)) one (H6 zero)) (inv zero) (H4 (inv zero)))) one 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_Demod_268:A.(eq A x_Demod_268 (add zero one))) 
  (eq_ind A (mult (inv zero) one) 
  (\lambda x_SupR_396:A.(eq A (add zero x_SupR_396) (add zero one))) 
  (eq_ind_r A (mult one (add zero one)) 
  (\lambda x_Demod_199:A.(eq A (add zero (mult (inv zero) one)) x_Demod_199)) 
  (eq_ind A (add zero (inv zero)) 
  (\lambda x_SupR_268:A.(eq A (add zero (mult (inv zero) one)) (mult x_SupR_268 (add zero one)))) (H2 zero (inv zero) one) one (H6 zero)) (add zero one) 
  (eq_ind A (mult (add zero one) one) 
  (\lambda x_SupR_271:A.(eq A x_SupR_271 (mult one (add zero one)))) (H1 (add zero one) one) (add zero one) (H5 (add zero one)))) (inv zero) (H5 (inv zero))) one (H6 zero))) zero (H5 zero))) x (H4 x))) x 
  (eq_ind A (add x zero) 
  (\lambda x_SupR_299:A.(eq A x_SupR_299 (add zero x))) (H x zero) x (H4 x))))) (add (add x (mult y z)) y) 
  (sym_eq\subst[A \Assign A ; x \Assign (add (add x (mult y z)) y) ; y \Assign (add y (add x (mult y z)))] (H (add x (mult y z)) y)))
).
auto paramodulation.

qed.
theorem bool5:
  \forall A:Set.
  \forall one:A.
  \forall zero:A.
  \forall add: A \to A \to A.
  \forall mult: A \to A \to A.
  \forall inv: A \to A.
  \forall c1:(\forall x,y:A.(add x y) = (add y x)). 
  \forall c2:(\forall x,y:A.(mult x y) = (mult y x)). 
  \forall d1: (\forall x,y,z:A.
              (add x (mult y z)) = (mult (add x y) (add x z))).
  \forall d2: (\forall x,y,z:A.
              (mult x (add y z)) = (add (mult x y) (mult x z))).  
  \forall i1: (\forall x:A. (add x zero) = x).
  \forall i2: (\forall x:A. (mult x one) = x).   
  \forall inv1: (\forall x:A. (add x (inv x)) = one).  
  \forall inv2: (\forall x:A. (mult x (inv x)) = zero). 
  \forall x,y:A.
    (inv (mult x y)) = (add (inv x) (inv y)).
intros.auto paramodulation.
qed.
