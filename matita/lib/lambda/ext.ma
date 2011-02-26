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

include "lambda/types.ma".

(* MATTER CONCERNING STRONG NORMALIZATION TO BE PUT ELSEWHERE *****************)

(* from sn.ma *****************************************************************)

(* all(P,l) holds when P holds for all members of l *)
let rec all (P:T→Prop) l on l ≝ match l with 
   [ nil ⇒ True
   | cons A D ⇒ P A ∧ all P D
   ].

(* all(?,P,l1,l2) holds when P holds for all paired members of l1 and l2 *)
let rec all2 (A:Type[0]) (P:A→A→Prop) l1 l2 on l1 ≝ match l1 with
   [ nil          ⇒ l2 = nil ?
   | cons hd1 tl1 ⇒ match l2 with
      [ nil          ⇒ False
      | cons hd2 tl2 ⇒ P hd1 hd2 ∧ all2 A P tl1 tl2
      ]
   ].

(* Appl F l generalizes App applying F to a list of arguments
 * The head of l is applied first
 *)
let rec Appl F l on l ≝ match l with 
   [ nil ⇒ F
   | cons A D ⇒ Appl (App F A) D  
   ].

(* FG: do we need this? 
definition lift0 ≝ λp,k,M . lift M p k. (**) (* remove definition *)

theorem lift_appl: ∀p,k,l,F. lift (Appl F l) p k = 
                             Appl (lift F p k) (map … (lift0 p k) l). 
#p #k #l (elim l) -l /2/ #A #D #IHl #F >IHl //
qed.
*)

(* from rc.ma *****************************************************************)

theorem arith1: ∀x,y. (S x) ≰ (S y) → x ≰ y.
#x #y #HS @nmk (elim HS) -HS /3/
qed.

theorem arith2: ∀i,p,k. k ≤ i → i + p - (k + p) = i - k.
#i #p #k #H @plus_to_minus
>commutative_plus >(commutative_plus k) >associative_plus @eq_f /2/
qed.

theorem arith3: ∀x,y,z. x ≰ y → x + z ≰ y + z.
#x #y #z #H @nmk (elim H) -H /3/
qed.

theorem length_append: ∀A. ∀(l2,l1:list A). |l1@l2| = |l1| + |l2|.
#A #l2 #l1 (elim l1) -l1 (normalize) //
qed.

theorem lift_rel_lt: ∀i,p,k. (S i) ≤ k → lift (Rel i) k p = Rel i.
#i #p #k #Hik normalize >(le_to_leb_true … Hik) //
qed.

theorem lift_rel_ge: ∀i,p,k. (S i) ≰ k → lift (Rel i) k p = Rel (i+p).
#i #p #k #Hik normalize >(lt_to_leb_false (S i) k) /2/
qed.

theorem lift_app: ∀M,N,k,p.
                  lift (App M N) k p = App (lift M k p) (lift N k p).
// qed.

theorem lift_lambda: ∀N,M,k,p. lift (Lambda N M) k p = 
                     Lambda (lift N k p) (lift M (k + 1) p).
// qed.

theorem lift_prod: ∀N,M,k,p.
                   lift (Prod N M) k p = Prod (lift N k p) (lift M (k + 1) p).
// qed.

(* telescopic non-delifting substitution of l in M.
 * [this is the telescoping delifting substitution lifted by |l|]
 * Rel 0 is replaced with the head of l
 *)
let rec substc M l on l ≝ match l with
   [ nil ⇒ M
   | cons A D ⇒ (lift (substc M[0≝A] D) 0 1)
   ]. 

notation "M [ l ]" non associative with precedence 90 for @{'Substc $M $l}.

interpretation "Substc" 'Substc M l = (substc M l).

(* this is just to test that substitution works as expected
theorem test1: ∀A,B,C. (App (App (Rel 0) (Rel 1)) (Rel 2))[A::B::C::nil ?] = 
                       App (App (lift A 0 1) (lift B 0 2)) (lift C 0 3).
#A #B #C normalize 
>lift_0 >lift_0 >lift_0
>lift_lift1>lift_lift1>lift_lift1>lift_lift1>lift_lift1>lift_lift1
normalize
qed.
*)

theorem substc_refl: ∀l,t. (lift t 0 (|l|))[l] = (lift t 0 (|l|)).
#l (elim l) -l (normalize) // #A #D #IHl #t cut (S (|D|) = |D| + 1) // (**) (* eliminate cut *)
qed.

theorem substc_sort: ∀n,l. (Sort n)[l] = Sort n.
//
qed.
(* FG: not needed for now 
(* nautral terms *)
inductive neutral: T → Prop ≝
   | neutral_sort: ∀n.neutral (Sort n)
   | neutral_rel: ∀i.neutral (Rel i)
   | neutral_app: ∀M,N.neutral (App M N)
.
*)
