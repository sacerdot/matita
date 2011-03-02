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
include "lambda/lambda_notation.ma".

(* MATTER CONCERNING STRONG NORMALIZATION TO BE PUT ELSEWHERE *****************)

(* arithmetics ****************************************************************)

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

theorem arith4: ∀x,y. S x ≰ y → x≠y → y < x.
#x #y #H1 #H2 lapply (not_le_to_lt … H1) -H1 #H1 @not_eq_to_le_to_lt /2/
qed.

theorem arith5: ∀x,y. x < y → S (y - 1) ≰ x.
#x #y #H @lt_to_not_le <minus_Sn_m /2/
qed.

(* lists **********************************************************************)

(* all(P,l) holds when P holds for all members of l *)
let rec all (A:Type[0]) (P:A→Prop) l on l ≝ match l with 
   [ nil        ⇒ True
   | cons hd tl ⇒ P hd ∧ all A P tl
   ].

theorem all_append: ∀A,P,l2,l1. all A P l1 → all A P l2 → all A P (l1 @ l2).
#A #P #l2 #l1 (elim l1) -l1 (normalize) // #hd #tl #IH1 #H (elim H) /3/
qed.

(* all(?,P,l1,l2) holds when P holds for all paired members of l1 and l2 *)
let rec all2 (A:Type[0]) (P:A→A→Prop) l1 l2 on l1 ≝ match l1 with
   [ nil          ⇒ l2 = nil ?
   | cons hd1 tl1 ⇒ match l2 with
      [ nil          ⇒ False
      | cons hd2 tl2 ⇒ P hd1 hd2 ∧ all2 A P tl1 tl2
      ]
   ].

theorem length_append: ∀A. ∀(l2,l1:list A). |l1@l2| = |l1| + |l2|.
#A #l2 #l1 (elim l1) -l1 (normalize) //
qed.

(* terms **********************************************************************)

(* Appl F l generalizes App applying F to a list of arguments
 * The head of l is applied first
 *)
let rec Appl F l on l ≝ match l with 
   [ nil ⇒ F
   | cons A D ⇒ Appl (App F A) D  
   ].

theorem appl_append: ∀N,l,M. Appl M (l @ [N]) = App (Appl M l) N.
#N #l (elim l) -l // #hd #tl #IHl #M >IHl //
qed.

(* FG: not needed for now 
(* nautral terms *)
inductive neutral: T → Prop ≝
   | neutral_sort: ∀n.neutral (Sort n)
   | neutral_rel: ∀i.neutral (Rel i)
   | neutral_app: ∀M,N.neutral (App M N)
.
*)

(* substitution ***************************************************************)

(* FG: do we need this? 
definition lift0 ≝ λp,k,M . lift M p k. (**) (* remove definition *)

theorem lift_appl: ∀p,k,l,F. lift (Appl F l) p k = 
                             Appl (lift F p k) (map … (lift0 p k) l). 
#p #k #l (elim l) -l /2/ #A #D #IHl #F >IHl //
qed.
*)

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

theorem subst_app: ∀M,N,k,L. (App M N)[k≝L] = App M[k≝L] N[k≝L].
// qed.

theorem subst_lambda: ∀N,M,k,L. (Lambda N M)[k≝L] = Lambda N[k≝L] M[k+1≝L].
// qed.

theorem subst_prod: ∀N,M,k,L. (Prod N M)[k≝L] = Prod N[k≝L] M[k+1≝L].
// qed.

(* telescopic delifting substitution of l in M.
 * Rel 0 is replaced with the head of l
 *)
let rec tsubst M l on l ≝ match l with
   [ nil      ⇒ M
   | cons A D ⇒ (tsubst M[0≝A] D)
   ]. 

interpretation "telescopic substitution" 'Subst1 M l = (tsubst M l).

theorem tsubst_refl: ∀l,t. (lift t 0 (|l|))[l] = t.
#l (elim l) -l (normalize) // #hd #tl #IHl #t cut (S (|tl|) = |tl| + 1) // (**) (* eliminate cut *)
qed.

theorem tsubst_sort: ∀n,l. (Sort n)[l] = Sort n.
//
qed.
