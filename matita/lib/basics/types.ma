(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_______________________________________________________________ *)

include "basics/logic.ma".

(* void *)
inductive void : Type[0] ≝.

(* unit *)
inductive unit : Type[0] ≝ it: unit.

(* Prod *)
record Prod (A,B:Type[0]) : Type[0] ≝ {
   fst: A
 ; snd: B
 }.

interpretation "Pair construction" 'pair x y = (mk_Prod ? ? x y).

interpretation "Product" 'product x y = (Prod x y).

interpretation "pair pi1" 'pi1 = (fst ? ?).
interpretation "pair pi2" 'pi2 = (snd ? ?).
interpretation "pair pi1" 'pi1a x = (fst ? ? x).
interpretation "pair pi2" 'pi2a x = (snd ? ? x).
interpretation "pair pi1" 'pi1b x y = (fst ? ? x y).
interpretation "pair pi2" 'pi2b x y = (snd ? ? x y).

theorem eq_pair_fst_snd: ∀A,B.∀p:A × B.
  p = 〈 \fst p, \snd p 〉.
#A #B #p (cases p) // qed.

lemma fst_eq : ∀A,B.∀a:A.∀b:B. \fst 〈a,b〉 = a.
// qed.

lemma snd_eq : ∀A,B.∀a:A.∀b:B. \snd 〈a,b〉 = b.
// qed.

(* sum *)
inductive Sum (A,B:Type[0]) : Type[0] ≝
  inl : A → Sum A B
| inr : B → Sum A B.

interpretation "Disjoint union" 'plus A B = (Sum A B).

(* option *)
inductive option (A:Type[0]) : Type[0] ≝
   None : option A
 | Some : A → option A.

(* sigma *)
inductive Sig (A:Type[0]) (f:A→Type[0]) : Type[0] ≝
  dp: ∀a:A.(f a)→Sig A f.
  
interpretation "Sigma" 'sigma x = (Sig ? x).
