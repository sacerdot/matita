(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "Plogic/equality.ma".

inductive True: Prop ≝  
I : True.

inductive False: Prop ≝ .

(*
ndefinition Not: Prop → Prop ≝
λA. A → False. *)

inductive Not (A:Prop): Prop ≝
nmk: (A → False) → Not A.

interpretation "logical not" 'not x = (Not x).

theorem absurd : ∀ A:Prop. A → ¬A → False.
#A  #H  #Hn  elim Hn /2/  qed.

(*
ntheorem absurd : ∀ A,C:Prop. A → ¬A → C.
#A  #C  #H  #Hn  nelim (Hn H).
nqed. *)

theorem not_to_not : ∀A,B:Prop. (A → B) → ¬B →¬A.
/4/  qed.

inductive And (A,B:Prop) : Prop ≝
    conj : A → B → And A B.

interpretation "logical and" 'and x y = (And x y).

theorem proj1: ∀A,B:Prop. A ∧ B → A.
#A  #B  #AB  elim AB  //.
qed.

theorem proj2: ∀ A,B:Prop. A ∧ B → B.
#A  #B  #AB  elim AB  //.
qed.

inductive Or (A,B:Prop) : Prop ≝
     or_introl : A → (Or A B)
   | or_intror : B → (Or A B).

interpretation "logical or" 'or x y = (Or x y).

definition decidable : Prop → Prop ≝ 
λ A:Prop. A ∨ ¬ A.

inductive ex (A:Type[0]) (P:A → Prop) : Prop ≝
    ex_intro: ∀ x:A. P x →  ex A P.
    
interpretation "exists" 'exists x = (ex ? x).

inductive ex2 (A:Type[0]) (P,Q:A \to Prop) : Prop ≝
    ex_intro2: ∀ x:A. P x → Q x → ex2 A P Q.

definition iff :=
 λ A,B. (A → B) ∧ (B → A).

interpretation "iff" 'iff a b = (iff a b).  
