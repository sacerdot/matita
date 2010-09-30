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

ninductive True: Prop ≝  
I : True.

default "true" cic:/matita/basics/connectives/True.ind.

ninductive False: Prop ≝ .

default "false" cic:/matita/basics/connectives/False.ind.

(*
ndefinition Not: Prop → Prop ≝
λA. A → False. *)

ninductive Not (A:Prop): Prop ≝
nmk: (A → False) → Not A.

interpretation "logical not" 'not x = (Not x).

ntheorem absurd : ∀ A:Prop. A → ¬A → False.
#A; #H; #Hn; nelim Hn;/2/; nqed.

(*
ntheorem absurd : ∀ A,C:Prop. A → ¬A → C.
#A; #C; #H; #Hn; nelim (Hn H).
nqed. *)

ntheorem not_to_not : ∀A,B:Prop. (A → B) → ¬B →¬A.
/4/; nqed.

ninductive And (A,B:Prop) : Prop ≝
    conj : A → B → And A B.

interpretation "logical and" 'and x y = (And x y).

ntheorem proj1: ∀A,B:Prop. A ∧ B → A.
#A; #B; #AB; nelim AB; //.
nqed.

ntheorem proj2: ∀ A,B:Prop. A ∧ B → B.
#A; #B; #AB; nelim AB; //.
nqed.

ninductive Or (A,B:Prop) : Prop ≝
     or_introl : A → (Or A B)
   | or_intror : B → (Or A B).

interpretation "logical or" 'or x y = (Or x y).

ndefinition decidable : Prop → Prop ≝ 
λ A:Prop. A ∨ ¬ A.

ninductive ex (A:Type[0]) (P:A → Prop) : Prop ≝
    ex_intro: ∀ x:A. P x →  ex A P.
    
interpretation "exists" 'exists x = (ex ? x).

ninductive ex2 (A:Type[0]) (P,Q:A \to Prop) : Prop ≝
    ex_intro2: ∀ x:A. P x → Q x → ex2 A P Q.

ndefinition iff :=
 λ A,B. (A → B) ∧ (B → A).

interpretation "iff" 'iff a b = (iff a b).  
