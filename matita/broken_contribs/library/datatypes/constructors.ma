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

include "logic/equality.ma".

inductive void : Set \def.

inductive unit : Set ≝ something: unit.

inductive Prod (A,B:Type) : Type \def
pair : A \to B \to Prod A B.

interpretation "Pair construction" 'pair x y = (pair ? ? x y).

interpretation "Product" 'product x y = (Prod x y).

definition fst \def \lambda A,B:Type.\lambda p: Prod A B.
match p with
[(pair a b) \Rightarrow a]. 

definition snd \def \lambda A,B:Type.\lambda p: Prod A B.
match p with
[(pair a b) \Rightarrow b].

interpretation "pair pi1" 'pi1 = (fst ? ?).
interpretation "pair pi2" 'pi2 = (snd ? ?).
interpretation "pair pi1" 'pi1a x = (fst ? ? x).
interpretation "pair pi2" 'pi2a x = (snd ? ? x).
interpretation "pair pi1" 'pi1b x y = (fst ? ? x y).
interpretation "pair pi2" 'pi2b x y = (snd ? ? x y).

theorem eq_pair_fst_snd: \forall A,B:Type.\forall p:Prod A B.
p = 〈 \fst p, \snd p 〉.
intros.elim p.simplify.reflexivity.
qed.

inductive Sum (A,B:Type) : Type \def
  inl : A \to Sum A B
| inr : B \to Sum A B.

interpretation "Disjoint union" 'plus A B = (Sum A B).

inductive option (A:Type) : Type ≝
   None : option A
 | Some : A → option A.
