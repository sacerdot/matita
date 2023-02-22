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

include "datatypes/pairs.ma".

ninductive void : Type[0] ≝.

ninductive unit : Type[0] ≝ something: unit.

ninductive Sum (A,B:Type[0]) : Type[0] ≝
| inl : A → Sum A B
| inr : B → Sum A B.

interpretation "Disjoint union" 'plus A B = (Sum A B).

ninductive option (A:Type[0]) : Type[0] ≝
 | None : option A
 | Some : A → option A.