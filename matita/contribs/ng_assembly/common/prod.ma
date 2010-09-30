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

(* ********************************************************************** *)
(*                          Progetto FreeScale                            *)
(*                                                                        *)
(*   Sviluppato da: Ing. Cosimo Oliboni, oliboni@cs.unibo.it              *)
(*   Sviluppo: 2008-2010                                                  *)
(*                                                                        *)
(* ********************************************************************** *)

include "num/bool.ma".

(* ***** *)
(* TUPLE *)
(* ***** *)

ninductive ProdT (T1:Type) (T2:Type) : Type ≝
 pair : T1 → T2 → ProdT T1 T2.

ndefinition fst ≝
λT1,T2:Type.λp:ProdT T1 T2.match p with [ pair  x _ ⇒ x ].

ndefinition snd ≝
λT1,T2:Type.λp:ProdT T1 T2.match p with [ pair  _ x ⇒ x ].

ndefinition eq_pair ≝
λT1,T2:Type.
λf1:T1 → T1 → bool.λf2:T2 → T2 → bool.
λp1,p2:ProdT T1 T2.
 (f1 (fst … p1) (fst … p2)) ⊗
 (f2 (snd … p1) (snd … p2)).

ninductive Prod3T (T1:Type) (T2:Type) (T3:Type) : Type ≝
triple : T1 → T2 → T3 → Prod3T T1 T2 T3.

ndefinition fst3T ≝
λT1.λT2.λT3.λp:Prod3T T1 T2 T3.match p with [ triple x _ _ ⇒ x ].

ndefinition snd3T ≝
λT1.λT2.λT3.λp:Prod3T T1 T2 T3.match p with [ triple _ x _ ⇒ x ].

ndefinition thd3T ≝
λT1.λT2.λT3.λp:Prod3T T1 T2 T3.match p with [ triple _ _ x ⇒ x ].

ndefinition eq_triple ≝
λT1,T2,T3:Type.
λf1:T1 → T1 → bool.λf2:T2 → T2 → bool.λf3:T3 → T3 → bool.
λp1,p2:Prod3T T1 T2 T3.
 (f1 (fst3T … p1) (fst3T … p2)) ⊗
 (f2 (snd3T … p1) (snd3T … p2)) ⊗
 (f3 (thd3T … p1) (thd3T … p2)).

ninductive Prod4T (T1:Type) (T2:Type) (T3:Type) (T4:Type) : Type ≝
quadruple : T1 → T2 → T3 → T4 → Prod4T T1 T2 T3 T4.

ndefinition fst4T ≝
λT1.λT2.λT3.λT4.λp:Prod4T T1 T2 T3 T4.match p with [ quadruple x _ _ _ ⇒ x ].

ndefinition snd4T ≝
λT1.λT2.λT3.λT4.λp:Prod4T T1 T2 T3 T4.match p with [ quadruple _ x _ _ ⇒ x ].

ndefinition thd4T ≝
λT1.λT2.λT3.λT4.λp:Prod4T T1 T2 T3 T4.match p with [ quadruple _ _ x _ ⇒ x ].

ndefinition fth4T ≝
λT1.λT2.λT3.λT4.λp:Prod4T T1 T2 T3 T4.match p with [ quadruple _ _ _ x ⇒ x ].

ndefinition eq_quadruple ≝
λT1,T2,T3,T4:Type.
λf1:T1 → T1 → bool.λf2:T2 → T2 → bool.λf3:T3 → T3 → bool.λf4:T4 → T4 → bool.
λp1,p2:Prod4T T1 T2 T3 T4.
 (f1 (fst4T … p1) (fst4T … p2)) ⊗
 (f2 (snd4T … p1) (snd4T … p2)) ⊗
 (f3 (thd4T … p1) (thd4T … p2)) ⊗
 (f4 (fth4T … p1) (fth4T … p2)).

ninductive Prod5T (T1:Type) (T2:Type) (T3:Type) (T4:Type) (T5:Type) : Type ≝
quintuple : T1 → T2 → T3 → T4 → T5 → Prod5T T1 T2 T3 T4 T5.

ndefinition fst5T ≝
λT1.λT2.λT3.λT4.λT5.λp:Prod5T T1 T2 T3 T4 T5.match p with [ quintuple x _ _ _ _ ⇒ x ].

ndefinition snd5T ≝
λT1.λT2.λT3.λT4.λT5.λp:Prod5T T1 T2 T3 T4 T5.match p with [ quintuple _ x _ _ _ ⇒ x ].

ndefinition thd5T ≝
λT1.λT2.λT3.λT4.λT5.λp:Prod5T T1 T2 T3 T4 T5.match p with [ quintuple _ _ x _ _ ⇒ x ].

ndefinition fth5T ≝
λT1.λT2.λT3.λT4.λT5.λp:Prod5T T1 T2 T3 T4 T5.match p with [ quintuple _ _ _ x _ ⇒ x ].

ndefinition fft5T ≝
λT1.λT2.λT3.λT4.λT5.λp:Prod5T T1 T2 T3 T4 T5.match p with [ quintuple _ _ _ _ x ⇒ x ].

ndefinition eq_quintuple ≝
λT1,T2,T3,T4,T5:Type.
λf1:T1 → T1 → bool.λf2:T2 → T2 → bool.λf3:T3 → T3 → bool.λf4:T4 → T4 → bool.λf5:T5 → T5 → bool.
λp1,p2:Prod5T T1 T2 T3 T4 T5.
 (f1 (fst5T … p1) (fst5T … p2)) ⊗
 (f2 (snd5T … p1) (snd5T … p2)) ⊗
 (f3 (thd5T … p1) (thd5T … p2)) ⊗
 (f4 (fth5T … p1) (fth5T … p2)) ⊗
 (f5 (fft5T … p1) (fft5T … p2)).
