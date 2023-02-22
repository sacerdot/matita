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

include "ng_pts.ma".

ninductive nat: Type ≝
   O: nat
 | S: nat → nat.

nlet rec nat_rect (Q_: (∀ (x_1: (nat)).Type)) H_O H_S x_1 on x_1: (Q_ x_1) ≝
 (match x_1 with [O ⇒ (H_O) | (S x_2) ⇒ (H_S x_2 (nat_rect Q_ H_O H_S x_2))]).


nlet rec nat_rec (Q: nat → Type) H_O H_S x_1 on x_1 : Q x_1 ≝
 match x_1 with
  [ O ⇒ H_O
  | S x_2 ⇒ H_S x_2 (nat_rec Q H_O H_S x_2)
  ].


ninductive ord: Type ≝
   OO: ord
 | OS: ord → ord
 | OLim: (nat → ord) → ord.

nlet rec ord_rect (Q_: (∀ (x_3: (ord)).Type)) H_OO H_OS H_OLim x_3 on x_3: (Q_ x_3) ≝
 (match x_3 with [OO ⇒ (H_OO) | (OS x_4) ⇒ (H_OS x_4 (ord_rect Q_ H_OO H_OS H_OLim (x_4))) | (OLim x_6) ⇒ (H_OLim x_6 (λx_5.(ord_rect Q_ H_OO H_OS H_OLim (x_6 x_5))))]).



naxiom P: nat → Prop.
naxiom p: ∀m. P m.

ninductive le (n:nat) (N: P n): ∀m:nat. P m → Type ≝
   len: le n N n (p n)
 | leS: ∀m,q.le n N m q → le n N (S m) (p (S m)).

nlet rec le_rect n N (Q_: (∀ m.(∀ x_4.(∀ (x_3: (le n N m x_4)).Type)))) H_len H_leS m x_4 x_3
 on x_3: (Q_ m x_4 x_3) ≝ 
(match x_3 with [len ⇒ (H_len) | (leS m q x_5) ⇒ (H_leS m q x_5 (le_rect n N Q_ H_len H_leS ? ? x_5))]).

(*
nlet rec le_rec' (n:nat) (Q: ∀D1:nat.∀D2: P D1. le n D1 D2 → Type) (p1: ?) (p2: ?) (D1:nat) (D2:P D1) (x: le n D1 D2) on x : Q D1 D2 x ≝
 match x with
  [ len ⇒ p1
  | leS m q A ⇒ p2 m q A (le_rec ? Q p1 p2 ?? A)
  ].

nlet rec le_rec (n:nat) (Q: ∀D1:nat.∀D2: P D1. le n D1 D2 → Type) (p1: ?) (p2: ?) (D1:nat) (D2:P D1) (x: le n D1 D2) on x : Q D1 D2 x ≝ ?.
 ## [ ncases x;
       ##[ #m; #q; #A; napply (p2 m q A (le_rec ? Q p1 p2 ?? A));
       ##| napply p1;
       ##]
 ## |##*: ## skip;
 ## ]
nqed.*)

ninductive list (A:Type) : nat → Type ≝
   nil: list A O
 | cons: ∀n. A → list A n → list A (S n).

ninductive ii: Type ≝
 kk: list ii O → ii.

nlet rec ii_rect (Q_: (∀(x_16: ii).Type)) H_kknil H_kkcons x_16 on x_16: (Q_ x_16) ≝
 (match x_16 with
  [ kk x_17 ⇒ list_rect ii (λx_17.Q_ (kk x_17)) H_kknil (λw.H_kkcons w (ii_rect Q_ H_kknil H_kkcons w)) x_17 ]).