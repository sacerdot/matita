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

include "arithmetics/nat.ma".
include "basics/bool.ma".
include "basics/lists/listb.ma".

inductive coerc : Type[0] ≝ 
  | CNat : nat → coerc
  | CBool : bool → coerc.

definition eq_c ≝ λa,b. match a with
  [ CNat n ⇒ (match b with [ CNat m ⇒ eqb n m | _ ⇒ false ])
  | CBool x ⇒ (match b with [ CBool y ⇒ 
                             beqb x y
                            | _ ⇒ false]
              )
  ].

inductive type : Type[0] ≝
  | Nat : type
  | Bool: type.


definition denotation_sem ≝ λn.
  match n with
  [ Nat ⇒ 1
  | Bool ⇒ 2].
(* Funzione di equivalenza tra tipi *)
definition eqb_type ≝ λa,b. eqb (denotation_sem a) (denotation_sem b).
definition getType : coerc → type ≝ 
λ gt. match gt with
  [ CNat _ ⇒ Nat
  | CBool _ ⇒ Bool].
  


