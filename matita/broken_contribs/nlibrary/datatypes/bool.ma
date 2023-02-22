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

include "logic/pts.ma".

inductive bool: Type[0] ≝ true: bool | false: bool.
 
definition orb ≝ λa,b:bool. match a with [ true ⇒ true | _ ⇒ b ].

notation "a || b" left associative with precedence 30 for @{'orb $a $b}.
interpretation "orb" 'orb a b = (orb a b).