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

include "basics/list.ma".
include "arithmetics/nat.ma".

nlet rec length (A:Type) (l:list A) on l ≝ 
  match l with 
    [ nil ⇒ 0
    | cons a tl ⇒ S (length A tl)].

notation "|M|" non associative with precedence 65 for @{'norm $M}.
interpretation "norm" 'norm l = (length ? l).

nlet rec nth n (A:Type) (l:list A) (d:A)  ≝  
  match n with
    [O ⇒ hd A l d
    |S m ⇒ nth m A (tail A l) d].

