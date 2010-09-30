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

include "nat/nat.ma".
include "list/list.ma".

let rec cazzo (l:list nat) (f:list nat -> nat -> nat) (x:nat) on l :=
  match l with [ nil => x
  | cons hd tl => cazzo tl f (f tl x)].
  
let rec f (l:list nat) (x:nat) on l  :=
  match l with 
  [ nil => x
  | cons hd tl => cazzo tl f x].