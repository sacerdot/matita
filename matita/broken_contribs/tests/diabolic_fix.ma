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

definition f :=
 λs1,s2:nat.
   let rec aux (s3:nat → nat) (x:nat) on x :=
     match x with
     [ O ⇒ s3 (S x)
     | S m ⇒ aux2 s3 m] 
    and aux2 (s3:nat → nat) (x:nat) on x :=
     match x with
     [ O ⇒ s3 x
     | S m ⇒ aux s3 m]
    in aux.
    
definition g :=
 λw.  