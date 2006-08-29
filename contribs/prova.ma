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

set "baseuri" "cic:/matita/test/".

include "nat/nat.ma".

theorem pippo: \forall (P,Q,R:nat \to Prop).
               \forall x,y. x=y \to P x \to Q x \to R x.
               intros.
               try rewrite > P in Q.  
(*             
theorem pippo2: \forall (P,Q,R:nat \to Prop).
                \forall x,y. x=y \to P x \to Q x \to R x.
                intros. rewrite > H in y.
*)
