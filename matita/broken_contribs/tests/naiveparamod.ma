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



include "logic/equality.ma".

inductive TT : Prop \def II:TT.

theorem prova1: 
  \forall A,B,C:Prop.
  \forall S:Set.
  \forall a:B -> A.
  \forall w:B \to Prop.
  \forall h:(A -> \forall x:B. w x -> TT -> C).
  \forall b:B.
  \forall s:S.
  \forall wb:w b. (* ASK ANDREA: what if b1 *)
  C.
  intros (A B C S a w h b wb).
  (* exact (h s (a b) b wb II). *)
  autobatch width = 5 depth = 3. (* look at h parameters! *)
  qed.
  
(* c'e' qualcosa di imperativo, se si cambia l'ordine delle ipotesi poi sclera *)
theorem prova2: 
  \forall A,B,C:Prop. (* SE METTO SET NON VA *)
  \forall a:B -> A.
  \forall h:A -> B -> A = B.
  (* \forall h:A -> C -> A = B. *)
  \forall b:B.
  A=B.
  intros.
  autobatch.
  try assumption.
  qed.