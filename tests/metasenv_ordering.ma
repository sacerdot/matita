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



include "coq.ma".

alias num (instance 0) = "natural number".
alias id "nat" = "cic:/Coq/Init/Datatypes/nat.ind#xpointer(1/1)".

(* REWRITE *)

theorem th1 : 
   \forall P:Prop.
   \forall H:(\forall G1: Set. \forall G2:Prop. \forall G3 : Type. 1 = 0). 
   1 = 1 \land 1 = 0 \land 2 = 2.
   intros. split; split;
   [ reflexivity
   | rewrite > H;
     [ reflexivity | exact nat | exact (0=0) | exact Type ]
   ]
qed.    
    
theorem th2 : 
   \forall P:Prop.
   \forall H:(\forall G1: Set. \forall G2:Prop. \forall G3 : Type. 1 = 0). 
   1 = 1 \land 1 = 0 \land 3 = 3.
   intros. split. split.
   focus 13.
     rewrite > (H ?); [reflexivity | exact nat | exact (0=0) | exact Type].     
   unfocus.
   reflexivity.
   reflexivity.
qed.       
    
theorem th3 : 
   \forall P:Prop.
   \forall H:(\forall G1: Set. \forall G2:Prop. \forall G3 : Type. 1 = 0). 
   1 = 1 \land 1 = 0 \land 4 = 4.
   intros. split. split.
   focus 13.
     rewrite > (H ? ?); [reflexivity | exact nat | exact (0=0) | exact Type].
   unfocus.     
   reflexivity.
   reflexivity.
qed. 

theorem th4 : 
   \forall P:Prop.
   \forall H:(\forall G1: Set. \forall G2:Prop. \forall G3 : Type. 1 = 0). 
   1 = 1 \land 1 = 0 \land 5 = 5.
   intros. split. split.
   focus 13.
     rewrite > (H ? ? ?); [reflexivity | exact nat | exact (0=0) | exact Type].
   unfocus.     
   reflexivity.
   reflexivity.
qed. 

(* APPLY *)

theorem th5 : 
   \forall P:Prop.
   \forall H:(\forall G1: Set. \forall G2:Prop. \forall G3 : Type. 1 = 0). 
   1 = 1 \land 1 = 0 \land 6 = 6.
   intros. split. split.
   focus 13.
     apply H; [exact nat | exact (0=0) | exact Type].
   unfocus.     
   reflexivity.
   reflexivity.
qed. 

theorem th6 : 
   \forall P:Prop.
   \forall H:(\forall G1: Set. \forall G2:Prop. \forall G3 : Type. 1 = 0). 
   1 = 1 \land 1 = 0 \land 7 = 7.
   intros. split. split.
   focus 13.
     apply (H ?); [exact nat | exact (0=0) | exact Type].
   unfocus.     
   reflexivity.
   reflexivity.
qed.
      
theorem th7 : 
   \forall P:Prop.
   \forall H:(\forall G1: Set. \forall G2:Prop. \forall G3 : Type. 1 = 0). 
   1 = 1 \land 1 = 0 \land 8 = 8.
   intros. split. split.
   focus 13.
     apply (H ? ?); [exact nat | exact (0=0) | exact Type].
   unfocus.     
   reflexivity.
   reflexivity.
qed.     
      
theorem th8 : 
   \forall P:Prop.
   \forall H:(\forall G1: Set. \forall G2:Prop. \forall G3 : Type. 1 = 0). 
   1 = 1 \land 1 = 0 \land 9 = 9.
   intros. split. split.
   focus 13.
     apply (H ? ? ?); [exact nat | exact (0=0) | exact Type].
   unfocus.     
   reflexivity.
   reflexivity.
qed.

(* ELIM *)

theorem th9:
  \forall P,Q,R,S : Prop. R \to S \to \forall E:(R \to S \to P \land Q). P \land Q.
  intros (P Q R S r s H).
  elim (H ? ?); [split; assumption | exact r | exact s].
  qed.
 
theorem th10:
  \forall P,Q,R,S : Prop. R \to S \to \forall E:(R \to S \to P \land Q). P \land Q.
  intros (P Q R S r s H).
  elim (H ?); [split; assumption | exact r | exact s].
  qed.
  
theorem th11:
  \forall P,Q,R,S : Prop. R \to S \to \forall E:(R \to S \to P \land Q). P \land Q.
  intros (P Q R S r s H).
  elim H; [split; assumption | exact r | exact s].
  qed.
