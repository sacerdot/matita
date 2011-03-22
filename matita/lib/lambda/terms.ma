(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  This file is distributed under the terms of the 
    \   /  GNU General Public License Version 2        
     \ /      
      V_______________________________________________________________ *)

include "basics/list.ma".
include "lambda/lambda_notation.ma".

inductive T : Type[0] ≝
  | Sort: nat → T     (* starts from 0 *)
  | Rel: nat → T      (* starts from 0 *)
  | App: T → T → T    (* function, argument *)
  | Lambda: T → T → T (* type, body *)
  | Prod: T → T → T   (* type, body *)
  | D: T → T          (* dummifier *)
.

(* Appl F l generalizes App applying F to a list of arguments
 * The head of l is applied first
 *)
let rec Appl F l on l ≝ match l with 
   [ nil ⇒ F
   | cons A D ⇒ Appl (App F A) D  
   ].

lemma appl_append: ∀N,l,M. Appl M (l @ [N]) = App (Appl M l) N.
#N #l elim l -l // #hd #tl #IHl #M >IHl //
qed.
