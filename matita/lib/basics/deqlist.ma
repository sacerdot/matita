(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_______________________________________________________________ *)

include "basics/deqsets.ma".
include "basics/lists/listb.ma".

(*

record DeqSet : Type[1] ≝ { 
   carr :> Type[0];
   eqb: carr → carr → bool;
   eqb_true: ∀x,y. (eqb x y = true) ↔ (x = y)
}. *)
    

(* list *)

let rec eq_list (A:DeqSet) (l1,l2:list A) on l1 ≝
  match l1 with 
  [ nil ⇒ match l2 with [nil ⇒ true | _ ⇒ false]
  | cons a1 tl1 ⇒ 
      match l2 with [nil ⇒ false | cons a2 tl2 ⇒ a1 ==a2 ∧ eq_list A tl1 tl2]].

lemma eq_list_true: ∀A:DeqSet.∀l1,l2:list A.
  eq_list A l1 l2 = true ↔ l1 = l2.
#A #l1 elim l1
  [* [% // |#a #tl % normalize #H destruct ]
  |#a1 #tl1 #Hind *  
    [normalize % #H destruct
    |#a2 #tl2 normalize %
      [cases (true_or_false (a1==a2)) #Heq >Heq normalize 
        [#Htl >(\P Heq) >(proj1 … (Hind tl2) Htl) // | #H destruct ]
      |#H destruct >(\b (refl … )) >(proj2 … (Hind tl2) (refl …)) //
      ]
    ]
  ]
qed.

definition DeqList ≝ λA:DeqSet.
  mk_DeqSet (list A) (eq_list A) (eq_list_true A).
  
unification hint  0 ≔ C; 
    T ≟ carr C,
    X ≟ DeqList C
(* ---------------------------------------- *) ⊢ 
    list T ≡ carr X.

alias id "eqb" = "cic:/matita/basics/deqsets/eqb#fix:0:0:3".
alias symbol "hint_decl" (instance 1) = "hint_decl_Type0".
unification hint  0 ≔ T,a1,a2; 
    X ≟ DeqList T
(* ---------------------------------------- *) ⊢ 
    eq_list T a1 a2 ≡ eqb X a1 a2.


