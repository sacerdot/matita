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

include "basics/lists/listb.ma".

(****** DeqSet: a set with a decidbale equality ******)

record FinSet : Type[1] ≝ 
{ carr:> DeqSet;
  enum: list carr;
  enum_complete: ∀x.memb carr x enum = true;
  enum_unique: uniqueb carr enum = true
}.

(*
definition DeqBool ≝ mk_DeqSet bool beqb beqb_true.

unification hint  0 ≔ ; 
    X ≟ mk_DeqSet bool beqb beqb_true
(* ---------------------------------------- *) ⊢ 
    bool ≡ carr X.
    
unification hint  0 ≔ b1,b2:bool; 
    X ≟ mk_DeqSet bool beqb beqb_true
(* ---------------------------------------- *) ⊢ 
    beqb b1 b2 ≡ eqb X b1 b2.
    
example exhint: ∀b:bool. (b == false) = true → b = false. 
#b #H @(\P H).
qed.

(* pairs *)
definition eq_pairs ≝
  λA,B:DeqSet.λp1,p2:A×B.(\fst p1 == \fst p2) ∧ (\snd p1 == \snd p2).

lemma eq_pairs_true: ∀A,B:DeqSet.∀p1,p2:A×B.
  eq_pairs A B p1 p2 = true ↔ p1 = p2.
#A #B * #a1 #b1 * #a2 #b2 %
  [#H cases (andb_true …H) #eqa #eqb >(\P eqa) >(\P eqb) //
  |#H destruct normalize >(\b (refl … a2)) >(\b (refl … b2)) //
  ]
qed.

definition DeqProd ≝ λA,B:DeqSet.
  mk_DeqSet (A×B) (eq_pairs A B) (eq_pairs_true A B).
  
unification hint  0 ≔ C1,C2; 
    T1 ≟ carr C1,
    T2 ≟ carr C2,
    X ≟ DeqProd C1 C2
(* ---------------------------------------- *) ⊢ 
    T1×T2 ≡ carr X.

unification hint  0 ≔ T1,T2,p1,p2; 
    X ≟ DeqProd T1 T2
(* ---------------------------------------- *) ⊢ 
    eq_pairs T1 T2 p1 p2 ≡ eqb X p1 p2.

example hint2: ∀b1,b2. 
  〈b1,true〉==〈false,b2〉=true → 〈b1,true〉=〈false,b2〉.
#b1 #b2 #H @(\P H).
*)