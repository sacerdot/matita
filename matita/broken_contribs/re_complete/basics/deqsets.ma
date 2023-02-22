include "basics/types.ma".
include "basics/bool.ma".

(****** DeqSet: a set with a decidbale equality ******)

record DeqSet : Type[1] ≝ { carr :> Type[0];
   eqb: carr → carr → bool;
   eqb_true: ∀x,y. (eqb x y = true) ↔ (x = y)
}.

notation "a == b" non associative with precedence 45 for @{ 'eqb $a $b }.
interpretation "eqb" 'eqb a b = (eqb ? a b).

notation "\P H" non associative with precedence 90 
  for @{(proj1 … (eqb_true ???) $H)}. 

notation "\b H" non associative with precedence 90 
  for @{(proj2 … (eqb_true ???) $H)}. 
  
lemma eqb_false: ∀S:DeqSet.∀a,b:S. 
  (eqb ? a b) = false ↔ a ≠ b.
#S #a #b % #H 
  [@(not_to_not … not_eq_true_false) #H1 <H @sym_eq @(\b H1)
  |cases (true_or_false (eqb ? a b)) // #H1 @False_ind @(absurd … (\P H1) H)
  ]
qed.
 
notation "\Pf H" non associative with precedence 90 
  for @{(proj1 … (eqb_false ???) $H)}. 

notation "\bf H" non associative with precedence 90 
  for @{(proj2 … (eqb_false ???) $H)}. 
  
lemma dec_eq: ∀S:DeqSet.∀a,b:S. a = b ∨ a ≠ b.
#S #a #b cases (true_or_false (eqb ? a b)) #H
  [%1 @(\P H) | %2 @(\Pf H)]
qed.

definition beqb ≝ λb1,b2.
  match b1 with [ true ⇒ b2 | false ⇒ notb b2].

notation < "a == b" non associative with precedence 45 for @{beqb $a $b }.
lemma beqb_true: ∀b1,b2. iff (beqb b1 b2 = true) (b1 = b2).
#b1 #b2 cases b1 cases b2 normalize /2/
qed. 

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