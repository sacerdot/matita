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

(****** DeqSet: a set with a decidable equality ******)

record FinSet : Type[1] ≝ 
{ FinSetcarr:> DeqSet;
  enum: list FinSetcarr;
  enum_unique: uniqueb FinSetcarr enum = true
}.

notation < "𝐅" non associative with precedence 90 
 for @{'bigF}.
interpretation "FinSet" 'bigF = (mk_FinSet ???).

(* bool *)
lemma bool_enum_unique: uniqueb ? [true;false] = true.
// qed.

definition FinBool ≝ mk_FinSet DeqBool [true;false] bool_enum_unique.

unification hint  0 ≔ ; 
    X ≟ FinBool
(* ---------------------------------------- *) ⊢ 
    bool ≡ FinSetcarr X.

(* nat segment *)

lemma eqbnat_true : ∀n,m. eqb n m = true ↔ n = m.
#n #m % [@eqb_true_to_eq | @eq_to_eqb_true]
qed.

definition DeqNat ≝ mk_DeqSet nat eqb eqbnat_true.

let rec enumn n ≝ 
  match n with [ O ⇒ [ ] | S p ⇒ p::enumn p ].

lemma memb_enumn: ∀m,n. n ≤ m →  (¬ (memb DeqNat m (enumn n))) = true.
#m #n elim n // #n1 #Hind #ltm  @sym_eq @noteq_to_eqnot @sym_not_eq
% #H cases (orb_true_l … H)
  [#H1 @(absurd … (\P H1)) @sym_not_eq /2/ 
  |<(notb_notb (memb …)) >Hind normalize /2/
  ]
qed.
  
lemma enumn_unique: ∀n. uniqueb DeqNat (enumn n) = true.
#n elim n // #m #Hind @true_to_andb_true /2/ 
qed.

definition initN ≝ λn.mk_FinSet DeqNat (enumn n) (enumn_unique n).

example tipa: ∀n.∃x: initN (S n). x = n.
#n @(ex_intro … n) // qed.

example inject : ∃f: initN 2 → initN 4. injective ?? f.
@(ex_intro … S) // 
qed.

(* sum *)
definition enum_sum ≝ λA,B:DeqSet.λl1.λl2.
  (map ?? (inl A B) l1) @ (map ?? (inr A B) l2).
  
lemma enumAB_def : ∀A,B:FinSet.∀l1,l2. enum_sum A B l1 l2 = 
  (map ?? (inl A B) l1) @ (map ?? (inr A B) l2).
// qed.

lemma enumAB_unique: ∀A,B:DeqSet.∀l1,l2. 
  uniqueb A l1 = true → uniqueb B l2 = true → 
    uniqueb ? (enum_sum A B l1 l2) = true.
#A #B #l1 #l2 elim l1 
  [#_ #ul2 @unique_map_inj // #b1 #b2 #Hinr destruct //
  |#a #tl #Hind #uA #uB @true_to_andb_true 
    [@sym_eq @noteq_to_eqnot % #H 
     cases (memb_append … (sym_eq … H))
      [#H1 @(absurd (memb ? a tl = true)) 
        [@(memb_map_inj …H1) #a1 #a2 #Hinl destruct //
        |<(andb_true_l … uA) @eqnot_to_noteq //
        ]
      |elim l2
        [normalize #H destruct 
        |#b #tlB #Hind #membH cases (orb_true_l … membH)
          [#H lapply (\P H) #H1 destruct |@Hind]
        ]
      ] 
    |@Hind // @(andb_true_r … uA)
    ]
  ]
qed.

definition FinSum ≝ λA,B:FinSet.
  mk_FinSet (DeqSum A B) 
   (enum_sum A B (enum A) (enum B)) 
   (enumAB_unique … (enum_unique A) (enum_unique B)).

unification hint  0 ≔ C1,C2; 
    T1 ≟ FinSetcarr C1,
    T2 ≟ FinSetcarr C2,
    X ≟ FinSum C1 C2
(* ---------------------------------------- *) ⊢ 
    T1+T2 ≡ FinSetcarr X.

(* prod *)

definition enum_prod ≝ λA,B:DeqSet.λl1.λl2.
  compose ??? (mk_Prod A B) l1 l2.
  
axiom enum_prod_unique: ∀A,B,l1,l2. 
  uniqueb A l1 = true → uniqueb B l2 = true →
  uniqueb ? (enum_prod A B l1 l2) = true.

definition FinProd ≝ 
λA,B:FinSet.mk_FinSet (DeqProd A B)
  (enum_prod A B (enum A) (enum B)) 
  (enum_prod_unique A B (enum A) (enum B) (enum_unique A) (enum_unique B) ).

unification hint  0 ≔ C1,C2; 
    T1 ≟ FinSetcarr C1,
    T2 ≟ FinSetcarr C2,
    X ≟ FinProd C1 C2
(* ---------------------------------------- *) ⊢ 
    T1×T2 ≡ FinSetcarr X.

