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

include "arithmetics/nat.ma".

inductive T : Type[0] ≝
  | Sort: nat → T     (* starts from 0 *)
  | Rel: nat → T      (* starts from ... ? *)
  | App: T → T → T    (* function, argument *)
  | Lambda: T → T → T (* type, body *)
  | Prod: T → T → T   (* type, body *)
  | D: T → T          (* dummifier *)
.

(* arguments: k is the depth (starts from 0), p is the height (starts from 0) *)
let rec lift t k p ≝
  match t with 
    [ Sort n ⇒ Sort n
    | Rel n ⇒ if_then_else T (leb (S n) k) (Rel n) (Rel (n+p))
    | App m n ⇒ App (lift m k p) (lift n k p)
    | Lambda m n ⇒ Lambda (lift m k p) (lift n (k+1) p)
    | Prod m n ⇒ Prod (lift m k p) (lift n (k+1) p)
    | D n ⇒ D (lift n k p)
    ].

(* 
ndefinition lift ≝ λt.λp.lift_aux t 0 p.

notation "↑ ^ n ( M )" non associative with precedence 40 for @{'Lift O $M}.
notation "↑ _ k ^ n ( M )" non associative with precedence 40 for @{'Lift $n $k $M}.
*)
(* interpretation "Lift" 'Lift n M = (lift M n). *)
interpretation "Lift" 'Lift n k M = (lift M k n).

let rec subst t k a ≝ 
  match t with 
    [ Sort n ⇒ Sort n
    | Rel n ⇒ if_then_else T (leb (S n) k) (Rel n)
        (if_then_else T (eqb n k) (lift a 0 n) (Rel (n-1)))
    | App m n ⇒ App (subst m k a) (subst n k a)
    | Lambda m n ⇒ Lambda (subst m k a) (subst n (k+1) a)
    | Prod m n ⇒ Prod (subst m k a) (subst n (k+1) a)
    | D n ⇒ D (subst n k a)
    ].

(* meglio non definire 
ndefinition subst ≝ λa.λt.subst_aux t 0 a.
notation "M [ N ]" non associative with precedence 90 for @{'Subst $N $M}.
*)

notation "M [ k := N ]" non associative with precedence 90 for @{'Subst $M $k $N}.

(* interpretation "Subst" 'Subst N M = (subst N M). *)
interpretation "Subst" 'Subst M k N = (subst M k N).

(*** properties of lift and subst ***)

lemma lift_0: ∀t:T.∀k. lift t k 0 = t.
#t (elim t) normalize // #n #k cases (leb (S n) k) normalize // 
qed.

(* nlemma lift_0: ∀t:T. lift t 0 = t.
#t; nelim t; nnormalize; //; nqed. *)

lemma lift_sort: ∀i,k,n. lift (Sort i) k n = Sort i.
// qed.

lemma lift_rel: ∀i,n. lift (Rel i) 0 n = Rel (i+n).
// qed.

lemma lift_rel1: ∀i.lift (Rel i) 0 1 = Rel (S i).
#i (change with (lift (Rel i) 0 1 = Rel (1 + i))) //
qed.

lemma lift_lift: ∀t.∀i,j.j ≤ i  → ∀h,k. 
  lift (lift t k i) (j+k) h = lift t k (i+h).
#t #i #j #h (elim t) normalize // #n #h #k
@(leb_elim (S n) k) #Hnk normalize
  [>(le_to_leb_true (S n) (j+k) ?) normalize /2/
  |>(lt_to_leb_false (S n+i) (j+k) ?)
     normalize // @le_S_S >(commutative_plus j k)
     @le_plus // @not_lt_to_le /2/
  ]
qed.

lemma lift_lift1: ∀t.∀i,j,k. 
  lift(lift t k j) k i = lift t k (j+i).
/2/ qed.

lemma lift_lift2: ∀t.∀i,j,k. 
  lift (lift t k j) (j+k) i = lift t k (j+i).
/2/ qed.

(*
nlemma lift_lift: ∀t.∀i,j. lift (lift t j) i = lift t (j+i).
nnormalize; //; nqed. *)

lemma subst_lift_k: ∀A,B.∀k. (lift B k 1)[k ≝ A] = B.
#A #B (elim B) normalize /2/ #n #k
@(leb_elim (S n) k) normalize #Hnk
  [>(le_to_leb_true ?? Hnk) normalize //
  |>(lt_to_leb_false (S (n + 1)) k ?) normalize
    [>(not_eq_to_eqb_false (n+1) k ?) normalize /2/
    |@le_S (applyS (not_le_to_lt (S n) k Hnk))
    ]
  ]
qed.

(*
nlemma subst_lift: ∀A,B. subst A (lift B 1) = B.
nnormalize; //; nqed. *)

lemma subst_sort: ∀A.∀n,k.(Sort n) [k ≝ A] = Sort n.
// qed.

lemma subst_rel: ∀A.(Rel 0) [0 ≝ A] = A.
normalize // qed.

lemma subst_rel1: ∀A.∀k,i. i < k → 
  (Rel i) [k ≝ A] = Rel i.
#A #k #i normalize #ltik >(le_to_leb_true (S i) k) //
qed.

lemma subst_rel2: ∀A.∀k. 
  (Rel k) [k ≝ A] = lift A 0 k.
#A #k normalize >(lt_to_leb_false (S k) k) // >(eq_to_eqb_true … (refl …)) //
qed.

lemma subst_rel3: ∀A.∀k,i. k < i → 
  (Rel i) [k ≝ A] = Rel (i-1).
#A #k #i normalize #ltik >(lt_to_leb_false (S i) k) /2/ 
>(not_eq_to_eqb_false i k) // @sym_not_eq @lt_to_not_eq //
qed.

lemma lift_subst_ijk: ∀A,B.∀i,j,k.
  lift (B [j+k := A]) k i = (lift B k i) [j+k+i ≝ A].
#A #B #i #j (elim B) normalize /2/ #n #k
@(leb_elim (S n) (j + k)) normalize #Hnjk
  [(elim (leb (S n) k))
    [>(subst_rel1 A (j+k+i) n) /2/
    |>(subst_rel1 A (j+k+i) (n+i)) /2/
    ]
  |@(eqb_elim n (j+k)) normalize #Heqnjk 
    [>(lt_to_leb_false (S n) k);
      [(cut (j+k+i = n+i)) [//] #Heq
       >Heq >(subst_rel2 A ?) normalize (applyS lift_lift) //
      |/2/
      ]
    |(cut (j + k < n))
      [@not_eq_to_le_to_lt;
        [/2/ |@le_S_S_to_le @not_le_to_lt /2/ ]
      |#ltjkn
       (cut (O < n)) [/2/] #posn (cut (k ≤ n)) [/2/] #lekn
       >(lt_to_leb_false (S (n-1)) k) normalize
        [>(lt_to_leb_false … (le_S_S … lekn))
         >(subst_rel3 A (j+k+i) (n+i)); [/3/ |/2/]
        |@le_S_S; (* /3/; 65 *) (applyS monotonic_pred) @le_plus_b //
        ]
     ]
  ]
qed. 

theorem delift : ∀A,B.∀i,j,k. i ≤ j → j ≤ i + k → 
  (lift B i (S k)) [j ≝ A] = lift B i k.
#A #B (elim B) normalize /2/
  [2,3,4: #T #T0 #Hind1 #Hind2 #i #j #k #leij #lejk
   @eq_f2 /2/ @Hind2 (applyS (monotonic_le_plus_l 1)) //
  |5:#T #Hind #i #j #k #leij #lejk @eq_f @Hind //
  |#n #i #j #k #leij #ltjk @(leb_elim (S n) i) normalize #len
    [>(le_to_leb_true (S n) j) /2/
    |>(lt_to_leb_false (S (n+S k)) j);
      [normalize >(not_eq_to_eqb_false (n+S k) j)normalize 
       /2/ @(not_to_not …len) #H @(le_plus_to_le_r k) normalize //
      |@le_S_S @(transitive_le … ltjk) @le_plus // @not_lt_to_le /2/
      ]
    ]
  ]
qed.
     
(********************* substitution lemma ***********************)    

lemma subst_lemma: ∀A,B,C.∀k,i. 
  (A [i ≝ B]) [k+i ≝ C] = 
    (A [S (k+i) := C]) [i ≝ B [k ≝ C]].
#A #B #C #k (elim A) normalize // (* WOW *)
#n #i @(leb_elim (S n) i) #Hle
  [(cut (n < k+i)) [/2/] #ltn (* lento *) (cut (n ≤ k+i)) [/2/] #len
   >(subst_rel1 C (k+i) n ltn) >(le_to_leb_true n (k+i) len) >(subst_rel1 … Hle) // 
  |@(eqb_elim n i) #eqni
    [>eqni >(le_to_leb_true i (k+i)) // >(subst_rel2 …); 
     normalize @sym_eq (applyS (lift_subst_ijk C B i k O))
    |@(leb_elim (S (n-1)) (k+i)) #nk
      [>(subst_rel1 C (k+i) (n-1) nk) >(le_to_leb_true n (k+i));
        [>(subst_rel3 ? i n) // @not_eq_to_le_to_lt;
          [/2/ |@not_lt_to_le /2/]
        |@(transitive_le … nk) //
        ]
      |(cut (i < n)) [@not_eq_to_le_to_lt; [/2/] @(not_lt_to_le … Hle)]
       #ltin (cut (O < n)) [/2/] #posn
       @(eqb_elim (n-1) (k+i)) #H
        [>H >(subst_rel2 C (k+i)) >(lt_to_leb_false n (k+i));
          [>(eq_to_eqb_true n (S(k+i))); 
            [normalize |<H (applyS plus_minus_m_m) // ]
           (generalize in match ltin)
           <H @(lt_O_n_elim … posn) #m #leim >delift normalize /2/
          |<H @(lt_O_n_elim … posn) #m normalize //
          ]
        |(cut (k+i < n-1))
          [@not_eq_to_le_to_lt; [@sym_not_eq @H |@(not_lt_to_le … nk)]]
         #Hlt >(lt_to_leb_false n (k+i));
          [>(not_eq_to_eqb_false n (S(k+i)));
            [>(subst_rel3 C (k+i) (n-1) Hlt);
             >(subst_rel3 ? i (n-1)) // @(le_to_lt_to_lt … Hlt) //
            |@(not_to_not … H) #Hn >Hn normalize //
            ]
          |@(transitive_lt … Hlt) @(lt_O_n_elim … posn) normalize // 
          ]
        ]
      ]
    ]
  ] 
qed.
