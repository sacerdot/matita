(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic   
    ||A||  Library of Mathematics, developed at the Computer Science 
    ||T||  Department of the University of Bologna, Italy.           
    ||I||                                                            
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_____________________________________________________________*)

include "basics/finset.ma".

record Vector (A:Type[0]) (n:nat): Type[0] ≝ 
{ vec :> list A;
  len: length ? vec = n
}.

lemma Vector_eq : ∀A,n,v1,v2.
  vec A n v1 = vec A n v2 → v1 = v2.
#A #n * #l1 #H1 * #l2 #H2 #eql1l2 generalize in match H1; 
-H1 >eql1l2 //
qed.

definition vec_tail ≝ λA.λn.λv:Vector A n.
mk_Vector A (pred n) (tail A v) ?.
>length_tail >(len A n v) //
qed.

definition vec_cons ≝ λA.λa.λn.λv:Vector A n.
mk_Vector A (S n) (cons A a v) ?.
normalize >(len A n v) //
qed.

definition vec_append ≝ λA.λn1,n2.λv1:Vector A n1.λv2: Vector A n2.
mk_Vector A (n1+n2) (v1@v2).

definition vec_map ≝ λA,B.λf:A→B.λn.λv:Vector A n.
mk_Vector B n (map ?? f v) 
  (trans_eq … (length_map …) (len A n v)).

(* mapi: map with index to move in list.ma *)
let rec mapi (A,B:Type[0]) (f: nat → A → B) (l:list A) (i:nat) on l: list B ≝
 match l with 
 [ nil ⇒ nil ? 
 | cons x tl ⇒ f i x :: (mapi A B f tl (S i))].
 
lemma length_mapi: ∀A,B,l.∀f:nat→A→B.∀i. 
  |mapi ?? f l i| = |l|.
#A #B #l #f elim l // #a #tl #Hind normalize //
qed.

let rec make_listi (A:Type[0]) (a:nat→A) (n,i:nat) on n : list A ≝
match n with
[ O ⇒ [ ]
| S m ⇒ a i::(make_listi A a m (S i))
].

lemma length_make_listi: ∀A,a,n,i. 
  |make_listi A a n i| = n.
#A #a #n elim n // #m #Hind normalize //
qed.

definition vec_mapi ≝ λA,B.λf:nat→A→B.λn.λv:Vector A n.λi.
mk_Vector B n (mapi ?? f v i) 
  (trans_eq … (length_mapi …) (len A n v)).
  
definition make_veci ≝ λA.λa:nat→A.λn,i.
mk_Vector A n (make_listi A a n i) (length_make_listi A a n i).

let rec pmap A B C (f:A→B→C) l1 l2 on l1 ≝
   match l1 with
   [ nil ⇒ nil C
   | cons a tlA ⇒ 
     match l2 with
     [nil ⇒ nil C
     |cons b tlB ⇒ (f a b)::pmap A B C f tlA tlB
     ]
   ].

lemma length_pmap: ∀A,B,C.∀f:A→B→C.∀l1,l2.
length C (pmap  A B C f l1 l2) = 
  min (length A l1) (length B l2).
#A #B #C #f #l1 elim l1 // #a #tlA #Hind #l2 cases l2 //
#b #tlB lapply (Hind tlB) normalize 
cases (true_or_false (leb (length A tlA) (length B tlB))) #H >H
normalize //
qed.

definition pmap_vec ≝ λA,B,C.λf:A→B→C.λn.λvA:Vector A n.λvB:Vector B n.
mk_Vector C n (pmap A B C f vA vB) ?.
>length_pmap >(len A n vA) >(len B n vB) normalize 
>(le_to_leb_true … (le_n n)) //
qed.

