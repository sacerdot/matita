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

include "arithmetics/nat.ma".

axiom lt_le_false: ∀x,y. x < y → y ≤ x → False.

definition eqn: ∀A:Type[0]. nat → (nat → A) → (nat → A) → Prop ≝
                λA,n,f1,f2. ∀m. m < n → f1 m = f2 m.

lemma eqn_O: ∀A,f1,f2. eqn A 0 f1 f2.
#A #f1 #f2 #m #H elim (lt_le_false … H) //
qed.

definition continuity ≝ λA.∀F:?→nat.∀f1.∃n.∀f2. eqn A n f1 f2 → F f1 = F f2.

definition continuity_s ≝ λA.∀f1.∀F:?→nat.∃n.∀f2. eqn A n f1 f2 → F f1 = F f2.

lemma continuity_to_s: ∀A. continuity A → continuity_s A.
// qed.

definition Zero: ∀A:Type[0]. (A→nat) → nat ≝ λ_,_.0.

definition Baire ≝ nat → nat.

definition zero: Baire ≝ λ_.0.

let rec const n k x on n ≝ match n with
[ O   ⇒ k
| S m ⇒ match x with [ O ⇒ 0 | S y ⇒ const m k y ]
].

lemma const_lt: ∀k,m,n. m ≤ n → eqn … m zero (const n k).
#k #m elim m -m // #m #IHm *
[ #H elim (lt_le_false … H) -H //
| #n #H lapply (le_S_S_to_le … H) -H
  #H1 * // #p #H2 lapply (lt_S_S_to_lt … H2) -H2
  #H2 lapply (IHm … H1 … H2) -IHm -H1 -H2 normalize //
]
qed.

lemma const_eq: ∀k,n. const n k n = k.
#K #n elim n -n // #n #H normalize //
qed.

definition comp_s: Baire → nat → Baire → nat ≝  λf,m,g. f (g m).

lemma comp_s_zero: ∀m. comp_s zero m = Zero nat.
// qed.

lemma comp_s_of_zero: ∀f,m. comp_s f m zero = f 0.
// qed.

lemma comp_s_of_const: ∀f,k,n. comp_s f n (const n k) = f k.
#f #k #n normalize //
qed.

axiom choice: ∀A:Type[0]. ∀P.
              (∀F:A→nat.∃n:nat. P F n) → ∃g. ∀F. P F (g F). 

theorem p: continuity nat → 0 = 1.
#HC lapply (continuity_to_s … HC) -HC
#HCs lapply (HCs zero) -HCs
#HCz lapply (choice … HCz) -HCz *
#MC #H letin m ≝ (MC (Zero …))
letin F ≝ (λf. MC (comp_s f m))
cut (F zero = m) // #Fz
letin mcf ≝ (MC F)
letin g ≝ (const (1+mcf) 1)
lapply (H F g ?) [ @const_lt // ] >Fz -Fz whd in ⊢ ((???%)→?); #H1
lapply (H (comp_s g m) (const m (1+mcf)) ?) [ <H1 @const_lt // ] -H -H1
>comp_s_of_zero >comp_s_of_const whd in ⊢ ((??%%)→?); >const_eq #H @H
qed.

definition uniform_continuity ≝ λA.∀F:?→nat.∃n.∀f1,f2. eqn A n f1 f2 → F f1 = F f2.

definition Cantor ≝ nat → bool.

(* la prova si rifa` con = definito come funzione proposizionale
   (ci vuole un universo ed e` un po' piu` debole) 
*)

let rec Id m n on m ≝ match m with
[ O   ⇒ match n with [ O ⇒ True  | S _ ⇒ False  ]
| S m ⇒ match n with [ O ⇒ False | S n ⇒ Id m n ]
].

lemma Id_refl: ∀n. Id n n = True.
#n elim n -n normalize //
qed.

let rec Re n on n ≝ match n return λn.Id n n with
[ O ⇒ I | S n ⇒ Re n ].

let rec J (P:∀m,n. Id m n → Type[0]) (r:∀n. P n n (Re n)) m n on m : ∀p.P m n p ≝ match m with
[ O   ⇒ match n return λn. ∀p.P O n p with [ O ⇒ True_rect_Type0 ? (* (P 0 0) *)(r 0) | S _ ⇒ False_rect_Type0 ? ]
| S x ⇒ match n return λn. ∀p.P (S x) n p with [ O ⇒ False_rect_Type0 ? | S y ⇒ J (λx,y.P (S x) (S y)) (λn.r (S n)) x y ]
].

(* Non vale: forse ci vuole η
lemma J_refl: ∀P,r,n. J P r n n (Re n) = r n.
#P #r #n elim n -n normalize // #n #IHn  
*)
