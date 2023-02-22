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

include "ng_pts.ma".
include "nat/plus.ma".

ntheorem test1 : ∀n:nat.n = S n + n → S n = (S (S n)).
#m; #H;
                                 nassert m:nat H: (m=S m + m) ⊢ (S m = S (S m));
nletin pippo ≝ (S m) in H: % ⊢ (???%);
            nassert m:nat pippo : nat ≝ (S m) ⊢ (m = pippo + m → S m = S pippo);
#H; nchange in match pippo in H:% with (pred (S pippo));
 nassert m:nat pippo : nat ≝ (S m) H:(m = pred (S pippo) + m) ⊢ (S m = S pippo);
ngeneralize in match m in H:(??%?) ⊢ %;
 nassert m:nat pippo : nat ≝ (S m) ⊢ (∀n:nat. n=(pred (S pippo)+m) → (S n)=S pippo);
#x; #H;
 nassert m:nat pippo : nat ≝ (S m) x: nat H:(x = pred (S pippo) + m) ⊢ (S x = S pippo);
nwhd in H: (?%? (?%?));
           nassert m:nat pippo:nat≝(S m) x:nat H:(x=S m + m) ⊢ (S x = S pippo);
nchange in match (S ?) in H:(??%?) ⊢ (??%%) with (pred (S ?));
ngeneralize in match H;
napply (? H);
nelim m in ⊢ (???(?%?) → %);
nnormalize;
 ##[ ncases x in H ⊢ (? → % → ?);
 ##|
 ##]
STOP;

axiom A : Prop.
axiom B : Prop.
axiom C : Prop.
axiom a: A.
axiom b: B.

include "logic/connectives.ma".

definition xxx ≝ A.

notation "†" non associative with precedence 90 for @{ 'sharp }.
interpretation "a" 'sharp = a.
interpretation "b" 'sharp = b.

ntheorem foo: ∀n:nat. match n with [ O ⇒ n | S m ⇒ m + m ] = n.

(*ntheorem prova : ((A ∧ A → A) → (A → B) → C) → C.
# H; nassert H: ((A ∧ A → A) → (A → B) → C) ⊢ C;
napply (H ? ?); nassert H: ((A ∧ A → A) → (A → B) → C) ⊢ (A → B)
                        H: ((A ∧ A → A) → (A → B) → C) ⊢ (A ∧ A → A);
 ##[#L | *; #K1; #K2]
definition k : A → A ≝ λx.a.
definition k1 : A → A ≝ λx.a.
*)
axiom P : A → Prop.

include "nat/plus.ma".

ntheorem pappo : ∀n:nat.n = S n + n → S n = (S (S n)).
#m; #H; napply (let pippo ≝ (S m) in ?);
nchange in match (S m) in ⊢ (?) with pippo;
STOP (BUG)

nletin pippo ≝ (S m) in H ⊢ (?); 

nwhd in H:(???%); 
nchange in match (S ?) in H:% ⊢ (? → %) with (pred (S ?));  
ntaint;

ngeneralize in match m in ⊢ %;   in ⊢ (???% → ??%?);
STOP 
ncases (O) in m : % (*H : (??%?)*) ⊢ (???%);
nelim (S m) in H : (??%?) ⊢ (???%);
STOP;

ntheorem pippo : ∀x:A. P (k x).
nchange in match (k x) in ⊢ (∀_.%) with (k1 x); STOP

ntheorem prova : (A → A → C) → C.
napply (λH.?);
napply (H ? ?); nchange A xxx; 
napply †.
nqed. 

REFL

G

{ r1 : T1, ..., r2 : T2 }

reflexivity  apply REFL
  =
  apply (eq_refl ?);
  apply (...)
  apply (reflexivite S)
  ...
