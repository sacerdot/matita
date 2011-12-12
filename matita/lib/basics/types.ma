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

include "basics/logic.ma".

(* void *)
inductive void : Type[0] ≝.

(* unit *)
inductive unit : Type[0] ≝ it: unit.

(* sum *)
inductive Sum (A,B:Type[0]) : Type[0] ≝
  inl : A → Sum A B
| inr : B → Sum A B.

interpretation "Disjoint union" 'plus A B = (Sum A B).

(* option *)
inductive option (A:Type[0]) : Type[0] ≝
   None : option A
 | Some : A → option A.

(* sigma *)
inductive Sig (A:Type[0]) (f:A→Type[0]) : Type[0] ≝
  dp: ∀a:A.(f a)→Sig A f.
  
interpretation "Sigma" 'sigma x = (Sig ? x).

(* Prod *)

record Prod (A,B:Type[0]) : Type[0] ≝ {
   fst: A
 ; snd: B
 }.

interpretation "Pair construction" 'pair x y = (mk_Prod ? ? x y).

interpretation "Product" 'product x y = (Prod x y).

interpretation "pair pi1" 'pi1 = (fst ? ?).
interpretation "pair pi2" 'pi2 = (snd ? ?).
interpretation "pair pi1" 'pi1a x = (fst ? ? x).
interpretation "pair pi2" 'pi2a x = (snd ? ? x).
interpretation "pair pi1" 'pi1b x y = (fst ? ? x y).
interpretation "pair pi2" 'pi2b x y = (snd ? ? x y).

notation "π1" with precedence 10 for @{ (proj1 ??) }.
notation "π2" with precedence 10 for @{ (proj2 ??) }.

(* Yeah, I probably ought to do something more general... *)
notation "hvbox(\langle term 19 a, break term 19 b, break term 19 c\rangle)"
with precedence 90 for @{ 'triple $a $b $c}.
interpretation "Triple construction" 'triple x y z = (mk_Prod ? ? (mk_Prod ? ? x y) z).

notation "hvbox(\langle term 19 a, break term 19 b, break term 19 c, break term 19 d\rangle)"
with precedence 90 for @{ 'quadruple $a $b $c $d}.
interpretation "Quadruple construction" 'quadruple w x y z = (mk_Prod ? ? (mk_Prod ? ? w x) (mk_Prod ? ? y z)).


theorem eq_pair_fst_snd: ∀A,B.∀p:A × B.
  p = 〈 \fst p, \snd p 〉.
#A #B #p (cases p) // qed.

lemma fst_eq : ∀A,B.∀a:A.∀b:B. \fst 〈a,b〉 = a.
// qed.

lemma snd_eq : ∀A,B.∀a:A.∀b:B. \snd 〈a,b〉 = b.
// qed.

notation > "hvbox('let' 〈ident x,ident y〉 ≝ t 'in' s)"
 with precedence 10
for @{ match $t with [ mk_Prod ${ident x} ${ident y} ⇒ $s ] }.

notation < "hvbox('let' \nbsp hvbox(〈ident x,ident y〉 \nbsp≝ break t \nbsp 'in' \nbsp) break s)"
 with precedence 10
for @{ match $t with [ mk_Prod (${ident x}:$X) (${ident y}:$Y) ⇒ $s ] }.

(* Also extracts an equality proof (useful when not using Russell). *)
notation > "hvbox('let' 〈ident x,ident y〉 'as' ident E ≝ t 'in' s)"
 with precedence 10
for @{ match $t return λx.x = $t → ? with [ mk_Prod ${ident x} ${ident y} ⇒
        λ${ident E}.$s ] (refl ? $t) }.

notation < "hvbox('let' \nbsp hvbox(〈ident x,ident y〉 \nbsp 'as'\nbsp ident E\nbsp ≝ break t \nbsp 'in' \nbsp) break s)"
 with precedence 10
for @{ match $t return λ${ident k}:$X.$eq $T $k $t → ? with [ mk_Prod (${ident x}:$U) (${ident y}:$W) ⇒
        λ${ident E}:$e.$s ] ($refl $T $t) }.

notation > "hvbox('let' 〈ident x,ident y,ident z〉 'as' ident E ≝ t 'in' s)"
 with precedence 10
for @{ match $t return λx.x = $t → ? with [ mk_Prod ${fresh xy} ${ident z} ⇒
       match ${fresh xy} return λx. ? = $t → ? with [ mk_Prod ${ident x} ${ident y} ⇒
        λ${ident E}.$s ] ] (refl ? $t) }.

notation < "hvbox('let' \nbsp hvbox(〈ident x,ident y,ident z〉 \nbsp'as'\nbsp ident E\nbsp ≝ break t \nbsp 'in' \nbsp) break s)"
 with precedence 10
for @{ match $t return λ${ident x}.$eq $T $x $t → $U with [ mk_Prod (${fresh xy}:$V) (${ident z}:$Z) ⇒
       match ${fresh xy} return λ${ident y}. $eq $R $r $t → ? with [ mk_Prod (${ident x}:$L) (${ident y}:$I) ⇒
        λ${ident E}:$J.$s ] ] ($refl $A $t) }.

notation > "hvbox('let' 〈ident w,ident x,ident y,ident z〉 ≝ t 'in' s)"
 with precedence 10
for @{ match $t with [ mk_Prod ${fresh wx} ${fresh yz} ⇒ match ${fresh wx} with [ mk_Prod ${ident w} ${ident x} ⇒ match ${fresh yz} with [ mk_Prod ${ident y} ${ident z} ⇒ $s ] ] ] }.

notation > "hvbox('let' 〈ident x,ident y,ident z〉 ≝ t 'in' s)"
 with precedence 10
for @{ match $t with [ mk_Prod ${fresh xy} ${ident z} ⇒ match ${fresh xy} with [ mk_Prod ${ident x} ${ident y} ⇒ $s ] ] }.

(* This appears to upset automation (previously provable results require greater
   depth or just don't work), so use example rather than lemma to prevent it
   being indexed. *)
example contract_pair : ∀A,B.∀e:A×B. (let 〈a,b〉 ≝ e in 〈a,b〉) = e.
#A #B * // qed.

lemma extract_pair : ∀A,B,C,D.  ∀u:A×B. ∀Q:A → B → C×D. ∀x,y.
((let 〈a,b〉 ≝ u in Q a b) = 〈x,y〉) →
∃a,b. 〈a,b〉 = u ∧ Q a b = 〈x,y〉.
#A #B #C #D * #a #b #Q #x #y normalize #E1 %{a} %{b} % try @refl @E1 qed.

lemma breakup_pair : ∀A,B,C:Type[0].∀x. ∀R:C → Prop. ∀P:A → B → C.
  R (P (\fst x) (\snd x)) → R (let 〈a,b〉 ≝ x in P a b).
#A #B #C *; normalize /2/
qed.

lemma pair_elim:
  ∀A,B,C: Type[0].
  ∀T: A → B → C.
  ∀p.
  ∀P: A×B → C → Prop.
    (∀lft, rgt. p = 〈lft,rgt〉 → P 〈lft,rgt〉 (T lft rgt)) →
      P p (let 〈lft, rgt〉 ≝ p in T lft rgt).
 #A #B #C #T * /2/
qed.

lemma pair_elim2:
  ∀A,B,C,C': Type[0].
  ∀T: A → B → C.
  ∀T': A → B → C'.
  ∀p.
  ∀P: A×B → C → C' → Prop.
    (∀lft, rgt. p = 〈lft,rgt〉 → P 〈lft,rgt〉 (T lft rgt) (T' lft rgt)) →
      P p (let 〈lft, rgt〉 ≝ p in T lft rgt) (let 〈lft, rgt〉 ≝ p in T' lft rgt).
 #A #B #C #C' #T #T' * /2/
qed.

(* Useful for avoiding destruct's full normalization. *)
lemma pair_eq1: ∀A,B. ∀a1,a2:A. ∀b1,b2:B. 〈a1,b1〉 = 〈a2,b2〉 → a1 = a2.
#A #B #a1 #a2 #b1 #b2 #H destruct //
qed.

lemma pair_eq2: ∀A,B. ∀a1,a2:A. ∀b1,b2:B. 〈a1,b1〉 = 〈a2,b2〉 → b1 = b2.
#A #B #a1 #a2 #b1 #b2 #H destruct //
qed.

lemma pair_destruct_1:
 ∀A,B.∀a:A.∀b:B.∀c. 〈a,b〉 = c → a = \fst c.
 #A #B #a #b *; /2/
qed.

lemma pair_destruct_2:
 ∀A,B.∀a:A.∀b:B.∀c. 〈a,b〉 = c → b = \snd c.
 #A #B #a #b *; /2/
qed.
