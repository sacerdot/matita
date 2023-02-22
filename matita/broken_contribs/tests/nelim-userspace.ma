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

include "hints_declaration.ma".

nrecord eliminator (P_ : Prop) (T_ : Type[1]) : Type[1] ≝ {
  indty : Type[0];
  elimP : indty → P_;
  elimT : indty → T_
}.

notation "\elim term 90 x term 90 P" non associative with precedence 90 
for @{'elim ?? ? $x … $P … $x}.
interpretation "elimP" 'elim = elimP.
interpretation "elimT" 'elim = elimT.

ninductive nat : Type[0] ≝ O : nat | S : nat → nat.

ndefinition eP ≝ mk_eliminator ?? nat (λ_.nat_ind) (λ_.nat_rect_Type0).

alias symbol "hint_decl" (instance 1) = "hint_decl_Type1".
unification hint 0 ≔;
  X ≟ eP
(*-----------------------------------------*) ⊢
  indty ?? X ≡ nat.
  
ninductive list (A : Type[0]) : nat → Type[0] ≝ 
| nil : list A O
| cons : ∀n.A → list A n → list A (S n).

ndefinition eL ≝ λA,n.
  mk_eliminator ?? (list A n) (λ_.list_ind A) (λ_.list_rect_Type0 A).

alias symbol "hint_decl" (instance 1) = "hint_decl_Type1".
unification hint 0 ≔ A,n;
  X ≟ eL A n
(*-----------------------------------------*) ⊢
  indty ?? X ≡ list A n.  

naxiom A : ∀n1,n2.∀l1:list nat n1.∀l2:list nat n2.Prop.

nlemma xxx : ∀n.∀x:list nat n.A ?? x x.
#n; #l;
napply (\elim l (λd,y.A ?? y l)); 


##[ ##| #len e l1 Pl1;
napply ((\elim ?? ? x) … x); #;#[ napply eP]


nrecord eliminator (indty : Type[0]) 
                   (s : Type[2])    
                   (t : Type[1]) : Type[2] ≝ {
  elimp : t
}.


ndefinition P :
  ?
≝  
  λity,s,t.λR : eliminator ity s t. λG:s.
   match R with [ mk_eliminator _ ⇒ G].

ninductive nat : Type[0] ≝ O : nat | S : nat → nat.

ndefinition eP := mk_eliminator nat Prop    ? nat_ind.
ndefinition eT := mk_eliminator nat Type[0] ? nat_rect_Type0.

unification hint 0 ≔ G;
  X ≟ eP
(*-----------------------------------------*) ⊢
  P nat Prop ? X G ≡ G.
  (*
unification hint 0 ≔ G;
  X ≟ eT
(*-----------------------------------------*) ⊢
  P nat Type[0] ? X G ≡ G.
  *)

nlemma A : nat.
napply (

ndefinition elim_gen : 
  ∀ity:Type[0].∀s,t.∀x:ity.
    ∀e:eliminator ity s t.∀G.P ity s t e G 
≝
  λity,s,t,x,e,G.elimp ??? e x.
