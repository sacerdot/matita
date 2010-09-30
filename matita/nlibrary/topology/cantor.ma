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

include "topology/igft.ma".

ntheorem axiom_cond: ∀A:Ax.∀a:A.∀i:𝐈 a.a ◃ 𝐂 a i.
#A; #a; #i; @2 i; #x; #H; @; napply H;
nqed.

nlemma hint_auto1 : ∀A,U,V. (∀x.x ∈ U → x ◃ V) → cover_set cover A U V.
nnormalize; /2/.
nqed.

alias symbol "covers" (instance 1) = "covers".
alias symbol "covers" (instance 2) = "covers set".
alias symbol "covers" (instance 3) = "covers".
ntheorem transitivity: ∀A:Ax.∀a:A.∀U,V. a ◃ U → U ◃ V → a ◃ V.
#A; #a; #U; #V; #aU; #UV; nelim aU; /3/;
nqed.

ndefinition emptyset: ∀A.Ω^A ≝ λA.{x | False}.

notation "∅" non associative with precedence 90 for @{ 'empty }.
interpretation "empty" 'empty = (emptyset ?).

naxiom EM : ∀A:Ax.∀a:A.∀i_star.(a ∈ 𝐂 a i_star) ∨ ¬( a ∈ 𝐂 a i_star).

alias symbol "covers" = "covers".
ntheorem th2_3 :
  ∀A:Ax.∀a:A. a ◃ ∅ → ∃i. ¬ a ∈ 𝐂 a i.
#A; #a; #H; nelim H;
##[ #n; *;
##| #b; #i_star; #IH1; #IH2; ncases (EM … b i_star); /3/;
##] 
nqed.

ninductive eq1 (A : Type[0]) : Type[0] → CProp[0] ≝ 
| refl1 : eq1 A A.

notation "hvbox( a break ∼ b)" non associative with precedence 40 
for @{ 'eqT $a $b }.

interpretation "eq between types" 'eqT a b = (eq1 a b).

ninductive unit : Type[0] ≝ one : unit.

nrecord uAx : Type[1] ≝ {
  uax_ : Ax;
  with_ : ∀a:uax_.𝐈 a ∼ unit
}.

ndefinition uax : uAx → Ax.
#A; @ (uax_ A) (λx.unit); #a; #_; 
napply (𝐂 a ?);  nlapply one; ncases (with_ A a); //; 
nqed.

ncoercion uax : ∀u:uAx. Ax ≝ uax on _u : uAx to Ax.

naxiom A: Type[0].
naxiom S: A → Ω^A.

ndefinition axs: uAx.
@; ##[ @ A (λ_.unit) (λa,x.S a); ##| #_; @; ##]
nqed.
 
alias id "S" = "cic:/matita/ng/topology/igft/S.fix(0,0,1)".
unification hint 0 ≔ ;
         x ≟ axs  
  (* -------------- *) ⊢
         S x ≡ A. 

ntheorem col2_4 :
  ∀A:uAx.∀a:uax A. a ◃ ∅ → ¬ a ∈ 𝐂 a one.
#A; #a; #H; nelim H;
##[ #n; *;
##| #b; #i_star; #IH1; #IH2; #H3; nlapply (IH2 … H3); /2/;
##]
nqed.

ndefinition Z : Ω^axs ≝ { x | x ◃ ∅ }.

ntheorem cover_monotone: ∀A:Ax.∀a:A.∀U,V.U ⊆ V → a ◃ U → a ◃ V.
#A; #a; #U; #V; #HUV; #H; nelim H; /3/; 
nqed.

ntheorem th3_1: ¬∃a:axs.Z ⊆ S a ∧ S a ⊆ Z.
*; #a; *; #ZSa; #SaZ; 
ncut (a ◃ Z); ##[
  nlapply (axiom_cond … a one); #AxCon; nchange in AxCon with (a ◃ S a);
  napply (cover_monotone … AxCon); nassumption; ##] #H; 
ncut (a ◃ ∅); ##[ napply (transitivity … H); nwhd in match Z; //; ##] #H1;
ncut (¬ a ∈ S a); ##[ napply (col2_4 … H1); ##] #H2;
ncut (a ∈ S a); ##[ napply ZSa; napply H1; ##] #H3;
/2/;
nqed.

include "nat/nat.ma".

naxiom phi : nat → nat → nat.

notation > "ϕ" non associative with precedence 90 for @{ 'phi }.
interpretation "phi" 'phi = phi.
 
notation < "ϕ a i" non associative with precedence 90 for @{ 'phi2 $a $i}.
interpretation "phi2" 'phi2 a i = (phi a i). 
notation < "ϕ a" non associative with precedence 90 for @{ 'phi1 $a }.
interpretation "phi2" 'phi1 a = (phi a). 

ndefinition caxs : uAx. 
@; ##[ @ nat (λ_.unit); #a; #_; napply { x | ϕ a x = O } ##| #_; @; ##]
nqed.


alias id "S" = "cic:/matita/ng/topology/igft/S.fix(0,0,1)".
unification hint 0 ≔ ;
         x ≟ caxs  
  (* -------------- *) ⊢
         S x ≡ nat. 

naxiom h : nat → nat. 

alias symbol "eq" = "leibnitz's equality".
alias symbol "eq" = "setoid1 eq".
alias symbol "covers" = "covers".
alias symbol "eq" = "leibnitz's equality".
naxiom Ph :  ∀x.h x = O \liff  x ◃ ∅.

nlemma replace_char:
  ∀A:Ax.∀U,V.U ⊆ V → V ⊆ U → ∀a:A.a ◃ U → a ◃ V.
#A; #U; #V;  #UV; #VU; #a; #aU; nelim aU; /3/;
nqed.

ntheorem th_ch3: ¬∃a:caxs.∀x.ϕ a x = h x.
*; #a; #H;
ncut (a ◃ { x | x ◃ ∅}); ##[
  napply (replace_char … { x | h x = O }); ##[ ##1,2: #x; ncases (Ph x); /2/; ##]
  napply (replace_char … { x | ϕ a x = O }); ##[##1,2: #x; nrewrite > (H x); //; ##]
  napply (axiom_cond … a one); ##] #H1;
ncut (a ◃ ∅); ##[ napply (transitivity … H1); //; ##] #H2;
nlapply (col2_4 …H2); #H3;
ncut (a ∈ 𝐂 a one); ##[
  nnormalize; ncases (Ph a); nrewrite > (H a); /2/; ##] #H4;
/2/;
nqed.