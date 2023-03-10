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

ntheorem axiom_cond: âA:Ax.âa:A.âi:đ a.a â đ a i.
#A; #a; #i; @2 i; #x; #H; @; napply H;
nqed.

nlemma hint_auto1 : âA,U,V. (âx.x â U â x â V) â cover_set cover A U V.
nnormalize; /2/.
nqed.

alias symbol "covers" (instance 1) = "covers".
alias symbol "covers" (instance 2) = "covers set".
alias symbol "covers" (instance 3) = "covers".
ntheorem transitivity: âA:Ax.âa:A.âU,V. a â U â U â V â a â V.
#A; #a; #U; #V; #aU; #UV; nelim aU; /3/;
nqed.

ndefinition emptyset: âA.ÎŠ^A â ÎťA.{x | False}.

notation "â" non associative with precedence 90 for @{ 'empty }.
interpretation "empty" 'empty = (emptyset ?).

naxiom EM : âA:Ax.âa:A.âi_star.(a â đ a i_star) â¨ ÂŹ( a â đ a i_star).

alias symbol "covers" = "covers".
ntheorem th2_3 :
  âA:Ax.âa:A. a â â â âi. ÂŹ a â đ a i.
#A; #a; #H; nelim H;
##[ #n; *;
##| #b; #i_star; #IH1; #IH2; ncases (EM âŚ b i_star); /3/;
##] 
nqed.

ninductive eq1 (A : Type[0]) : Type[0] â CProp[0] â 
| refl1 : eq1 A A.

notation "hvbox( a break âź b)" non associative with precedence 40 
for @{ 'eqT $a $b }.

interpretation "eq between types" 'eqT a b = (eq1 a b).

ninductive unit : Type[0] â one : unit.

nrecord uAx : Type[1] â {
  uax_ : Ax;
  with_ : âa:uax_.đ a âź unit
}.

ndefinition uax : uAx â Ax.
#A; @ (uax_ A) (Îťx.unit); #a; #_; 
napply (đ a ?);  nlapply one; ncases (with_ A a); //; 
nqed.

ncoercion uax : âu:uAx. Ax â uax on _u : uAx to Ax.

naxiom A: Type[0].
naxiom S: A â ÎŠ^A.

ndefinition axs: uAx.
@; ##[ @ A (Îť_.unit) (Îťa,x.S a); ##| #_; @; ##]
nqed.
 
alias id "S" = "cic:/matita/ng/topology/igft/S.fix(0,0,1)".
unification hint 0 â ;
         x â axs  
  (* -------------- *) â˘
         S x âĄ A. 

ntheorem col2_4 :
  âA:uAx.âa:uax A. a â â â ÂŹ a â đ a one.
#A; #a; #H; nelim H;
##[ #n; *;
##| #b; #i_star; #IH1; #IH2; #H3; nlapply (IH2 âŚ H3); /2/;
##]
nqed.

ndefinition Z : ÎŠ^axs â { x | x â â }.

ntheorem cover_monotone: âA:Ax.âa:A.âU,V.U â V â a â U â a â V.
#A; #a; #U; #V; #HUV; #H; nelim H; /3/; 
nqed.

ntheorem th3_1: ÂŹâa:axs.Z â S a â§ S a â Z.
*; #a; *; #ZSa; #SaZ; 
ncut (a â Z); ##[
  nlapply (axiom_cond âŚ a one); #AxCon; nchange in AxCon with (a â S a);
  napply (cover_monotone âŚ AxCon); nassumption; ##] #H; 
ncut (a â â); ##[ napply (transitivity âŚ H); nwhd in match Z; //; ##] #H1;
ncut (ÂŹ a â S a); ##[ napply (col2_4 âŚ H1); ##] #H2;
ncut (a â S a); ##[ napply ZSa; napply H1; ##] #H3;
/2/;
nqed.

include "nat/nat.ma".

naxiom phi : nat â nat â nat.

notation > "Ď" non associative with precedence 90 for @{ 'phi }.
interpretation "phi" 'phi = phi.
 
notation < "Ď a i" non associative with precedence 90 for @{ 'phi2 $a $i}.
interpretation "phi2" 'phi2 a i = (phi a i). 
notation < "Ď a" non associative with precedence 90 for @{ 'phi1 $a }.
interpretation "phi2" 'phi1 a = (phi a). 

ndefinition caxs : uAx. 
@; ##[ @ nat (Îť_.unit); #a; #_; napply { x | Ď a x = O } ##| #_; @; ##]
nqed.


alias id "S" = "cic:/matita/ng/topology/igft/S.fix(0,0,1)".
unification hint 0 â ;
         x â caxs  
  (* -------------- *) â˘
         S x âĄ nat. 

naxiom h : nat â nat. 

alias symbol "eq" = "leibnitz's equality".
alias symbol "eq" = "setoid1 eq".
alias symbol "covers" = "covers".
alias symbol "eq" = "leibnitz's equality".
naxiom Ph :  âx.h x = O \liff  x â â.

nlemma replace_char:
  âA:Ax.âU,V.U â V â V â U â âa:A.a â U â a â V.
#A; #U; #V;  #UV; #VU; #a; #aU; nelim aU; /3/;
nqed.

ntheorem th_ch3: ÂŹâa:caxs.âx.Ď a x = h x.
*; #a; #H;
ncut (a â { x | x â â}); ##[
  napply (replace_char âŚ { x | h x = O }); ##[ ##1,2: #x; ncases (Ph x); /2/; ##]
  napply (replace_char âŚ { x | Ď a x = O }); ##[##1,2: #x; nrewrite > (H x); //; ##]
  napply (axiom_cond âŚ a one); ##] #H1;
ncut (a â â); ##[ napply (transitivity âŚ H1); //; ##] #H2;
nlapply (col2_4 âŚH2); #H3;
ncut (a â đ a one); ##[
  nnormalize; ncases (Ph a); nrewrite > (H a); /2/; ##] #H4;
/2/;
nqed.