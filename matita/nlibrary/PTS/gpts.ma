(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "PTS/subst.ma".

(*************************** substl *****************************)

nlet rec substl (G:list T) (N:T) : list T ≝  
  match G with
    [ nil ⇒ nil T
    | cons A D ⇒ ((subst A (length T D) N)::(substl D N))
    ].

(*
nlemma substl_cons: ∀A,N.∀G.
substl (A::G) N = (subst_aux A (length T G) N)::(substl G N).
//; nqed.
*)

(*
nlemma length_cons: ∀A.∀G. length T (A::G) = length T G + 1.
/2/; nqed.*)

(****************************************************************)

naxiom A: nat → nat → Prop.
naxiom R: nat → nat → nat → Prop.
naxiom conv: T → T → Prop.

ninductive TJ: list T → T → T → Prop ≝
  | ax : ∀i,j. A i j → TJ (nil T) (Sort i) (Sort j)
  | start: ∀G.∀A.∀i.TJ G A (Sort i) → TJ (A::G) (Rel 0) (lift A 0 1)
  | weak: ∀G.∀A,B,C.∀i.
     TJ G A B → TJ G C (Sort i) → TJ (C::G) (lift A 0 1) (lift B 0 1)
  | prod: ∀G.∀A,B.∀i,j,k. R i j k →
     TJ G A (Sort i) → TJ (A::G) B (Sort j) → TJ G (Prod A B) (Sort k)
  | app: ∀G.∀F,A,B,a. 
     TJ G F (Prod A B) → TJ G a A → TJ G (App F a) (subst B 0 a)
  | abs: ∀G.∀A,B,b.∀i. 
     TJ (A::G) b B → TJ G (Prod A B) (Sort i) → TJ G (Lambda A b) (Prod A B)
  | conv: ∀G.∀A,B,C.∀i. conv B C →
     TJ G A B → TJ G B (Sort i) → TJ G A C.
     
notation "hvbox(G break  ⊢ A : B)" non associative with precedence 55 for @{'TJ $G $A $B}.
interpretation "type judgement" 'TJ G A B = (TJ G A B).

(* ninverter TJ_inv2 for TJ (%?%) : Prop. *)

(**** definitions ****)

ninductive Glegal (G: list T) : Prop ≝
glegalk : ∀A,B. G ⊢ A : B → Glegal G.

ninductive Gterm (G: list T) (A:T) : Prop ≝
  | is_term: ∀B.G ⊢ A:B → Gterm G A
  | is_type: ∀B.G ⊢ B:A → Gterm G A.

ninductive Gtype (G: list T) (A:T) : Prop ≝ 
gtypek: ∀i.G ⊢ A : Sort i → Gtype G A.

ninductive Gelement (G:list T) (A:T) : Prop ≝
gelementk: ∀B.G ⊢ A:B → Gtype G B → Gelement G A.

ninductive Tlegal (A:T) : Prop ≝ 
tlegalk: ∀G. Gterm G A → Tlegal A.

(*
ndefinition Glegal ≝ λG: list T.∃A,B:T.TJ G A B .

ndefinition Gterm ≝ λG: list T.λA.∃B.TJ G A B ∨ TJ G B A.

ndefinition Gtype ≝ λG: list T.λA.∃i.TJ G A (Sort i).

ndefinition Gelement ≝ λG: list T.λA.∃B.TJ G A B ∨ Gtype G B.

ndefinition Tlegal ≝ λA:T.∃G: list T.Gterm G A.
*)

(*
ntheorem free_var1: ∀G.∀A,B,C. TJ G A B →
subst C A 
#G; #i; #j; #axij; #Gleg; ncases Gleg; 
#A; #B; #tjAB; nelim tjAB; /2/; (* bello *) nqed.
*)

ntheorem start_lemma1: ∀G.∀i,j. 
A i j → Glegal G → G ⊢ Sort i: Sort j.
#G; #i; #j; #axij; #Gleg; ncases Gleg; 
#A; #B; #tjAB; nelim tjAB; /2/;
(* bello *) nqed.

ntheorem start_rel: ∀G.∀A.∀C.∀n,i,q.
G ⊢ C: Sort q → G ⊢ Rel n: lift A 0 i → (C::G) ⊢ Rel (S n): lift A 0 (S i).
#G; #A; #C; #n; #i; #p; #tjC; #tjn;
 napplyS (weak G (Rel n));//. (* bello *)
 (*
 nrewrite > (plus_n_O i); 
 nrewrite > (plus_n_Sm i O); 
 nrewrite < (lift_lift A 1 i);
 nrewrite > (plus_n_O n);  nrewrite > (plus_n_Sm n O); 
 applyS (weak G (Rel n) (lift A i) C p tjn tjC). *)
nqed.
  
ntheorem start_lemma2: ∀G.
Glegal G → ∀n. n < |G| → G ⊢ Rel n: lift (nth n T G (Rel O)) 0 (S n).
#G; #Gleg; ncases Gleg; #A; #B; #tjAB; nelim tjAB; /2/;
  ##[#i; #j; #axij; #p; nnormalize; #abs; napply False_ind;
     napply (absurd … abs); //; 
  ##|#G; #A; #i; #tjA; #Hind; #m; ncases m; /2/;
     #p; #Hle; napply start_rel; //; napply Hind;
     napply le_S_S_to_le; napply Hle;
  ##|#G; #A; #B; #C; #i; #tjAB; #tjC; #Hind1; #_; #m; ncases m;
     /2/; #p; #Hle; napply start_rel; //; 
     napply Hind1; napply le_S_S_to_le; napply Hle;
  ##]
nqed.

(*
nlet rec TJm G D on D : Prop ≝
  match D with
    [ nil ⇒ True
    | cons A D1 ⇒ TJ G (Rel 0) A ∧ TJm G D1
    ].
    
nlemma tjm1: ∀G,D.∀A. TJm G (A::D) → TJ G (Rel 0) A.
#G; #D; #A; *; //; nqed.

ntheorem transitivity_tj: ∀D.∀A,B. TJ D A B → 
  ∀G. Glegal G → TJm G D → TJ G A B.
#D; #A; #B; #tjAB; nelim tjAB;
  ##[/2/;
  ##|/2/;
  ##|#E; #T; #T0; #T1; #n; #tjT; #tjT1; #H; #H1; #G; #HlegG;
     #tjGcons; 
     napply weak;
*)
(*
ntheorem substitution_tj: 
∀G.∀A,B,N,M.TJ (A::G) M B → TJ G N A →
  TJ G (subst N M) (subst N B).
#G;#A;#B;#N;#M;#tjM; 
  napply (TJ_inv2 (A::G) M B); 
  ##[nnormalize; /3/;
  ##|#G; #A; #N; #tjA; #Hind; #Heq;
     ndestruct;//; 
  ##|#G; #A; #B; #C; #n; #tjA; #tjC; #Hind1; #Hind2; #Heq;
     ndestruct;//;
  ##|nnormalize; #E; #A; #B; #i; #j; #k;
     #Ax; #tjA; #tjB; #Hind1; #_;
     #Heq; #HeqB; #tjN; napply (prod ?????? Ax);
      ##[/2/;
      ##|nnormalize; napplyS weak;

*)

ntheorem substitution_tj: 
∀E.∀A,B,M. E ⊢M:B → ∀G,D.∀N. E = D@A::G → G ⊢ N:A → 
  ((substl D N)@G) ⊢ M[|D| ← N]: B[|D| ← N].
#E; #A; #B; #M; #tjMB; nelim tjMB; 
  ##[nnormalize; #i; #j; #k; #G; #D; #N; ncases D; 
      ##[nnormalize; #isnil; ndestruct;
      ##|#P; #L; nnormalize; #isnil; ndestruct;
      ##]
  ##|#G; #A1; #i; #tjA; #Hind; #G1; #D; ncases D; 
    ##[#N; #Heq; #tjN; 
       nrewrite > (delift (lift N O O) A1 O O O ??); //;
       nnormalize in Heq; ndestruct;/2/;
    ##|#H; #L; #N1; #Heq; nnormalize in Heq;
       #tjN1; nnormalize; ndestruct;             
       napplyS start; /2/;
    ##]
  ##|#G; #P; #Q; #R; #i; #tjP; #tjR; #Hind1; #Hind2;
     #G1; #D; #N; ncases D; nnormalize;
    ##[#Heq; ndestruct; #tjN; //;
    ##|#H; #L; #Heq;
       #tjN1; ndestruct;
       (* napplyS weak non va *)
       ncut (S (length T L) = (length T L)+0+1); ##[//##] #Heq;
       napplyS weak; /2/;
    ##]
  ##|#G; #P; #Q; #i; #j; #k; #Ax; #tjP; #tjQ; #Hind1; #Hind2;
     #G1; #D; #N; #Heq; #tjN; nnormalize;
     napply (prod … Ax); 
    ##[/2/;
    ##|ncut (S (length T D) = (length T D)+1); ##[//##] #Heq1;
       nrewrite < Heq1; 
       napply (Hind2 ? (P::D));nnormalize;//;
    ##]
  ##|#G; #P; #Q; #R; #S; #tjP; #tjS; #Hind1; #Hind2;
     #G1; #D; #N; #Heq; #tjN; nnormalize in Hind1 ⊢ %;
     nrewrite > (plus_n_O (length ? D)) in ⊢ (? ? ? (? ? % ?));
     nrewrite > (subst_lemma R S N ? 0);
     napplyS app; /2/;
  ##|#G; #P; #Q; #R; #i; #tjR; #tjProd; #Hind1; #Hind2;
     #G1; #D; #N; #Heq; #tjN; nnormalize;
     napplyS abs; 
      ##[nnormalize in Hind2; /2/;
      ##|(* napplyS (Hind1 G1 (P::D) N ? tjN); sistemare *)
       ngeneralize in match (Hind1 G1 (P::D) N ? tjN); 
        ##[#H; nnormalize in H; napplyS H;##|nnormalize; //##]
      ##|##]
  ##|
 
  
 





