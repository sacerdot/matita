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

include "lambda/subst.ma".
include "basics/list.ma".


(*************************** substl *****************************)

let rec substl (G:list T) (N:T) : list T ≝  
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

axiom A: nat → nat → Prop.
axiom R: nat → nat → nat → Prop.
axiom conv: T → T → Prop.

inductive TJ: list T → T → T → Prop ≝
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
     TJ G A B → TJ G B (Sort i) → TJ G A C
  | dummy: ∀G.∀A,B.∀i. 
     TJ G A B → TJ G B (Sort i) → TJ G (D A) B.
     
interpretation "type judgement" 'TJ G A B = (TJ G A B).

(* ninverter TJ_inv2 for TJ (%?%) : Prop. *)

(**** definitions ****)

inductive Glegal (G: list T) : Prop ≝
glegalk : ∀A,B. G ⊢ A : B → Glegal G.

inductive Gterm (G: list T) (A:T) : Prop ≝
  | is_term: ∀B.G ⊢ A:B → Gterm G A
  | is_type: ∀B.G ⊢ B:A → Gterm G A.

inductive Gtype (G: list T) (A:T) : Prop ≝ 
gtypek: ∀i.G ⊢ A : Sort i → Gtype G A.

inductive Gelement (G:list T) (A:T) : Prop ≝
gelementk: ∀B.G ⊢ A:B → Gtype G B → Gelement G A.

inductive Tlegal (A:T) : Prop ≝ 
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

theorem start_lemma1: ∀G.∀i,j. 
A i j → Glegal G → G ⊢ Sort i: Sort j.
#G #i #j #axij #Gleg (cases Gleg) 
#A #B #tjAB (elim tjAB) /2/
(* bello *) qed.

theorem start_rel: ∀G.∀A.∀C.∀n,i,q.
G ⊢ C: Sort q → G ⊢ Rel n: lift A 0 i → (C::G) ⊢ Rel (S n): lift A 0 (S i).
#G #A #C #n #i #p #tjC #tjn
 (applyS (weak G (Rel n))) //. (* bello *)
 (*
 nrewrite > (plus_n_O i); 
 nrewrite > (plus_n_Sm i O); 
 nrewrite < (lift_lift A 1 i);
 nrewrite > (plus_n_O n);  nrewrite > (plus_n_Sm n O); 
 applyS (weak G (Rel n) (lift A i) C p tjn tjC). *)
qed.
  
theorem start_lemma2: ∀G.
Glegal G → ∀n. n < |G| → G ⊢ Rel n: lift (nth n T G (Rel O)) 0 (S n).
#G #Gleg (cases Gleg) #A #B #tjAB (elim tjAB) /2/
  [#i #j #axij #p normalize #abs @False_ind @(absurd … abs) // 
  |#G #A #i #tjA #Hind #m (cases m) /2/
   #p #Hle @start_rel // @Hind @le_S_S_to_le @Hle
  |#G #A #B #C #i #tjAB #tjC #Hind1 #_ #m (cases m)
     /2/ #p #Hle @start_rel // @Hind1 @le_S_S_to_le @Hle
  ]
qed.

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


axiom conv_subst: ∀P,Q,N,i.conv P Q → conv P[i := N] Q[i := N].

theorem substitution_tj: 
∀E.∀A,B,M. E ⊢M:B → ∀G,D.∀N. E = D@A::G → G ⊢ N:A → 
  ((substl D N)@G) ⊢ M[|D| := N]: B[|D| := N].
#E #A #B #M #tjMB (elim tjMB)
  [normalize #i #j #k #G #D #N (cases D) 
    [normalize #isnil destruct
    |#P #L normalize #isnil destruct
    ]
  |#G #A1 #i #tjA #Hind #G1 #D (cases D) 
    [#N #Heq #tjN >(delift (lift N O O) A1 O O O ??) //
     (normalize in Heq) destruct /2/
    |#H #L #N1 #Heq (normalize in Heq)
     #tjN1 normalize destruct; (applyS start) /2/
    ]
  |#G #P #Q #R #i #tjP #tjR #Hind1 #Hind2 #G1 #D #N
   (cases D) normalize
    [#Heq destruct #tjN //
    |#H #L #Heq #tjN1 destruct;
       (* napplyS weak non va *)
     (cut (S (length T L) = (length T L)+0+1)) [//] 
     #Hee (applyS weak) /2/
    ]
  |#G #P #Q #i #j #k #Ax #tjP #tjQ #Hind1 #Hind2
   #G1 #D #N #Heq #tjN normalize @(prod … Ax);
    [/2/
    |(cut (S (length T D) = (length T D)+1)) [//] 
     #Heq1 <Heq1 @(Hind2 ? (P::D)) normalize //
    ]
  |#G #P #Q #R #S #tjP #tjS #Hind1 #Hind2
   #G1 #D #N #Heq #tjN (normalize in Hind1 ⊢ %)
   >(plus_n_O (length ? D)) in ⊢ (? ? ? (? ? % ?))
   >(subst_lemma R S N ? 0) (applyS app) /2/
  |#G #P #Q #R #i #tjR #tjProd #Hind1 #Hind2
   #G1 #D #N #Heq #tjN normalize
   (applyS abs) 
    [normalize in Hind2 /2/
    |(* napplyS (Hind1 G1 (P::D) N ? tjN); sistemare *)
     generalize in match (Hind1 G1 (P::D) N ? tjN);
      [#H (normalize in H) (applyS H) | normalize // ]
    ]
  |#G #P #Q #R #i #convQR #tjP #tjQ #Hind1 #Hind2
   #G1 #D #N #Heq #tjN
   @(conv …(conv_subst … convQR) ? (Hind2 …)) // @Hind1 //
  |#G #P #Q #i #tjP #tjQ #Hind1 #Hind2
   #G1 #D #N #Heq #tjN @dummy /2/ 
  ]
qed.

lemma tj_subst_0: ∀G,v,w. G ⊢ v : w → ∀t,u. w :: G ⊢ t : u →
                  G ⊢ t[0≝v] : u[0≝v].
#G #v #w #Hv #t #u #Ht 
lapply (substitution_tj … Ht ? ([]) … Hv) normalize //
qed.

(* weakening lemma: special case *)
axiom tj_weak_1: ∀G,t,u. G ⊢ t : u → ∀w. w :: G ⊢ lift t 0 1 : lift u 0 1.
