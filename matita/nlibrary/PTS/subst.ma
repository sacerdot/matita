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

include "basics/list2.ma".

ninductive T : Type ≝
  | Sort: nat → T
  | Rel: nat → T 
  | App: T → T → T 
  | Lambda: T → T → T (* type, body *)
  | Prod: T → T → T (* type, body *)
.

nlet rec lift t k p ≝
  match t with 
    [ Sort n ⇒ Sort n
    | Rel n ⇒ if_then_else T (leb (S n) k) (Rel n) (Rel (n+p))
    | App m n ⇒ App (lift m k p) (lift n k p)
    | Lambda m n ⇒ Lambda (lift m k p) (lift n (k+1) p)
    | Prod m n ⇒ Prod (lift m k p) (lift n (k+1) p)
    ].

(* 
ndefinition lift ≝ λt.λp.lift_aux t 0 p.*)

notation "↑ \sup n ( M )" non associative with precedence 70 for @{'Lift O $M}.
notation "↑ \sub k \sup n ( M )" non associative with precedence 70 for @{'Lift $n $k $M}.

(* interpretation "Lift" 'Lift n M = (lift M n). *)
interpretation "Lift" 'Lift n k M = (lift M k n).

nlet rec subst t k a ≝ 
  match t with 
    [ Sort n ⇒ Sort n
    | Rel n ⇒ if_then_else T (leb (S n) k) (Rel n)
        (if_then_else T (eqb n k) (lift a 0 n) (Rel (n-1)))
    | App m n ⇒ App (subst m k a) (subst n k a)
    | Lambda m n ⇒ Lambda (subst m k a) (subst n (k+1) a)
    | Prod m n ⇒ Prod (subst m k a) (subst n (k+1) a)
    ].

(* meglio non definire 
ndefinition subst ≝ λa.λt.subst_aux t 0 a.
notation "M [ N ]" non associative with precedence 90 for @{'Subst $N $M}.
*)

notation "M [ k ← N]" non associative with precedence 90 for @{'Subst $M $k $N}.

(* interpretation "Subst" 'Subst N M = (subst N M). *)
interpretation "Subst" 'Subst M k N = (subst M k N).

(*** properties of lift and subst ***)

nlemma lift_0: ∀t:T.∀k. lift t k 0 = t.
#t; nelim t; nnormalize; //; #n; #k; ncases (leb (S n) k); 
nnormalize;//;nqed.

(* nlemma lift_0: ∀t:T. lift t 0 = t.
#t; nelim t; nnormalize; //; nqed. *)

nlemma lift_sort: ∀i,k,n. lift (Sort i) k n = Sort i.
//; nqed.

nlemma lift_rel: ∀i,n. lift (Rel i) 0 n = Rel (i+n).
//; nqed.

nlemma lift_rel1: ∀i.lift (Rel i) 0 1 = Rel (S i).
#i; nchange with (lift (Rel i) 0 1 = Rel (1 + i)); //; nqed.

nlemma lift_lift: ∀t.∀i,j.j ≤ i  → ∀h,k. 
  lift (lift t k i) (j+k) h = lift t k (i+h).
#t; #i; #j; #h; nelim t; nnormalize; //; #n; #h;#k;
napply (leb_elim (S n) k); #Hnk;nnormalize;
  ##[nrewrite > (le_to_leb_true (S n) (j+k) ?);nnormalize;/2/;
  ##|nrewrite > (lt_to_leb_false (S n+i) (j+k) ?); 
     nnormalize;//;napply le_S_S; nrewrite > (symmetric_plus j k);
     napply le_plus;//;napply not_lt_to_le;/2/;
  ##]
nqed.

nlemma lift_lift1: ∀t.∀i,j,k. 
  lift(lift t k j) k i = lift t k (j+i).
#t;/3/; nqed.

nlemma lift_lift2: ∀t.∀i,j,k. 
  lift (lift t k j) (j+k) i = lift t k (j+i).
#t; /2/; nqed.

(*
nlemma lift_lift: ∀t.∀i,j. lift (lift t j) i = lift t (j+i).
nnormalize; //; nqed. *)

nlemma subst_lift_k: ∀A,B.∀k. subst (lift B k 1) k A = B.
#A; #B; nelim B; nnormalize; /2/; #n; #k;
napply (leb_elim (S n) k); nnormalize; #Hnk;
  ##[nrewrite > (le_to_leb_true ?? Hnk);nnormalize;//;
  ##|nrewrite > (lt_to_leb_false (S (n + 1)) k ?); nnormalize;
      ##[nrewrite > (not_eq_to_eqb_false (n+1) k ?);
         nnormalize;/2/
      ##|napply le_S; napplyS (not_le_to_lt (S n) k Hnk);
      ##]
  ##]
nqed.

(*
nlemma subst_lift: ∀A,B. subst A (lift B 1) = B.
nnormalize; //; nqed. *)

nlemma subst_sort: ∀A.∀n,k. subst (Sort n) k A = Sort n.
//; nqed.

nlemma subst_rel: ∀A.subst (Rel 0) 0 A = A.
nnormalize; //; nqed.

nlemma subst_rel1: ∀A.∀k,i. i < k → 
  subst (Rel i) k A = Rel i.
#A; #k; #i; nnormalize; #ltik;
nrewrite > (le_to_leb_true (S i) k ?); //; nqed.

nlemma subst_rel2: ∀A.∀k. 
  subst (Rel k) k A = lift A 0 k.
#A; #k; nnormalize; 
nrewrite > (lt_to_leb_false (S k) k ?); //; 
nrewrite > (eq_to_eqb_true … (refl …)); //;
nqed.

nlemma subst_rel3: ∀A.∀k,i. k < i → 
  subst (Rel i) k A = Rel (i-1).
#A; #k; #i; nnormalize; #ltik;
nrewrite > (lt_to_leb_false (S i) k ?); /2/; 
nrewrite > (not_eq_to_eqb_false i k ?); //;
napply nmk; #eqik; nelim (lt_to_not_eq … (ltik …)); /2/;
nqed.

nlemma lift_subst_ijk: ∀A,B.∀i,j,k.
  lift (subst B (j+k) A) k i = subst (lift B k i) (j+k+i) A.
#A; #B; #i; #j; nelim B; nnormalize; /2/; #n; #k;
napply (leb_elim (S n) (j + k)); nnormalize; #Hnjk;
  ##[nelim (leb (S n) k);
    ##[nrewrite > (subst_rel1 A (j+k+i) n ?);/2/;
    ##|nrewrite > (subst_rel1 A (j+k+i) (n+i) ?);/2/;
    ##]
  ##|napply (eqb_elim n (j+k)); nnormalize; #Heqnjk; 
    ##[nrewrite > (lt_to_leb_false (S n) k ?);
       ##[ncut (j+k+i = n+i);##[//;##] #Heq;
          nrewrite > Heq; nrewrite > (subst_rel2 A ?);
          nnormalize; napplyS lift_lift;//;
       ##|/2/;
       ##]
    ##|ncut (j + k < n);
      ##[napply not_eq_to_le_to_lt;
        ##[/2/;##|napply le_S_S_to_le;napply not_le_to_lt;/2/;##]
      ##|#ltjkn;
         ncut (O < n); ##[/2/; ##] #posn;
         ncut (k ≤ n); ##[/2/; ##] #lekn;
         nrewrite > (lt_to_leb_false (S (n-1)) k ?); nnormalize;
          ##[nrewrite > (lt_to_leb_false … (le_S_S … lekn));
             nrewrite > (subst_rel3 A (j+k+i) (n+i) ?);
              ##[/3/; ##|/2/; ##]
          ##|napply le_S_S;/3/;  (* /3/;*)
          ##]
     ##]
  ##]
nqed. 

ntheorem delift : ∀A,B.∀i,j,k. i ≤ j → j ≤ i + k → 
  subst (lift B i (S k)) j A = (lift B i k).
#A; #B; nelim B; nnormalize; /2/;
   ##[##2,3,4: #T; #T0; #Hind1; #Hind2; #i; #j; #k; #leij; #lejk;
      napply eq_f2; /2/; napply Hind2;
      napplyS (monotonic_le_plus_l 1);//
   ##|#n; #i; #j; #k; #leij; #ltjk;
      napply (leb_elim (S n) i); nnormalize; #len;
      ##[nrewrite > (le_to_leb_true (S n) j ?);/2/;
      ##|nrewrite > (lt_to_leb_false (S (n+S k)) j ?);
        ##[nnormalize; 
           nrewrite > (not_eq_to_eqb_false (n+S k) j ?);
           nnormalize; /2/; napply (not_to_not …len);
           #H; napply (le_plus_to_le_r k); (* why napplyS ltjk; *)
           nnormalize; //; 
        ##|napply le_S_S; napply (transitive_le … ltjk);
           napply le_plus;//; napply not_lt_to_le; /2/;
        ##]
    ##]
nqed.
     
(********************* substitution lemma ***********************)    

nlemma subst_lemma: ∀A,B,C.∀k,i. 
  subst (subst A i B) (k+i) C = 
    subst (subst A (S (k+i)) C) i (subst B k C).
#A; #B; #C; #k; nelim A; nnormalize;//; (* WOW *)
#n; #i; napply (leb_elim (S n) i); #Hle;
  ##[ncut (n < k+i); ##[/2/##] #ltn; (* lento *)
     ncut (n ≤ k+i); ##[/2/##] #len;
     nrewrite > (subst_rel1 C (k+i) n ltn);
     nrewrite > (le_to_leb_true n (k+i) len);
     nrewrite > (subst_rel1 … Hle);//;
  ##|napply (eqb_elim n i); #eqni;
    ##[nrewrite > eqni; 
       nrewrite > (le_to_leb_true i (k+i) ?); //;
       nrewrite > (subst_rel2 …); nnormalize; 
       napply sym_eq; 
       napplyS (lift_subst_ijk C B i k O);
    ##|napply (leb_elim (S (n-1)) (k+i)); #nk;
      ##[nrewrite > (subst_rel1 C (k+i) (n-1) nk);
         nrewrite > (le_to_leb_true n (k+i) ?);
        ##[nrewrite > (subst_rel3 ? i n ?);//;
           napply not_eq_to_le_to_lt;
            ##[/2/;
            ##|napply not_lt_to_le;/2/;
            ##]
        ##|napply (transitive_le … nk);//;
        ##]
      ##|ncut (i < n);
        ##[napply not_eq_to_le_to_lt; ##[/2/]
           napply (not_lt_to_le … Hle);##]
         #ltin; ncut (O < n); ##[/2/;##] #posn;
         napply (eqb_elim (n-1) (k+i)); #H
         ##[nrewrite > H; nrewrite > (subst_rel2 C (k+i));
            nrewrite > (lt_to_leb_false n (k+i) ?);
            ##[nrewrite > (eq_to_eqb_true n (S(k+i)) ?); 
              ##[nnormalize;
              ##|nrewrite < H; napplyS plus_minus_m_m;//;
              ##]
            ##|nrewrite < H; napply (lt_O_n_elim … posn);
               #m; nnormalize;//;
            ##]
         ##|ncut (k+i < n-1);
            ##[napply not_eq_to_le_to_lt;
              ##[napply symmetric_not_eq; napply H;
              ##|napply (not_lt_to_le … nk);
              ##]
            ##]
            #Hlt; nrewrite > (lt_to_leb_false n (k+i) ?);
            ##[nrewrite > (not_eq_to_eqb_false n (S(k+i)) ?);
              ##[nrewrite > (subst_rel3 C (k+i) (n-1) Hlt);
                 nrewrite > (subst_rel3 ? i (n-1) ?);//;
                 napply (le_to_lt_to_lt … Hlt);//;
              ##|napply (not_to_not … H); #Hn; nrewrite > Hn; nnormalize;//;
              ##]
            ##|napply (transitive_lt … Hlt);
               napply (lt_O_n_elim … posn);
               #m; nnormalize;//;
            ##]
          ##]
          nrewrite <H;
          ncut (∃m:nat. S m = n);
          ##[napply (lt_O_n_elim … posn); #m;@ m;//;
            ##|*; #m; #Hm; nrewrite < Hm;
               nrewrite > (delift ???????);nnormalize;/2/;
          ##]
nqed.
  



