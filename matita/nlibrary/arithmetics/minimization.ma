(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        Matita is distributed under the terms of the          *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "arithmetics/nat.ma".
      
nlet rec max i f ≝
  match i with 
  [ O ⇒ O
  | (S n) ⇒ match f i with 
      [ true ⇒ i
      | false ⇒ max n f ]].

ntheorem max_O_f : ∀f: nat → bool. max O f = O.
//; nqed.

ntheorem max_S_max : ∀f: nat → bool.∀n:nat.
  (f (S n) = true ∧ max (S n) f = (S n)) ∨ 
  (f (S n) = false ∧ max (S n) f = max n f).
#f; #n; nnormalize; ncases (f (S n)); /3/;
nqed.

ntheorem le_max_n : ∀f: nat → bool. ∀n:nat.
  max n f ≤ n.
#f; #n; nelim n;//;
#n; #Hind; nnormalize; ncases (f (S n)); nnormalize; /2/;
nqed.

ntheorem le_to_le_max : ∀f: nat → bool. ∀n,m:nat.
n ≤ m  → max n f ≤ max m f.
#f; #n; #m; #lenm; nelim lenm; //;
#m; #le_n_m; #Hind; ncases (max_S_max f m); *; #_; #maxf;
##[napplyS le_S; /2/; ##| //; ##]
nqed.

ntheorem f_m_to_le_max: ∀f.∀ n,m:nat.
 m ≤n  → f m = true → m ≤ max n f.
#f; #n; nelim n; //;
#m; #Hind; #a; #lea; #fa; ncases (max_S_max f m);*;//;
#fSm; #max; napplyS Hind;//; napply (le_n_Sm_elim … lea);
##[/2/; ##| #eqa; napply False_ind;/2/;##]
nqed.

ntheorem max_f_g: ∀f,g,n. (∀i. i ≤ n → f i = g i) →
  max n f = max n g.
#f; #g; #n; nelim n;//;
#a; #Hind; #eqfg; nnormalize;
nrewrite > (eqfg …);//;
nrewrite > (Hind ?);/3/;
nqed.

(* spostare *)
ntheorem bool_elim: ∀P:bool→Prop.∀b.
(b = true → P true) → ( b = false → P false) → P b.
#P; #b; ncases b;/2/; nqed.

ntheorem le_max_f_max_g: ∀f,g,n. (∀i. i ≤ n → f i = true → g i =true) →
  max n f ≤ max n g.
#f; #g; #n; nelim n;//;
#a; #Hind; #eqfg; nnormalize;
napply (bool_elim ? (f (S a)));#fSa;
  ##[nrewrite > (eqfg …);//;
  ##|ncases (g (S a));nnormalize;
    ##[/2/; ##| napply Hind; /3/;
nqed.

ntheorem max_O : ∀f:nat → bool. ∀n:nat.
(∀i:nat. le i n → f i = false) → max n f = O.
#f; #n; nelim n; //;
#a; #Hind; #ffalse; nnormalize;
nrewrite > (ffalse ??);//; napply Hind; /3/;
nqed.

ntheorem f_max_true : ∀f:nat → bool. ∀n:nat.
(∃i:nat. i ≤ n ∧ f i = true) → f (max n f) = true. 
#f; #n; nelim n;
##[*;#x;*; #lexO; napply (le_n_O_elim … lexO);//; 
##|#a; #Hind; #exi;
   ncases (max_S_max f a); *; //;
   #fSa; #eqmax; napplyS Hind; 
   ncases exi; #x; *;#lex; #fx; @ x; @;//;
   napply (le_n_Sm_elim x a lex);
   ##[/2/; ##|#eqx; napply False_ind; /2/;##]
##]
nqed.

ntheorem exists_forall_le:∀f,n. 
  (∃i. i ≤ n ∧ f i = true) ∨ (∀i. i ≤ n → f i = false).
#f; #n; nelim n
  ##[napply (bool_elim ? (f O)); #f0;
    ##[/4/; 
    ##|@2; #i; #lei; napply (le_n_O_elim ? lei); //; ##]
 ##|#a; *;
    ##[*;#x;*;#lex;#fx;@1;@x;/3/;
    ##|#H; napply (bool_elim ? (f (S a)));#fSa;
      ##[@1;@ (S a);/2/;
      ##|@2;#i;#lei; napply (le_n_Sm_elim …lei);/3/;
      ##]
    ##]
 ##]
nqed.
     
ntheorem exists_max_forall_false:∀f,n. 
 (∃i. i ≤ n ∧ f i = true) ∧ (f (max n f) = true) ∨
 (∀i. i ≤ n → f i = false) ∧ (max n f) = O.
#f; #n; ncases (exists_forall_le f n); #H;/5/;
nqed.

ntheorem false_to_lt_max: ∀f,n,m.O < n →
f n = false → max m f ≤ n → max m f < n.
#f; #n; #m; #posn; #fn; #maxf;
nelim (le_to_or_lt_eq ? ? maxf);//;
#maxfn; ncases (exists_max_forall_false f m);*;//;
#_; #fmax; napply False_ind; /2/;
nqed.

ntheorem lt_max_to_false : ∀f:nat → bool. ∀n,m:nat. 
  max n f < m → m ≤ n → f m = false.
#f; #n; nelim n; 
  ##[#m; #H; #H1; napply False_ind; /3/; 
  ##|#a; #Hind; #m; 
     ncases (max_S_max f a); *;
     ##[#_;#eqmax;#H; #nH;napply False_ind;/3/;
     ##|#eqf;#eqmax;#lemax;#lem;
        napply (le_n_Sm_elim m a lem);/3/;
nqed.

ntheorem f_false_to_le_max: ∀f,n,p. (∃i:nat.i≤n∧f i=true) →
(∀m. p < m → f m = false) → max n f \le p.
#f; #n; #p; #exi; #allm;
napply not_lt_to_le; napply (not_to_not … not_eq_true_false);
#ltp; nrewrite < (allm ? ltp);
napply sym_eq; napply (f_max_true ? n exi); (* ? *)
nqed.

ndefinition max_spec ≝ λf:nat → bool.λn,m: nat.
m ≤ n ∧ f m =true ∧ ∀i. m < i → i ≤ n → f i = false.

ntheorem max_spec_to_max: ∀f:nat → bool.∀n,m:nat.
 max_spec f n m → max n f = m.
#f; #n; nelim n
  ##[#m; *; *; #lemO; #_; #_; napply (le_n_O_elim ? lemO); //;
  ##|#n1; #Hind; #a; *; *; #lea; #fa; #all;
     ncases (max_S_max f n1); *; #fSn1; #maxSn1;
     ##[ncases (le_to_or_lt_eq … lea); #Ha;
      ##[napply False_ind;napply (absurd ?? not_eq_true_false);
         nrewrite < fSn1; napply all;//;
      ##|//;
      ##]
     ##|napplyS Hind; @;
      ##[@; //; ncases (le_to_or_lt_eq … lea); #Ha;
        ##[/2/;
        ##|napply False_ind;/2/;
        ##]
      ##|/3/;
      ##]
  ##]
nqed.
    
(************************ minimization ************************)

nlet rec min_aux off n f ≝
  match off with
  [ O ⇒ n
  | S p ⇒ match f n with 
    [ true ⇒ n
    | false ⇒ min_aux p (S n) f]].

ndefinition min : nat → (nat → bool) → nat ≝
  λn.λf.min_aux n O f.

ntheorem min_aux_O_f: ∀f:nat → bool. ∀i :nat.
  min_aux O i f = i.
#f; #i; ncases i; //; nqed.

ntheorem min_O_f : ∀f:nat → bool.
  min O f = O.
//; nqed.

ntheorem min_aux_S : ∀f: nat → bool. ∀i,n:nat.
(f n = true ∧ min_aux (S i) n f = n) ∨ 
(f n = false ∧ min_aux (S i) n f = min_aux i (S n) f).
#f; #i; #n; nnormalize; ncases (f n); nnormalize;/3/;
nqed.

ntheorem f_min_aux_true: ∀f:nat → bool. ∀off,m:nat.
  (∃i. m ≤ i ∧ i ≤ off + m ∧ f i = true) →
  f (min_aux off m f) = true. 
#f; #off; nelim off; 
  ##[#m; *; #a; *; *; #leam; #lema; ncut (a = m);/2/;
  ##|#n; #Hind; #m; #exi; nnormalize;
     napply (bool_elim … (f m)); nnormalize; //;
     #fm;  napply Hind; 
     ncases exi; #x; *; *; #lemx; #lex; #fx;
     @ x; @; //; @; //;
     ncases (le_to_or_lt_eq …lemx); #eqx; //;
     napply False_ind; /2/; 
  ##]
nqed.

ntheorem f_min_true: ∀f:nat → bool. ∀m:nat.
  (∃i. i ≤ m ∧ f i = true) → f (min m f) = true.
#f; #m; *; #x; *; #lexm; #fx; 
napply (f_min_aux_true f m 0 ?); /4/;
nqed.

ntheorem lt_min_aux_to_false : ∀f:nat → bool.∀off,n,m:nat. 
  n ≤ m → m < min_aux off n f → f m = false.
#f; #off; nelim off;
  ##[#n; #m; #lenm; #ltmn; napply False_ind; 
     napply (absurd … lenm);/2/;
  ##|#n; #Hind; #a; #m; #leam; 
     nnormalize; napply (bool_elim ? (f a)); nnormalize;
     ##[#fa; #ltm; napply False_ind; napply (absurd  (m < a));/2/;
     ##|ncases (le_to_or_lt_eq … leam);/2/;
nqed.

nlemma le_min_aux : ∀f:nat → bool. ∀off,n:nat. 
  n ≤ min_aux off n f.
#f; #off; nelim off;//;
#n; #Hind; #a; nelim (min_aux_S f n a); *; /2/;
nqed.

ntheorem le_min_aux_r : ∀f:nat → bool. 
  ∀off,n:nat. min_aux off n f ≤ n+off.
#f; #off; nelim off; //;
#n; #Hind; #a; nelim (min_aux_S f n a); *; /2/;
nqed.
