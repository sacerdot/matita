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

include "sets/sets.ma".
include "nat/plus.ma". 
include "nat/compare.ma".
include "nat/minus.ma".
include "datatypes/pairs.ma".

alias symbol "eq" (instance 7) = "setoid1 eq".
nrecord partition (A: setoid) : Type[1] ≝ 
 { support: setoid;
   indexes: ext_powerclass support;
   class: unary_morphism1 (setoid1_of_setoid support) (ext_powerclass_setoid A);
   inhabited: ∀i. i ∈ indexes → class i ≬ class i;
   disjoint: ∀i,j. i ∈ indexes → j ∈ indexes → class i ≬ class j → i = j;
   covers: big_union support ? indexes (λx.class x) = full_set A
 }.
 
naxiom daemon: False.

nlet rec iso_nat_nat_union (s: nat → nat) m index on index : pair nat nat ≝
 match ltb m (s index) with
  [ true ⇒ mk_pair … index m
  | false ⇒
     match index with
      [ O ⇒ (* dummy value: it could be an elim False: *) mk_pair … O O
      | S index' ⇒ iso_nat_nat_union s (minus m (s index)) index']].

alias symbol "eq" = "leibnitz's equality".
naxiom plus_n_O: ∀n. n + O = n.
naxiom plus_n_S: ∀n,m. n + S m = S (n + m).
naxiom ltb_t: ∀n,m. n < m → ltb n m = true.
naxiom ltb_f: ∀n,m. ¬ (n < m) → ltb n m = false.
naxiom ltb_cases: ∀n,m. (n < m ∧ ltb n m = true) ∨ (¬ (n < m) ∧ ltb n m = false).
naxiom minus_canc: ∀n. minus n n = O.
naxiom ad_hoc9: ∀a,b,c. a < b + c → a - b < c.
naxiom ad_hoc10: ∀a,b,c. a - b = c → a = b + c.
naxiom ad_hoc11: ∀a,b. a - b ≤ S a - b.
naxiom ad_hoc12: ∀a,b. b ≤ a → S a - b - (a - b) = S O.
naxiom ad_hoc13: ∀a,b. b ≤ a → (O + (a - b)) + b = a.
naxiom ad_hoc14: ∀a,b,c,d,e. c ≤ a → a - c = b + d + e → a = b + (c + d) + e.
naxiom ad_hoc15: ∀a,a',b,c. a=a' → b < c → a + b < c + a'.
naxiom ad_hoc16: ∀a,b,c. a < c → a < b + c.
naxiom not_lt_to_le: ∀a,b. ¬ (a < b) → b ≤ a.
naxiom le_to_le_S_S: ∀a,b. a ≤ b → S a ≤ S b.
naxiom minus_S: ∀n. S n - n = S O.
naxiom ad_hoc17: ∀a,b,c,d,d'. a+c+d=b+c+d' → a+d=b+d'.
naxiom split_big_plus:
  ∀n,m,f. m ≤ n →
   big_plus n f = big_plus m (λi,p.f i ?) + big_plus (n - m) (λi.λp.f (i + m) ?).
 nelim daemon.
nqed.
naxiom big_plus_preserves_ext:
 ∀n,f,f'. (∀i,p. f i p = f' i p) → big_plus n f = big_plus n f'.

ntheorem iso_nat_nat_union_char:
 ∀n:nat. ∀s: nat → nat. ∀m:nat. m < big_plus (S n) (λi.λ_.s i) →
  let p ≝ iso_nat_nat_union s m n in
   m = big_plus (n - fst … p) (λi.λ_.s (S (i + fst … p))) + snd … p ∧
    fst … p ≤ n ∧ snd … p < s (fst … p).
 #n; #s; nelim n
  [ #m; nwhd in ⊢ (??% → let p ≝ % in ?); nwhd in ⊢ (??(??%) → ?);
    nrewrite > (plus_n_O (s O)); #H; nrewrite > (ltb_t … H); nnormalize; @; /2/
##| #n'; #Hrec; #m; nwhd in ⊢ (??% → let p ≝ % in ?); #H;
    ncases (ltb_cases m (s (S n'))); *; #H1; #H2; nrewrite > H2;
    nwhd in ⊢ (let p ≝ % in ?); nwhd
     [ napply conj [napply conj; //;
       nwhd in ⊢ (???(?(?%(λ_.λ_:(??%).?))%)); nrewrite > (minus_canc n'); //
   ##| nnormalize; // ]
##| nchange in H with (m < s (S n') + big_plus (S n') (λi.λ_.s i));
    nlapply (Hrec (m - s (S n')) ?); /2/; *; *; #Hrec1; #Hrec2; #Hrec3; @; //; @; /2/;
    nrewrite > (split_big_plus …); ##[##2:napply ad_hoc11;##|##3:##skip]
    nrewrite > (ad_hoc12 …); //;
    nwhd in ⊢ (???(?(??%)?));
    nrewrite > (ad_hoc13 …); //;
    napply ad_hoc14; /2/;
    nwhd in ⊢ (???(?(??%)?));
    nrewrite > (plus_n_O …); // ##]##]
nqed.

ntheorem iso_nat_nat_union_pre:
 ∀n:nat. ∀s: nat → nat.
  ∀i1,i2. i1 ≤ n → i2 < s i1 →
   big_plus (n - i1) (λi.λ_.s (S (i + i1))) + i2 < big_plus (S n) (λi.λ_.s i).
/2/. nqed.
    
ntheorem iso_nat_nat_union_uniq:
 ∀n:nat. ∀s: nat → nat.
  ∀i1,i1',i2,i2'. i1 ≤ n → i1' ≤ n → i2 < s i1 → i2' < s i1' →
   big_plus (n - i1) (λi.λ_.s (S (i + i1))) + i2 = big_plus (n - i1') (λi.λ_.s (S (i + i1'))) + i2' →
    i1 = i1' ∧ i2 = i2'.
 #n; #s; #i1; #i1'; #i2; #i2'; #H1; #H1'; #H2; #H2'; #E;
 nelim daemon.
nqed.

nlemma partition_splits_card:
 ∀A. ∀P:partition A. ∀n,s.
  ∀f:isomorphism ?? (Nat_ n) (indexes ? P).
   (∀i. isomorphism ?? (Nat_ (s i)) (class ? P (iso_f ???? f i))) →
    (isomorphism ?? (Nat_ (big_plus n (λi.λ_.s i))) (Full_set A)).
#A; #P; #Sn; ncases Sn
  [ #s; #f; #fi;
    nlapply (covers ? P); *; #_; #H;
    (*
    nlapply
     (big_union_preserves_iso ??? (indexes A P) (Nat_ O) (λx.class ? P x) f);
     *; #K; #_; nwhd in K: (? → ? → %);*)
    nelim daemon (* impossibile *)
  | #n; #s; #f; #fi; @
  [ @
     [ napply (λm.let p ≝ (iso_nat_nat_union s m n) in iso_f ???? (fi (fst … p)) (snd … p))
     | #a; #a'; #H; nrewrite < H; napply refl ]
##| #x; #Hx; nwhd; napply I
##| #y; #_;
    nlapply (covers ? P); *; #_; #Hc;
    nlapply (Hc y I); *; #index; *; #Hi1; #Hi2;
    nlapply (f_sur ???? f ? Hi1); *; #nindex; *; #Hni1; #Hni2;
    nlapply (f_sur ???? (fi nindex) y ?)
     [ alias symbol "refl" (instance 3) = "refl".
alias symbol "prop2" (instance 2) = "prop21".
alias symbol "prop1" (instance 4) = "prop11".
napply (. #‡(†?));##[##2: napply Hni2 |##1: ##skip | nassumption]##]
    *; #nindex2; *; #Hni21; #Hni22;
    nletin xxx ≝ (plus (big_plus (minus n nindex) (λi.λ_.s (S (plus i nindex)))) nindex2);
    @ xxx; @
     [ napply iso_nat_nat_union_pre [ napply le_S_S_to_le; nassumption | nassumption ]
   ##| nwhd in ⊢ (???%%); napply (.= ?) [##3: nassumption|##skip]
       nlapply (iso_nat_nat_union_char n s xxx ?)
        [napply iso_nat_nat_union_pre [ napply le_S_S_to_le; nassumption | nassumption]##]
       *; *; #K1; #K2; #K3;
       nlapply
        (iso_nat_nat_union_uniq n s nindex (fst … (iso_nat_nat_union s xxx n))
          nindex2 (snd … (iso_nat_nat_union s xxx n)) ?????); /2/
        [##2: *; #E1; #E2; nrewrite > E1; nrewrite > E2; //
        | nassumption ]##]
##| #x; #x'; nnormalize in ⊢ (? → ? → %); #Hx; #Hx'; #E;
    ncut(∀i1,i2,i1',i2'. i1 ∈ Nat_ (S n) → i1' ∈ Nat_ (S n) → i2 ∈ Nat_ (s i1) → i2' ∈ Nat_ (s i1') → eq_rel (carr A) (eq A) (fi i1 i2) (fi i1' i2') → i1=i1' ∧ i2=i2');
    ##[ #i1; #i2; #i1'; #i2'; #Hi1; #Hi1'; #Hi2; #Hi2'; #E;
       nlapply(disjoint … P (f i1) (f i1') ???)
       [##2,3: napply f_closed; //
       |##1: @ (fi i1 i2); @;
         ##[ napply f_closed; // ##| alias symbol "refl" = "refl1".
napply (. E‡#);
             nwhd; napply f_closed; //]##]
      #E'; ncut(i1 = i1'); ##[ napply (f_inj … E'); // ##]
      #E''; nrewrite < E''; @; //;
      nrewrite < E'' in E; #E'''; napply (f_inj … E'''); //;
      nrewrite > E''; // ]##]
   ##] #K;
    nelim (iso_nat_nat_union_char n s x Hx); *; #i1x; #i2x; #i3x;
    nelim (iso_nat_nat_union_char n s x' Hx'); *; #i1x'; #i2x'; #i3x';
    nlapply (K … E)  
     [##1,2: nassumption;
     ##|##3,4:napply le_to_le_S_S; nassumption; ##]
    *; #K1; #K2;
    napply (eq_rect_CProp0_r ?? (λX.λ_.? = X) ?? i1x');
    napply (eq_rect_CProp0_r ?? (λX.λ_.X = ?) ?? i1x);
    nrewrite > K1; nrewrite > K2; napply refl.
nqed.

(************** equivalence relations vs partitions **********************)

ndefinition partition_of_compatible_equivalence_relation:
 ∀A:setoid. compatible_equivalence_relation A → partition A.
 #A; #R; napply mk_partition
  [ napply (quotient ? R)
  | napply Full_set
  | napply mk_unary_morphism1
     [ #a; napply mk_ext_powerclass
        [ napply {x | R x a}
        | #x; #x'; #H; nnormalize; napply mk_iff; #K; nelim daemon]
   ##| #a; #a'; #H; napply conj; #x; nnormalize; #K [ nelim daemon | nelim daemon]##]
##| #x; #_; nnormalize; /3/
  | #x; #x'; #_; #_; nnormalize; *; #x''; *; /3/
  | nnormalize; napply conj; /4/ ]
nqed.