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

include "arithmetics/nat.ma".
include "datatypes/bool.ma".

ndefinition two ≝ S (S O).
ndefinition natone ≝ S O.
ndefinition four ≝ two * two.
ndefinition eight ≝ two * four.
ndefinition natS ≝ S.

include "topology/igft.ma".

nlemma hint_auto2 : ∀T.∀U,V:Ω^T.(∀x.x ∈ U → x ∈ V) → U ⊆ V./2/.nqed.

ninductive Sigma (A: Type[0]) (P: A → CProp[0]) : Type[0] ≝
 mk_Sigma: ∀a:A. P a → Sigma A P.

(*<< To be moved in igft.ma *)
ninductive ncover (A : nAx) (U : Ω^A) : A → CProp[0] ≝
| ncreflexivity : ∀a. a ∈ U → ncover A U a
| ncinfinity    : ∀a. ∀i. (∀y.Sigma ? (λj.y = 𝐝 a i j) → ncover A U y) → ncover A U a.

interpretation "ncovers" 'covers a U = (ncover ? U a).

ntheorem ncover_cover_ok: ∀A:nAx.∀U.∀a:A. a ◃ U → cover (Ax_of_nAx A) U a.
 #A; #U; #a; #H; nelim H
  [ #n; #H1; @1; nassumption
  | #a; #i; #IH; #H; @2 [ napply i ]
    nnormalize; #y; *; #j; #E; nrewrite > E;
    napply H;
    /2/ ]
nqed.

ntheorem cover_ncover_ok: ∀A:Ax.∀U.∀a:A. a ◃ U → ncover (nAx_of_Ax A) U a.
 #A; #U; #a; #H; nelim H
  [ #n; #H1; @1; nassumption
  | #a; #i; #IH; #H; @2 [ napply i ] #y; *; #j; #E; nrewrite > E; ncases j; #x; #K;
    napply H; nnormalize; //.
nqed.

ndefinition ncoverage : ∀A:nAx.∀U:Ω^A.Ω^A ≝ λA,U.{ a | a ◃ U }.

interpretation "ncoverage cover" 'coverage U = (ncoverage ? U).

(*>> To be moved in igft.ma *)

(*XXX
nlemma ncover_ind':
 ∀A:nAx.∀U,P:Ω^A.
   (U ⊆ P) → (∀a:A.∀i:𝐈 a.(∀j. 𝐝 a i j ◃ U) → (∀j. 𝐝 a i j ∈ P) → a ∈ P) →
    ◃ U ⊆ P.
 #A; #U; #P; #refl; #infty; #a; #H; nelim H
  [ // | #b; #j; #K1; #K2; napply infty; //; ##] 
nqed.

alias symbol "covers" (instance 3) = "ncovers".
nlemma cover_ind'':
 ∀A:nAx.∀U:Ω^A.∀P:A → CProp[0].
  (∀a. a ∈ U → P a) → (∀a:A.∀i:𝐈 a.(∀j. 𝐝 a i j ◃ U) → (∀j. P (𝐝 a i j)) → P a) →
   ∀b. b ◃ U → P b.
 #A; #U; #P; nletin V ≝ {x | P x}; napply (ncover_ind' … V).
nqed.
*)

(*********** from Cantor **********)
ninductive eq1 (A : Type[0]) : Type[0] → CProp[0] ≝
| refl1 : eq1 A A.

notation "hvbox( a break ∼ b)" non associative with precedence 40
for @{ 'eqT $a $b }.

interpretation "eq between types" 'eqT a b = (eq1 a b).

ninductive unit : Type[0] ≝ one : unit.

ninductive option (A: Type[0]) : Type[0] ≝
   None: option A
 | Some: A → option A
 | Twice: A → A → option A.

nrecord uuAx : Type[1] ≝ {
  uuS : Type[0];
  uuC : uuS → option uuS
}.

ndefinition uuax : uuAx → nAx.
#A; @ (uuS A)
  [ #a; napply unit
##| #a; ncases (uuC … a); nnormalize
     [ #_; napply False
     | #_; #_; napply unit
     | #_; #_; #_; napply bool ]
##| #a; ncases (uuC … a); nnormalize
     [ #_; #H; napply (False_rect_Type1 … H)
     | #b; #_; #_; napply b
     | #b1; #b2; #_; * [ napply b1 | napply b2]##]##]
nqed.

ncoercion uuax : ∀u:uuAx. nAx ≝ uuax on _u : uuAx to nAx.

nlemma eq_rect_Type0_r':
 ∀A.∀a,x.∀p:eq ? x a.∀P: ∀x:A. eq ? x a → Type[0]. P a (refl A a) → P x p.
 #A; #a; #x; #p; ncases p; //;
nqed.

nlemma eq_rect_Type0_r:
 ∀A.∀a.∀P: ∀x:A. eq ? x a → Type[0]. P a (refl A a) → ∀x.∀p:eq ? x a.P x p.
 #A; #a; #P; #p; #x0; #p0; napply (eq_rect_Type0_r' ??? p0); //.
nqed.

nrecord memdec (A: Type[0]) (U:Ω^A) : Type[0] ≝
 { decide_mem:> A → bool;
   decide_mem_ok: ∀x. decide_mem x = true → x ∈ U;
   decide_mem_ko: ∀x. decide_mem x = false → ¬ (x ∈ U)
 }.

(*********** end from Cantor ********)

nlemma csc_sym_eq: ∀A,x,y. eq A x y → eq A y x.
 #A; #x; #y; #H; ncases H; @1.
nqed.

nlemma csc_eq_rect_CProp0_r':
 ∀A.∀a,x.∀p:eq ? x a.∀P: ∀x:A. CProp[0]. P a → P x.
 #A; #a; #x; #p; #P; #H;
 napply (match csc_sym_eq ??? p return λa.λ_.P a with [ refl ⇒ H ]).
nqed.
 
nlet rec cover_rect
 (A:uuAx) (U:Ω^(uuax A)) (memdec: memdec … U) (P:uuax A → Type[0])
  (refl: ∀a:uuax A. a ∈ U → P a)
  (infty: ∀a:uuax A.∀i: 𝐈 a.(∀j. 𝐝 a i j ◃ U) → (∀j.P (𝐝 a i j)) → P a)
   (b:uuax A) (p: b ◃ U) on p : P b
≝ ?.
 nlapply (decide_mem_ok … memdec b); nlapply (decide_mem_ko … memdec b);
 ncases (decide_mem … memdec b)
  [ #_; #H; napply refl; /2/
  | #H; #_; ncut (uuC … b=uuC … b) [//] ncases (uuC … b) in ⊢ (???% → ?)
    [ #E;
      nlapply (infty b); nnormalize; nrewrite > E; nnormalize; #H2;
      napply (H2 one); #y; nelim y
  ##| #a; #E;
      ncut (a ◃ U)
       [ nlapply E; nlapply (H ?); //; ncases p
          [ #x; #Hx; #K1; #_; ncases (K1 Hx)  
        ##| #x; #i; #Hx; #K1; #E2; napply Hx; ngeneralize in match i; nnormalize;
            nrewrite > E2; nnormalize; /2/ ]##]
      #Hcut;
      nlapply (infty b); nnormalize; nrewrite > E; nnormalize; #H2;
      napply (H2 one); #y
       [ napply Hcut
     ##| napply (cover_rect A U memdec P refl infty a); // ]
  ##| #a; #a1; #E;
      ncut (a ◃ U)
       [ nlapply E; nlapply (H ?) [//] ncases p
          [ #x; #Hx; #K1; #_; ncases (K1 Hx)
        ##| #x; #i; #Hx; #K1; #E2; napply Hx; ngeneralize in match i; nnormalize;
            nrewrite > E2; nnormalize; #_; @1 (true); /2/ ]##]
      #Hcut;
      ncut (a1 ◃ U)
       [ nlapply E; nlapply (H ?) [//] ncases p
          [ #x; #Hx; #K1; #_; ncases (K1 Hx)
        ##| #x; #i; #Hx; #K1; #E2; napply Hx; ngeneralize in match i; nnormalize;
            nrewrite > E2; nnormalize; #_; @1 (false); /2/ ]##]
      #Hcut1;
      nlapply (infty b); nnormalize; nrewrite > E; nnormalize; #H2;
      napply (H2 one); #y; ncases y; nnormalize
       [##1,2: nassumption
       | napply (cover_rect A U memdec P refl infty a); //
       | napply (cover_rect A U memdec P refl infty a1); //]
nqed.

(********* Esempio:
   let rec skip n =
     match n with
      [ O ⇒ 1
      | S m ⇒
         match m with
          [ O ⇒ skipfact O
          | S _ ⇒ S m * skipfact (pred m) * skipfact (pred m) ]]
**)

ntheorem psym_plus: ∀n,m. n + m = m + n.//.
nqed.

nlemma easy1: ∀n:nat. two * (S n) = two + two * n.//.
nqed.

ndefinition skipfact_dom: uuAx.
 @ nat; #n; ncases n [ napply None | #m; ncases m [ napply (Some … O) | #_; napply (Twice … (pred m) (pred m)) ]
nqed.

ntheorem skipfact_base_dec:
 memdec (uuax skipfact_dom) (mk_powerclass ? (λx: uuax skipfact_dom. False)).
 nnormalize; @ (λ_.false); //. #_; #H; ndestruct.
nqed.

ntheorem skipfact_partial:
 ∀n: uuax skipfact_dom. two * n ◃ mk_powerclass ? (λx: uuax skipfact_dom.False).
 #n; nelim n
  [ @2; nnormalize; //; #y; *; #a; ncases a
  |
 #m; nelim m; nnormalize
     [ #H; @2; nnormalize; //;
       #y; *; #a; #E; nrewrite > E; ncases a; nnormalize; //
   ##| #p; #H1; #H2; @2; nnormalize; //;
       #y; *; #a; #E; nrewrite > E; ncases a; nnormalize;
       nrewrite < (plus_n_Sm …); // ]
nqed.

ndefinition skipfact: ∀n:nat. n ◃ mk_powerclass ? (λx: uuax skipfact_dom.False) → nat.
 #n; #D; napply (cover_rect … skipfact_base_dec … n D)
  [ #a; #H; nelim H
  | #a; ncases a
    [ nnormalize; #i; #_; #_; napply natone
    | #m; ncases m
       [ nnormalize; #_; #_; #H; napply H; @1
       | #p; #i; nnormalize in i; #K;
         #H; nnormalize in H;
         napply (S m * H true * H false) ]
nqed.

nlemma test: skipfact four ? = four * two * two. ##[##2: napply (skipfact_partial two)]//.
nqed.