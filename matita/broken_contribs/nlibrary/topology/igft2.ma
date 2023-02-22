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

ndefinition two ≝ S (S O).
ndefinition natone ≝ S O.
ndefinition four ≝ two * two.
ndefinition eight ≝ two * four.
ndefinition natS ≝ S.

include "topology/igft.ma".

nlemma hint_auto2 : ∀T.∀U,V:Ω^T.(∀x.x ∈ U → x ∈ V) → U ⊆ V.
nnormalize; /2/;
nqed.

alias symbol "covers" = "covers set".
alias symbol "coverage" = "coverage cover".
alias symbol "I" = "I".
nlemma cover_ind':
 ∀A:Ax.∀U,P:Ω^A.
   (U ⊆ P) → (∀a:A.∀j:𝐈 a. 𝐂 a j ◃ U → 𝐂 a j ⊆ P → a ∈ P) →
    ◃ U ⊆ P.
 #A; #U; #P; #refl; #infty; #a; #H; nelim H; /3/. 
nqed.

alias symbol "covers" (instance 1) = "covers".
nlemma cover_ind'':
 ∀A:Ax.∀U:Ω^A.∀P:A → CProp[0].
  (∀a. a ∈ U → P a) → (∀a:A.∀j:𝐈 a. 𝐂 a j ◃ U → (∀b. b ∈ 𝐂 a j → P b) → P a) →
   ∀b. b ◃ U → P b.
 #A; #U; #P; nletin V ≝ {x | P x}; napply (cover_ind' … V).
nqed.

(*********** from Cantor **********)
ninductive eq1 (A : Type[0]) : Type[0] → CProp[0] ≝
| refl1 : eq1 A A.

notation "hvbox( a break ∼ b)" non associative with precedence 40
for @{ 'eqT $a $b }.

interpretation "eq between types" 'eqT a b = (eq1 a b).

ninductive unit : Type[0] ≝ one : unit.

ninductive option (A: Type[0]) : Type[0] ≝
   None: option A
 | Some: A → option A.

nrecord uuAx : Type[1] ≝ {
  uuS : Type[0];
  uuC : uuS → option uuS
}.

ndefinition uuax : uuAx → Ax.
#A; @ (uuS A)
  [ #a; ncases (uuC … a) [ napply False | #_; napply unit]
##| #a; ncases (uuC … a)
     [ nnormalize; #H; napply (False_rect_Type1 … H)
     | nnormalize; #b; #_; napply {x | x=b }]##]
nqed.

ncoercion uuax : ∀u:uuAx. Ax ≝ uuax on _u : uuAx to Ax.

nlemma eq_rect_Type0_r':
 ∀A.∀a,x.∀p:eq ? x a.∀P: ∀x:A. eq ? x a → Type[0]. P a (refl A a) → P x p.
 #A; #a; #x; #p; ncases p; //;
nqed.

nlemma eq_rect_Type0_r:
 ∀A.∀a.∀P: ∀x:A. eq ? x a → Type[0]. P a (refl A a) → ∀x.∀p:eq ? x a.P x p.
 #A; #a; #P; #p; #x0; #p0; napply (eq_rect_Type0_r' ??? p0); nassumption.
nqed.

ninductive bool: Type[0] ≝
   true: bool
 | false: bool.

nrecord memdec (A: Type[0]) (U:Ω^A) : Type[0] ≝
 { decide_mem:> A → bool;
   decide_mem_ok: ∀x. decide_mem x = true → x ∈ U;
   decide_mem_ko: ∀x. decide_mem x = false → ¬ (x ∈ U)
 }.

(*********** end from Cantor ********)

alias symbol "covers" (instance 9) = "covers".
alias symbol "covers" (instance 8) = "covers".
nlet rec cover_rect
 (A:uuAx) (U:Ω^(uuax A)) (memdec: memdec … U) (P:uuax A → Type[0])
  (refl: ∀a:uuax A. a ∈ U → P a)
  (infty: ∀a:uuax A.∀i: 𝐈 a. 𝐂 a i ◃ U → (∀b. b ∈ 𝐂 a i → P b) → P a)
   (b:uuax A) (p: b ◃ U) on p : P b
≝ ?.
 nlapply (decide_mem_ok … memdec b); nlapply (decide_mem_ko … memdec b);
 ncases (decide_mem … memdec b)
  [ #_; #H; napply refl; /2/
  | #H; #_; ncut (uuC … b=uuC … b) [//] ncases (uuC … b) in ⊢ (???% → ?)
    [ #E; napply False_rect_Type0; ncut (b=b) [//] ncases p in ⊢ (???% → ?)
      [ #a; #K; #E2; napply H [ // | nrewrite > E2; // ]
    ##| #a; #i; #K; #E2; nrewrite < E2 in i; nnormalize; nrewrite > E; nnormalize;
        //]
  ##| #a; #E;
      ncut (a ◃ U)
       [ nlapply E; nlapply (H ?) [//] ncases p
          [ #x; #Hx; #K1; #_; ncases (K1 Hx)
        ##| #x; #i; #Hx; #K1; #E2; napply Hx; ngeneralize in match i; nnormalize;
            nrewrite > E2; nnormalize; #_; //]##]
      #Hcut; 
      nlapply (infty b); nnormalize; nrewrite > E; nnormalize; #H2;
      napply (H2 one); #y; #E2; nrewrite > E2 
      (* [##2: napply cover_rect] //; *)
       [ napply Hcut
     ##| napply (cover_rect A U memdec P refl infty a); // ]##]
nqed.

(********* Esempio:
   let rec skipfact n =
     match n with
      [ O ⇒ 1
      | S m ⇒ S m * skipfact (pred m) ]
**)

ntheorem psym_plus: ∀n,m. n + m = m + n.//.
nqed.

nlemma easy1: ∀n:nat. two * (S n) = two + two * n.//.
nqed.

ndefinition skipfact_dom: uuAx.
 @ nat; #n; ncases n [ napply None | #m; napply (Some … (pred m)) ]
nqed.

ntheorem skipfact_base_dec:
 memdec (uuax skipfact_dom) (mk_powerclass ? (λx: uuax skipfact_dom. x=O)).
 nnormalize; @ (λx. match x with [ O ⇒ true | S _ ⇒ false ]); #n; nelim n;
  nnormalize; //; #X; ndestruct; #Y; #Z; ndestruct; #W; ndestruct.
nqed.

ntheorem skipfact_partial:
 ∀n: uuax skipfact_dom. two * n ◃ mk_powerclass ? (λx: uuax skipfact_dom.x=O).
 #n; nelim n
  [ @1; nnormalize; @1
  | #m; #H; @2
     [ nnormalize; @1
     | nnormalize; #y; nchange in ⊢ (% → ?) with (y = pred (pred (two * (natone + m))));
       nnormalize; nrewrite < (plus_n_Sm …); nnormalize;
       #E; nrewrite > E; napply H ]##]
nqed.

ndefinition skipfact: ∀n:nat. n ◃ mk_powerclass ? (λx: uuax skipfact_dom.x=O) → nat.
 #n; #D; napply (cover_rect … skipfact_base_dec … n D)
  [ #a; #_; napply natone
  | #a; ncases a
    [ nnormalize; #i; nelim i
    | #m; #i; nnormalize in i; #d; #H;
      napply (S m * H (pred m) …); //]
nqed.

nlemma test: skipfact four ? = eight. ##[##2: napply (skipfact_partial two)] //.
nqed.