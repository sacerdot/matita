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

naxiom Q: Type[0].
naxiom nat_to_Q: nat → Q.
ncoercion nat_to_Q : ∀x:nat.Q ≝ nat_to_Q on _x:nat to Q.
ndefinition bool_to_nat ≝ λb. match b with [ true ⇒ 1 | false ⇒ 0 ].
ncoercion bool_to_nat : ∀b:bool.nat ≝ bool_to_nat on _b:bool to nat.
naxiom Qplus: Q → Q → Q.
naxiom Qminus: Q → Q → Q.
naxiom Qtimes: Q → Q → Q.
naxiom Qdivides: Q → Q → Q.
naxiom Qle : Q → Q → Prop.
naxiom Qlt: Q → Q → Prop.
naxiom Qmin: Q → Q → Q.
naxiom Qmax: Q → Q → Q.
interpretation "Q plus" 'plus x y = (Qplus x y).
interpretation "Q minus" 'minus x y = (Qminus x y).
interpretation "Q times" 'times x y = (Qtimes x y).
interpretation "Q divides" 'divide x y = (Qdivides x y).
interpretation "Q le" 'leq x y = (Qle x y).
interpretation "Q lt" 'lt x y = (Qlt x y).
naxiom Qtimes_plus: ∀n,m:nat.∀q:Q. (n * q + m * q) = (plus n m) * q.
naxiom Qmult_one: ∀q:Q. 1 * q = q.
naxiom Qdivides_mult: ∀q1,q2. (q1 * q2) / q1 = q2.
naxiom Qtimes_distr: ∀q1,q2,q3:Q.(q3 * q1 + q3 * q2) = q3 * (q1 + q2).
naxiom Qdivides_distr: ∀q1,q2,q3:Q.(q1 / q3 + q2 / q3) = (q1 + q2) / q3.
naxiom Qplus_comm: ∀q1,q2. q1 + q2 = q2 + q1.
naxiom Qplus_assoc: ∀q1,q2,q3. q1 + q2 + q3 = q1 + (q2 + q3).
ntheorem Qplus_assoc1: ∀q1,q2,q3. q1 + q2 + q3 = q3 + q2 + q1.
#a; #b; #c; //; nqed.
naxiom Qle_refl: ∀q1. q1≤q1.
naxiom Qle_trans: ∀x,y,z. x≤y → y≤z → x≤z.
naxiom Qlt_trans: ∀x,y,z. x < y → y < z → x < z.
naxiom Qle_lt_trans1: ∀x,y,z. x ≤ y → y < z → x < z.
naxiom Qle_lt_trans2: ∀x,y,z. x < y → y ≤ z → x < z.
naxiom Qle_plus_compat: ∀x,y,z,t. x≤y → z≤t → x+z ≤ y+t.
naxiom Qmult_zero: ∀q:Q. 0 * q = 0.

naxiom phi: Q. (* the golden number *)
naxiom golden: phi = phi * phi + phi * phi * phi.

(* naxiom Ndivides_mult: ∀n:nat.∀q. (n * q) / n = q. *)

ntheorem lem1: ∀n:nat.∀q:Q. (n * q + q) = (S n) * q.
#n; #q; ncut (plus n 1 = S n);##[//##]
//; nqed.

ntheorem Qplus_zero: ∀q:Q. 0 + q = q. //. nqed.

ncoinductive locate : Q → Q → Prop ≝
   L: ∀l,u. locate l ((1 - phi) * l + phi * u) → locate l u
 | H: ∀l,u. locate (phi * l + (1 - phi) * u) u → locate l u.

ndefinition locate_inv_ind':
 ∀l,u:Q.∀P:Q → Q → Prop.
  ∀H1: locate l ((1 - phi) * l + phi * u) → P l u. 
  ∀H2: locate (phi * l + (1 - phi) * u) u → P l u.
   locate l u → P l u.
 #l; #u; #P; #H1; #H2; #p; ninversion p; #l; #u; #H; #E1; #E2;
 ndestruct; /2/.
nqed.

ndefinition R ≝ ∃l,u:Q. locate l u.

(*
nlet corec Q_to_locate q : locate q q ≝ L q q … (Q_to_locate q).
  //; nrewrite < (Qdivides_mult 3 q) in ⊢ (? % ?); //.
nqed.

ndefinition Q_to_R : Q → R.
 #q; @ q; @q; //.
nqed.
*)

nlemma help_auto1: ∀q:Q. false * q = 0. #q; nnormalize; //. nqed.

(*
nlet corec locate_add (l,u:?) (r1,r2: locate l u) (c1,c2:bool) :
 locate (l + l + c1 * phi + c2 * phi * phi) (u + u + c1 * phi + c2 * phi * phi) ≝ ?.
 napply (locate_inv_ind' … r1); napply (locate_inv_ind' … r2);
 #r2'; #r1'; ncases c1; ncases c2
  [ ##4: nnormalize; @1;
    nlapply (locate_add … r1' r2' false false); nnormalize;
    nrewrite > (Qmult_zero …); nrewrite > (Qmult_zero …); #K; nauto demod;
     #K;
    nnormalize in K; nrewrite > (Qmult_zero …) in K; nnormalize; #K;
    napplyS K;
     


 
  [ ##1,4: ##[ @1 ? (l1'+l2') (u1'+u2') | @2 ? (l1'+l2') (u1'+u2') ]
    ##[ ##1,5: /2/ | napplyS (Qle_plus_compat …leq1u leq2u) |
        ##4: napplyS (Qle_plus_compat …leq1l leq2l)
      |##*: /2/ ]
 ##| ninversion r2; #l2''; #u2''; #leq2l'; #leq2u'; #r2';
     ninversion r1; #l1''; #u1''; #leq1l'; #leq1u'; #r1';
      ##[ @1 ? (l1''+l2'') (u1''+u2''); 
      ##[ napply Qle_plus_compat; /3/;
        ##| ##3: /2/;
        ##| napplyS (Qle_plus_compat …leq1u' leq2u');

(*
nlet corec locate_add (l1,u1:?) (r1: locate l1 u1) (l2,u2:?) (r2: locate l2 u2) :
 locate (l1 + l2) (u1 + u2) ≝ ?.
 napply (locate_inv_ind' … r1); napply (locate_inv_ind' … r2); #l2'; #u2'; #leq2l; #leq2u; #r2;
 #l1'; #u1'; #leq1l; #leq1u; #r1
  [ ##1,4: ##[ @1 ? (l1'+l2') (u1'+u2') | @2 ? (l1'+l2') (u1'+u2') ]
    ##[ ##1,5: /2/ | napplyS (Qle_plus_compat …leq1u leq2u) |
        ##4: napplyS (Qle_plus_compat …leq1l leq2l)
      |##*: /2/ ]
 ##| ninversion r2; #l2''; #u2''; #leq2l'; #leq2u'; #r2';
     ninversion r1; #l1''; #u1''; #leq1l'; #leq1u'; #r1';
      ##[ @1 ? (l1''+l2'') (u1''+u2''); 
      ##[ napply Qle_plus_compat; /3/;
        ##| ##3: /2/;
        ##| napplyS (Qle_plus_compat …leq1u' leq2u');
      .
 
nlet corec apart (l1,u1) (r1: locate l1 u1) (l2,u2) (r2: locate l2 u2) : CProp[0] ≝
 match disjoint l1 u1 l2 u2 with
  [ true ⇒ True
  | false ⇒ 
*)
*)

include "topology/igft.ma".
include "datatypes/pairs.ma".
include "datatypes/sums.ma".

nrecord pre_order (A: Type[0]) : Type[1] ≝
 { pre_r :2> A → A → CProp[0];
   pre_refl: reflexive … pre_r;
   pre_trans: transitive … pre_r
 }.

nrecord Ax_pro : Type[1] ≝
 { AAx :> Ax;
   Aleq: pre_order AAx
 }.

interpretation "Ax_pro leq" 'leq x y = (pre_r ? (Aleq ?) x y).

(*CSC: per auto per sotto, ma non sembra aiutare *)
nlemma And_elim1: ∀A,B. A ∧ B → A.
 #A; #B; *; //.
nqed.

nlemma And_elim2: ∀A,B. A ∧ B → B.
 #A; #B; *; //.
nqed.
(*CSC: /fine per auto per sotto *)

ndefinition Rax : Ax_pro.
 @
  [ @ (Q × Q)
    [ #p; napply (unit + sigma … (λc. fst … p < fst … c ∧ fst … c < snd … c ∧ snd … c < snd … p))
    | #c; *
      [ #_; napply {c' | fst … c < fst … c' ∧ snd … c' < snd … c}
      | *; #c'; #_; napply {d' | fst … d' = fst … c  ∧ snd … d' = fst … c'
                               ∨ fst … d' = snd … c' ∧ snd … d' = snd … c } ]##]
##| @ (λc,d. fst … d ≤ fst … c ∧ snd … c ≤ snd … d)
     [ /2/
     | nnormalize; #z; #x; #y; *; #H1; #H2; *; /3/; (*CSC: perche' non va? *) ##]
nqed.

ndefinition downarrow: ∀S:Ax_pro. Ω \sup S → Ω \sup S ≝
 λS:Ax_pro.λU:Ω ^S.{a | ∃b:S. b ∈ U ∧ a ≤ b}.

interpretation "downarrow" 'downarrow a = (downarrow ? a).

ndefinition fintersects: ∀S:Ax_pro. Ω \sup S → Ω \sup S → Ω \sup S ≝
 λS.λU,V. ↓U ∩ ↓V.

interpretation "fintersects" 'fintersects U V = (fintersects ? U V).

ndefinition singleton ≝ λA.λa:A.{b | b=a}.

interpretation "singleton" 'singl a = (singleton ? a).

ninductive ftcover (A : Ax_pro) (U : Ω^A) : A → CProp[0] ≝
| ftreflexivity : ∀a. a ∈ U → ftcover A U a
| ftleqinfinity : ∀a,b. a ≤ b → ∀i. (∀x. x ∈ 𝐂 b i ↓ (singleton … a) → ftcover A U x) → ftcover A U a
| ftleqleft     : ∀a,b. a ≤ b → ftcover A U b → ftcover A U a.

interpretation "ftcovers" 'covers a U = (ftcover ? U a).

ntheorem ftinfinity: ∀A: Ax_pro. ∀U: Ω^A. ∀a. ∀i. (∀x. x ∈ 𝐂 a i → x ◃ U) → a ◃ U.
 #A; #U; #a; #i; #H;
 napply (ftleqinfinity … a … i); //;
 #b; *; *; #b; *; #H1; #H2; #H3; napply (ftleqleft … b); //;
 napply H; napply H1 (*CSC: auto non va! *).
nqed.

ncoinductive ftfish (A : Ax_pro) (F : Ω^A) : A → CProp[0] ≝
| ftfish : ∀a.
    a ∈ F →
    (∀b. a ≤ b → ftfish A F b) →
    (∀b. a ≤ b → ∀i:𝐈 b. ∃x.  x ∈ 𝐂 b i ↓ (singleton … a) ∧ ftfish A F x) →
    ftfish A F a.

interpretation "fish" 'fish a U = (ftfish ? U a).

nlemma ftcoreflexivity: ∀A: Ax_pro.∀F.∀a:A. a ⋉ F → a ∈ F.
 #A; #F; #a; #H; ncases H; //.
nqed.

nlemma ftcoleqinfinity:
 ∀A: Ax_pro.∀F.∀a:A. a ⋉ F →
  ∀b. (a ≤ b → ∀i. (∃x. x ∈ 𝐂 b i ↓ (singleton … a) ∧ x ⋉ F)).
 #A; #F; #a; #H; ncases H; /2/.
nqed.

nlemma ftcoleqleft:
 ∀A: Ax_pro.∀F.∀a:A. a ⋉ F →
  (∀b. a ≤ b → b ⋉ F).
 #A; #F; #a; #H; ncases H; /2/.
nqed.

alias symbol "I" (instance 7) = "I".
alias symbol "I" (instance 18) = "I".
alias symbol "I" (instance 18) = "I".
alias symbol "I" (instance 18) = "I".
nlet corec ftfish_coind
 (A: Ax_pro) (F: Ω^A) (P: A → CProp[0])
 (Hcorefl: ∀a. P a → a ∈ F)
 (Hcoleqleft: ∀a. P a → ∀b. a ≤ b → P b)
 (Hcoleqinfinity: ∀a. P a → ∀b. a ≤ b → ∀i:𝐈 b. ∃x. x ∈ 𝐂 b i ↓ (singleton … a) ∧ P x)
: ∀a:A. P a → a ⋉ F ≝ ?.
 #a; #H; @
  [ /2/
  | #b; #H; napply (ftfish_coind … Hcorefl Hcoleqleft Hcoleqinfinity); /2/
  | #b; #H1; #i; ncases (Hcoleqinfinity a H ? H1 i); #x; *; #H2; #H3;
    @ x; @; //; napply (ftfish_coind … Hcorefl Hcoleqleft Hcoleqinfinity); //]
nqed.

(*CSC: non serve manco questo (vedi sotto) *)
nlemma auto_hint3: ∀A. S__o__AAx A = S (AAx A).
 #A; //.
nqed.

alias symbol "I" (instance 6) = "I".
ntheorem ftcoinfinity: ∀A: Ax_pro. ∀F: Ω^A. ∀a. a ⋉ F → (∀i: 𝐈 a. ∃b. b ∈ 𝐂 a i ∧ b ⋉ F).
 #A; #F; #a; #H; #i; nlapply (ftcoleqinfinity … F … a … i); //; #H;
 ncases H; #c; *; *; *; #b; *; #H1; #H2; #H3; #H4; @ b; @ [ napply H1 (*CSC: auto non va *)]
 napply (ftcoleqleft … c); //.
nqed.

nrecord Pt (A: Ax_pro) : Type[1] ≝
 { pt_set: Ω^A;
   pt_inhabited: ∃a. a ∈ pt_set;
   pt_filtering: ∀a,b. a ∈ pt_set → b ∈ pt_set → ∃c. c ∈ (singleton … a) ↓ (singleton … b) → c ∈ pt_set;
   pt_closed: pt_set ⊆ {b | b ⋉ pt_set}   
 }.

ndefinition Rd ≝ Pt Rax.

naxiom daemon: False.

ndefinition Q_to_R: Q → Rd.
 #q; @
  [ napply { c | fst … c < q ∧ q < snd … c  }
  | @ [ @ (Qminus q 1) (Qplus q 1) | ncases daemon ]
##| #c; #d; #Hc; #Hd; @ [ @ (Qmin (fst … c) (fst … d)) (Qmax (snd … c) (snd … d)) | ncases daemon]
##| #a; #H; napply (ftfish_coind Rax ? (λa. fst … a < q ∧ q < snd … a)); /2/
    [ /5/ | #b; *; #H1; #H2; #c; *; #H3; #H4; #i; ncases i
      [ #w; nnormalize;
    ##| nnormalize;
  ]
nqed.

