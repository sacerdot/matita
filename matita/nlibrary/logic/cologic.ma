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

include "logic/pts.ma".
include "logic/equality.ma".
include "datatypes/bool.ma".

ncoinductive cprop: Type[0] ≝
   certain: bool → cprop
 | maybe: cprop → cprop.

ntheorem ccases:
 ∀c. c = match c with [ certain b ⇒ certain b | maybe c ⇒ maybe c ].
 #c; ncases c; //.
nqed.

ninductive cconv : cprop → cprop → CProp[0] ≝
   certain_certain: ∀b. cconv b b
 | maybe1: ∀c1,c2. cconv c1 c2 → cconv (maybe c1) c2
 | maybe2: ∀c1,c2. cconv c1 c2 → cconv c1 (maybe c2).

nlemma cconv_sym: ∀c,d. cconv c d → cconv d c.
 #c d K; nelim K; /2/.
nqed.

ncoinductive ceq: cprop → cprop → CProp[0] ≝
   maybe_maybe: ∀c,d. ceq c d → ceq (maybe c) (maybe d)
 | certain_maybe: ∀b,c. cconv (certain b) c → ceq (certain b) c
 | maybe_certain: ∀b,c. cconv c (certain b) → ceq c (certain b).

nlet corec ceq_refl c : ceq c c ≝ ?.
 ncases c [ #b; @2; @1 | #d; @1; //]
nqed.

nlet corec ceq_sym c d : ceq c d → ceq d c ≝ ?.
 ncases c; ncases d; #x y K; ninversion K; #a b E1 E2 E3
 [##4,10: @1; napply ceq_sym; napply E1]
 ndestruct [ @2 | @2 | @3 | @2] /2/.
nqed.

nlemma ceq_to_cconv: ∀c,b. ceq c (certain b) → cconv c (certain b).
 #c b K; ninversion K; #; ndestruct; //.
nqed.

nlemma ceq_to_cconv2: ∀c,b. ceq (certain b) c → cconv (certain b) c.
 #c b K; ninversion K; #; ndestruct; //.
nqed.
      
nlet corec cand c1 c2 : cprop ≝
 match c1 with
  [ certain b ⇒ match b with [ false ⇒ certain false | true ⇒ c2 ]
  | maybe c ⇒
     match c2 with
      [ certain b ⇒ match b with [ false ⇒ certain false | true ⇒ maybe c ]
      | maybe d ⇒ maybe (cand c d) ]].

nlemma cand_false: ∀c. cand (certain false) c = certain false.
 #c; ncases c; nrewrite > (ccases (cand …)); //; #d;
 nrewrite > (ccases (cand …)); //.
nqed.

nlemma cand_true: ∀c. cand (certain true) c = c.
 #c; ncases c; nrewrite > (ccases (cand …)); //; #d;
 nrewrite > (ccases (cand …)); //.
nqed.

nlemma cand_truer: ∀c. cand c (certain true) = c.
 #c; ncases c
  [ #b; ncases b; //
  | #d; nrewrite > (ccases (cand …)); // ]
nqed.


ntheorem cand_true: ∀c1,c2. ceq c1 (certain true) → ceq (cand c1 c2) c2.
 #c1 c2 K; ninversion K; #x y E1 E2 E3 [ ndestruct ]
 ##[ nrewrite < E3 in E1; #K1; ninversion K1; #; ndestruct; nrewrite > (cand_true c2);
     //
   | nrewrite < E3 in E1; #K1;
     ncut (∀y,z. cconv y z → z = certain true → ceq (cand y c2) c2); /2/;
     #a b X; nelim X
      [ #e E; nrewrite > E; nrewrite > (cand_true c2); //
      | ncases c2
         [ #bb; ncases bb; #xx yy KK1 KK2 EE;
           ##[ nlapply (KK2 EE); #XX; nrewrite > (cand_truer …) in XX; #YY;
               @3;
               
           ##[ nrewrite > (ccases (cand (maybe xx) (certain true)));
               nnormalize; @3; @2; 

 

ncoinductive cprop: Type[0] ≝
   false: cprop
 | true: cprop
 | hmm: cprop → cprop.

nlet corec cand c1 c2 : cprop ≝
 match c1 with
  [ false ⇒ false
  | true ⇒ c2
  | hmm c ⇒ hmm (cand c c2) ].

nlet corec cor c1 c2 : cprop ≝
 match c1 with
  [ false ⇒ c2
  | true ⇒ true
  | hmm c ⇒ hmm (cor c c2) ].

nlet corec cimpl c1 c2 : cprop ≝
 match c2 with
  [ false ⇒
      match c1 with
       [ false ⇒ true
       | true ⇒ false
       | hmm c ⇒ hmm (cimpl c c2) ]
  | true ⇒ true
  | hmm c ⇒ hmm (cimpl c1 c) ].

include "Plogic/equality.ma".

nlet corec ceq c1 c2 : cprop ≝
 match c1 with
  [ false ⇒
     match c2 with
      [ false ⇒ true
      | true ⇒ false
      | hmm c ⇒ hmm (ceq c1 c) ]
  | true ⇒ c2
  | hmm c ⇒ hmm (ceq c c2) ].

ninductive holds: cprop → Prop ≝
   holds_true: holds true
 | holds_hmm: ∀c. holds c → holds (hmm c).

include "Plogic/connectives.ma".

nlemma ccases1:
 ∀c. holds c →
  match c with
   [ true ⇒ True
   | false ⇒ False
   | hmm c' ⇒ holds c'].
 #c; #H; ninversion H; //.
nqed.

nlemma ccases2:
 ∀c.
 match c with
   [ true ⇒ True
   | false ⇒ False
   | hmm c' ⇒ holds c'] → holds c ≝ ?.
 #c; ncases c; nnormalize; /2/; *.
nqed.

(*CSC: ??? *)
naxiom cimpl1: ∀c. holds (cimpl true c) → holds c.

nlemma ceq1: ∀c. holds c → holds (ceq c true).
 #c H; nelim H; /2/.
nqed.

ncoinductive EQ: cprop → cprop → Prop ≝
   EQ_true: EQ true true
 | EQ_false: EQ false false
 | EQ_hmm1: ∀x,y. EQ x y → EQ (hmm x) y
 | EQ_hmm2: ∀x,y. EQ x y → EQ x (hmm y).

naxiom daemon: False.

nlet corec tech1 x: ∀y. EQ (hmm x) y → EQ x y ≝ ?.
 #y; ncases y
  [##1,2: #X; ninversion X; #; ndestruct; //
  | #c; #X; ninversion X; #; ndestruct; //;
    @4; ncases daemon (* napply tech1; //*) (* BUG GBC??? *)
  ]
nqed.

nlemma Ccases1:
 ∀c,d. EQ c d →
  match c with
   [ true ⇒ EQ true d
   | false ⇒ EQ false d
   | hmm c' ⇒ EQ c' d] ≝ ?.
 #c d H; ninversion H; //;
 #x y H H1 H2; ndestruct; ncases x in H ⊢ %; nnormalize; #; @4; //;
 napply tech1; //.
nqed.

nlemma Ccases2:
 ∀c,d.
  match c with
   [ true ⇒ EQ true d
   | false ⇒ EQ false d
   | hmm c' ⇒ EQ c' d] → EQ c d ≝ ?.
 #c; ncases c; nnormalize; /2/.
nqed.

nlet corec heyting5 x: ∀y. EQ (cimpl (cand x y) x) true ≝ ?.
 #y; napply Ccases2; ncases x; ncases y; nnormalize; /3/
  [ #c; napply heyting5;


nlemma heyting3: ∀x,y. holds (cimpl x (cimpl y x)).
 #x; #y; ncases x; ncases y; /3/; nnormalize
  [ #d; napply ccases2; nnormalize; napply ccases2; nnormalize; 

nlemma heyting1: ∀x,y. holds (cimpl x y) → holds (cimpl y x) → holds (ceq x y).
 #x y; #H; ngeneralize in match (refl … (cimpl x y));
 nelim H in ⊢ (???% → % → %)
  [ #K1; #K2; nrewrite > K1 in K2; #X1;    
 
  napply ccases2; nlapply (ccases1 … H1); nlapply (ccases1 … H2);
 ncases x; ncases y; nnormalize; /2/
  [ #c; #H3 H4; nlapply (cimpl1 … H3); napply ceq1
  | #d; #e; #H3; #H4;  

 ncases x; nnormalize
  [ #y; ncases y; //
  | #y; ncases y; //
     [ #H1; ninversion H1; ##[##1,4: #; ndestruct]
       ##[ ncases (cimpl true false);
    [ ninversion H1; #; ndestruct; 