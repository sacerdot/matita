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

include "Fsub/util.ma".
include "nat/le_arith.ma".
include "nat/lt_arith.ma".

(*** representation of Fsub types ***)  
inductive Typ : Set ≝
  | TVar : nat → Typ          (* type var *)
  | Top : Typ                 (* maximum type *)
  | Arrow : Typ → Typ → Typ   (* functions *) 
  | Forall : Typ → Typ → Typ. (* universal type *)

(* representation of bounds *)

record bound : Set ≝ { 
                          istype : bool;    (* is subtyping bound? *)
                          btype  : Typ      (* type to which the name is bound *)
                     }.

(*** Type Well-Formedness judgement ***)

inductive WFType : list bound → Typ → Prop ≝
  | WFT_TVar : ∀G,n,T.n < length ? G → (nth ? G (mk_bound true Top) n = mk_bound true T) → 
               WFType G (TVar n)
  | WFT_Top : ∀G.WFType G Top
  | WFT_Arrow : ∀G,T,U.WFType G T → WFType G U → WFType G (Arrow T U)
  | WFT_Forall : ∀G,T,U.WFType G T → WFType (mk_bound true T::G) U → 
                 WFType G (Forall T U).

(*** Environment Well-Formedness judgement ***)

inductive WFEnv : list bound → Prop ≝
  | WFE_Empty : WFEnv (nil ?)
  | WFE_cons : ∀B,T,G.WFEnv G → WFType G T → WFEnv (mk_bound B T :: G).
            
let rec lift T h k on T ≝
match T with
[ TVar n ⇒ TVar (match (leb k n) with [true ⇒ n + h | false ⇒ n])
| Top ⇒ Top
| Arrow U V ⇒ Arrow (lift U h k) (lift V h k)
| Forall U V ⇒ Forall (lift U h k) (lift V h (S k))].
            
(*** Subtyping judgement ***)              
inductive JSubtype : list bound → Typ → Typ → Prop ≝
  | SA_Top : ∀G,T.WFEnv G → WFType G T → JSubtype G T Top
  | SA_Refl_TVar : ∀G,n.WFEnv G → WFType G (TVar n) → JSubtype G (TVar n) (TVar n)
  | SA_Trans_TVar : ∀G,n,T,U.n < length ? G → 
                      nth ? G (mk_bound true Top) n = mk_bound true U → 
                      JSubtype G (lift U (S n) O) T → JSubtype G (TVar n) T
  | SA_Arrow : ∀G,S1,S2,T1,T2. JSubtype G T1 S1 → JSubtype G S2 T2 → 
               JSubtype G (Arrow S1 S2) (Arrow T1 T2)
  | SA_All : ∀G,S1,S2,T1,T2. 
             JSubtype G T1 S1 → JSubtype (mk_bound true T1 :: G) S2 T2 →
             JSubtype G (Forall S1 S2) (Forall T1 T2).

notation "hvbox(e ⊢ break ta ⊴  break tb)" 
  non associative with precedence 30 for @{ 'subjudg $e $ta $tb }.  
interpretation "Fsub subtype judgement" 'subjudg e ta tb = (JSubtype e ta tb).

notation > "hvbox(\Forall S.T)" 
  non associative with precedence 65 for @{ 'forall $S $T}.
notation < "hvbox('All' \sub S. break T)" 
  non associative with precedence 65 for @{ 'forall $S $T}.
interpretation "universal type" 'forall S T = (Forall S T).
  
notation "#x" with precedence 79 for @{'tvar $x}.
interpretation "bound tvar" 'tvar x = (TVar x).

notation "⊤" with precedence 90 for @{'toptype}.
interpretation "toptype" 'toptype = Top.

notation "hvbox(s break ⇛ t)"
  right associative with precedence 60 for @{ 'arrow $s $t }.
interpretation "arrow type" 'arrow S T = (Arrow S T).

notation "hvbox(⊴ T)"
  non associative with precedence 65 for @{ 'subtypebound $T }.
interpretation "subtyping bound" 'subtypebound T = (mk_bound true T).  

(****** PROOFS ********)

(*** theorems about lists ***)

let rec flift f k on k ≝ match k with
[ O ⇒ f
| S p ⇒ flift (λn.match n with [ O ⇒ O | S m ⇒ S (f m) ]) p ]. 

let rec perm T f ≝ match T with
[ TVar m ⇒ TVar (f m)
| Top ⇒ Top
| Arrow U V ⇒ Arrow (perm U f) (perm V f)
| Forall U V ⇒ Forall (perm U f) (perm V (flift f 1))].

definition blift : bound → nat → bound ≝ 
λB,n.match B with [ mk_bound b t ⇒ mk_bound b (lift t n O) ].

definition bperm : bound → (nat→nat) → bound ≝
λB,f.match B with [ mk_bound b t ⇒ mk_bound b (perm t f) ].
 
definition incl : list bound → list bound → (nat → nat) → Prop ≝
λG,H,f.injective ?? f → ∀n.n < length ? G → 
  bperm (blift (nth ? G (mk_bound true Top) n) (S n)) f =
  blift (nth ? H (mk_bound true Top) (f n)) (S (f n)).
  
lemma lift_lift : ∀T,n,m,k.lift (lift T n k) m k = lift T (n+m) k.
intros 3;elim T;simplify;
[apply (leb_elim k n1);intros;simplify;
 [apply leb_elim;intros;simplify;
  [apply eq_f;rewrite < assoc_plus;reflexivity
  |elim H1;autobatch]
 |rewrite > lt_to_leb_false
  [simplify;reflexivity
  |autobatch]]
|*:autobatch]
qed.

lemma lift_O : ∀T,k.lift T O k = T.
intro;elim T;simplify
[cases (leb k n);simplify;autobatch paramodulation
|*:autobatch]
qed.

lemma flift_flift : ∀h,k,f.flift (flift f h) k = flift f (h+k).
intros 2;elim h;simplify
[reflexivity
|rewrite > H;reflexivity]
qed.

lemma eq_f_g_to_eq_fx_gx : ∀A,B:Type.∀f,g:A → B.∀x.f = g → f x = g x.
intros;rewrite > H;reflexivity;
qed.

lemma flift_S : ∀n,m,f.flift f (S n) (S m) = S (flift f n m).
intros 2;elim n
[reflexivity
|cut (flift f (S (S n1)) (S m) = flift (flift f (S n1)) 1 (S m))
 [rewrite > Hcut;simplify;reflexivity
 |change in match (S (S n1)) with (1 + (S n1));rewrite > sym_plus;
  apply eq_f_g_to_eq_fx_gx;symmetry;apply flift_flift]]
qed.

lemma le_flift : ∀k,n.k ≤ n → ∀f.k ≤ flift f k n.
intro;elim k
[autobatch
|cut (∃p.n1 = S p)
 [elim Hcut;rewrite > H2;rewrite > flift_S;apply le_S_S;apply H;
  rewrite > H2 in H1;autobatch
 |elim H1
  [exists[apply n]
   reflexivity
  |elim H3;exists[apply (S a)]
   apply eq_f;assumption]]]
qed.

lemma le_flift2 : ∀k,n.n < k → ∀f.flift f k n = n.
intro;elim k
[elim (not_le_Sn_O ? H)
|generalize in match H1;cases n1;intros
 [cut (flift f (S n) O = flift (flift f n) 1 O)
  [rewrite > Hcut;reflexivity
  |apply eq_f_g_to_eq_fx_gx;autobatch paramodulation]
 |rewrite > flift_S;apply eq_f;apply H;autobatch]]
qed.

lemma lift_perm : ∀T,n,f,k.perm (lift T (S n) k) (flift f (S k)) = lift (perm (lift T n k) (flift f k)) 1 k.
intros 2;elim T;simplify;
[apply (leb_elim k n1);simplify;intros
 [apply eq_f;change in ⊢ (??(?%??)?) with (flift f 1);
  cut (flift (flift f 1) k (n1+S n) = flift (flift f k) 1 (n1+S n))
  [rewrite > Hcut;rewrite < plus_n_Sm;simplify;
   apply (leb_elim k (flift f k (n1+n)));simplify;intros
   [rewrite > sym_plus in ⊢ (???%);simplify;reflexivity
   |elim H1;elim k in H
    [autobatch
    |apply le_flift;autobatch]]
  |apply eq_f_g_to_eq_fx_gx;autobatch paramodulation]
 |apply eq_f;change in ⊢ (??(?%??)?) with (flift f 1);
  rewrite > le_flift2 [|autobatch]
  apply (leb_elim k (flift f k n1));simplify;intro
  [rewrite > le_flift2 in H1 [|autobatch]
   elim (H H1)
  |symmetry;apply le_flift2;autobatch]]
|reflexivity
|apply eq_f2;change in ⊢ (? ? (? ? (? % ?)) ?) with (flift f 1);
  rewrite > flift_flift;simplify in ⊢ (? ? (? ? (? ? %)) ?);autobatch
|apply eq_f2
 [change in ⊢ (? ? (? ? (? % ?)) ?) with (flift f 1);
  rewrite > flift_flift;simplify in ⊢ (? ? (? ? (? ? %)) ?);autobatch
 |change in ⊢ (??(??%)?) with (flift (flift (flift f 1) k) 1);
  rewrite > flift_flift in ⊢ (??%?);
  rewrite > sym_plus in ⊢ (? ? (? ? (? ? %)) ?);
  rewrite > flift_flift;
  simplify in ⊢ (? ? (? ? (? ? %)) ?);
  rewrite > H1;do 2 apply eq_f_g_to_eq_fx_gx;
  apply eq_f;apply eq_f;
  change in ⊢ (???%) with (flift (flift f k) 1);
  rewrite > flift_flift;rewrite > sym_plus;reflexivity]]
qed.

lemma blift_bperm : ∀B,n,f.bperm (blift B (S n)) (flift f 1) = blift (bperm (blift B n) f) 1.
intros;cases B;simplify;apply eq_f;
change in ⊢ (? ? ? (? (? ? %) ? ?)) with (flift f O);
apply lift_perm;
qed.

definition lifter : nat → nat → nat → nat ≝
 λn,k,m.match (leb k m) with
 [ true ⇒ m+n
 | false ⇒ m ].
 
lemma extensional_perm : ∀T.∀f,g.(∀x.f x = g x) → perm T f = perm T g.
intro;elim T
[4:whd in ⊢ (??%%);cut (∀x.flift f 1 x = flift g 1 x)
 [rewrite > (H f g);
  [rewrite > (H1 (flift f 1) (flift g 1));
   [reflexivity
   |assumption]
  |assumption]
 |intro;simplify;cases x
  [reflexivity
  |simplify;rewrite > H2;reflexivity]]
|*:simplify;autobatch]
qed.

lemma flift_lifter : ∀p,n,m,k.flift (lifter n k) p m = lifter n (k+p) m.
intro;elim p
[simplify;autobatch paramodulation
|change in ⊢ (? ? (? ? % ?) ?) with (1+n);
 rewrite < plus_n_Sm;whd in ⊢ (???%);
 transitivity (flift (flift (lifter n1 k) n) 1 m)
 [apply eq_f_g_to_eq_fx_gx;rewrite > sym_plus;autobatch
 |unfold lifter;simplify;
  change in ⊢ (? ? match ? return ? with [_⇒?|_⇒λ_:?.? (? % ? ?)] ?) with (lifter n1 k);
  cases m
  [simplify;reflexivity
  |simplify;rewrite > H;unfold lifter;cases (leb (k+n) n2);reflexivity]]]
qed.

lemma lift_perm2 : ∀T,n,k.lift T n k = perm T (lifter n k).
intros 2;elim T;simplify
[1,2,3:autobatch
|rewrite < H;change in ⊢ (???(??(??%))) with (flift (lifter n k) 1);
 rewrite > H1;
 rewrite > (extensional_perm ? (lifter n (S k)) (flift (lifter n k) 1))
 [reflexivity
 |intro;symmetry;autobatch]]
qed.

lemma incl_cons : ∀G,H,f,T.injective ?? f → incl G H f → 
                           incl (⊴ T::G) (⊴ perm T f :: H) (flift f 1).
intros;unfold;intros 2;
elim n;
[simplify;change in ⊢ (? ? (? ? (? ? %)) ?) with (flift f 1);
 rewrite > lift_perm;rewrite > lift_O;reflexivity
|simplify in H5;lapply (le_S_S_to_le ?? H5);clear H5;
 simplify in ⊢ (? ? ? (? % ?));
 simplify in ⊢ (? ? (? (? % ?) ?) ?);
 unfold in H2;rewrite > (blift_bperm ? ? f);
 rewrite > (H2 ?? Hletin);
 [cases (nth bound H (mk_bound true Top) (f n1));
  simplify;rewrite > lift_lift;rewrite > sym_plus;
  reflexivity
 |assumption]]
qed.

lemma injective_flift : ∀f,n.injective ?? f → injective ?? (flift f n).
intros;elim n
[simplify;assumption
|change in ⊢ (? ? ? (? ? %)) with (1+n1);rewrite > sym_plus;
 rewrite < flift_flift;unfold;intros 2;
 cases (decidable_eq_nat x 0)
 [rewrite > le_flift2
  [cases (decidable_eq_nat y 0)
   [intro;autobatch paramodulation
   |elim y in H3
    [elim H3;reflexivity
    |simplify in H5;destruct]]
  |rewrite > H2;autobatch]
 |generalize in match H2;cases x
  [intros;elim H3;reflexivity
  |intro;cases y;simplify;intros;destruct;
   rewrite > (H1 ?? Hcut);reflexivity]]]
qed.

lemma injective_lifter : ∀n,k.injective ?? (lifter n k).
intros;unfold;intros;unfold lifter in H;
apply (leb_elim k x);intros;
[rewrite > (le_to_leb_true ?? H1) in H;apply (leb_elim k y);intros;
 [rewrite > (le_to_leb_true ?? H2) in H;simplify in H;
  autobatch
 |lapply (not_le_to_lt ?? H2) as H3;rewrite > (lt_to_leb_false ?? H3) in H;
  simplify in H;rewrite < H in H2;elim H2;autobatch]
|lapply (not_le_to_lt ?? H1) as H2;rewrite > (lt_to_leb_false ?? H2) in H;
 apply (leb_elim k y);intros
 [rewrite > (le_to_leb_true ?? H3) in H;simplify in H;rewrite > H in H1;
  elim H1;autobatch
 |lapply (not_le_to_lt ?? H3) as H4;rewrite > (lt_to_leb_false ?? H4) in H;
  simplify in H;assumption]]
qed.

lemma incl_append : ∀G,H. incl G (H@G) (lifter (length ? H) O).
intros;unfold;intros;
cut (nth ? G (⊴ ⊤) n = nth ? (H@G) (⊴ ⊤) (lifter (length ? H) O n))
[rewrite < Hcut;cases (nth bound G (⊴ ⊤) n);simplify;
 rewrite < lift_perm2;rewrite > lift_lift;reflexivity
|elim H
 [simplify;rewrite < plus_n_O;reflexivity
 |simplify;rewrite < plus_n_Sm;apply H3]] 
qed.

lemma flift_id : ∀m,n.flift (λx.x) m n = n.
intro;elim m
[reflexivity
|change in ⊢ (??(??%?)?) with (1+n);rewrite > sym_plus;
 transitivity (flift (flift (λx.x) n) 1 n1)
 [apply eq_f_g_to_eq_fx_gx;autobatch
 |simplify;generalize in match H;cases n1;intro
  [reflexivity
  |simplify;apply eq_f;apply H1]]]
qed. 

lemma perm_id : ∀T,n.T = perm T (flift (λx.x) n).
intro;elim T;
[1:simplify;rewrite > flift_id;reflexivity
|4:whd in ⊢ (???%);rewrite > flift_flift;rewrite < H1;rewrite < H;reflexivity
|*:simplify;autobatch]
qed.

lemma perm_compose : ∀T,f,g.perm (perm T f) g = perm T (λx.g (f x)).
intro;elim T
[reflexivity
|reflexivity
|simplify;autobatch
|simplify;rewrite > H;
 change in ⊢ (? ? (? ? (? (? ? %) ?)) ?) with (flift f 1);
 change in ⊢ (? ? (? ? (? ? %)) ?) with (flift g 1);
 rewrite > H1;
 change in ⊢ (? ? ? (? ? (? ? %))) with (flift (λx.g (f x)) 1);
 rewrite > (extensional_perm ? (λx.flift g 1 (flift f 1 x)) (flift (λx.g (f x)) 1));
 [reflexivity
 |intros;cases x;simplify;reflexivity]]
qed.

lemma WFT_env_incl : ∀G,T.WFType G T → ∀H,f.injective nat nat f → incl G H f →
                          (∀n. n < length ? G → f n < length ? H) → 
                          WFType H (perm T f).
intros 3;elim H
[simplify;unfold in H5;lapply (H5 H4 n H1);
 cut (∃T.nth ? H3 (mk_bound true Top) (f n) = mk_bound true T)
 [elim Hcut;apply WFT_TVar
  [apply a
  |*:autobatch]
 |rewrite > H2 in Hletin;simplify in Hletin;
  elim (nth bound H3 (mk_bound true Top) (f n)) in Hletin;elim b in H7
  [exists[apply t1]
   reflexivity
  |simplify in H7;destruct]]
|2:simplify;autobatch
|simplify;autobatch width=4 size=9
|simplify;apply WFT_Forall
 [autobatch
 |apply H4
  [change in ⊢ (???%) with (flift f 1);apply injective_flift;assumption
  |change in ⊢ (???%) with (flift f 1);apply incl_cons;assumption
  |intro;cases n;simplify;intros;autobatch depth=4]]]
qed.

lemma WFT_env_incl2: ∀G,T.WFType G T → ∀H.length ? G = length ? H →
(∀n,U.n < length ? G → nth ? G (mk_bound true Top) n = mk_bound true U → 
 ∃V.nth ? H (mk_bound true Top) n = mk_bound true V) →
 WFType H T.
intros 3;elim H
[elim (H5 n t)
 [apply WFT_TVar
  [2:applyS H1
  |3:apply H6]
 |assumption
 |assumption]
|autobatch
|apply WFT_Arrow;autobatch
|apply WFT_Forall;try autobatch;
 apply H4;
 [simplify;autobatch
 |intros;elim n in H8 H9
  [exists[apply t]
   reflexivity
  |elim (H7 n1 U ? H10)
   [exists[apply a]
    assumption
   |apply le_S_S_to_le;apply H9]]]]
qed.

lemma WFT_extends : ∀G,H,U,P,T.WFType (G@(mk_bound true U::H)) T → WFType (G@(mk_bound true P::H)) T.
intros;apply (WFT_env_incl2 ?? H1)
[elim G;simplify
 [reflexivity
 |rewrite > H2;reflexivity]
|intros 3;elim (decidable_eq_nat n (length ? G))
 [exists [apply P]
  elim G in n H3
  [simplify in H4;destruct;reflexivity
  |simplify;simplify in H5;rewrite > H5;simplify;apply H3;reflexivity]
 |exists [apply U1]
  elim G in n H3 H4 0
  [simplify;intro;elim n1
   [elim H3;reflexivity
   |simplify in H5;simplify;assumption]
  |simplify;intros 4;elim n1
   [simplify in H5;simplify;assumption
   |simplify;apply H3
    [intro;elim H5;autobatch
    |apply H6]]]]]
qed.

lemma WFE_extends : ∀G,H,U,P.WFType H P → WFEnv (G@(mk_bound true U::H)) → WFEnv (G@(mk_bound true P::H)).
intros;cut (WFType H U)
[generalize in match H2;elim G 0;simplify;intros
 [inversion H3;intros;destruct;autobatch
 |generalize in match H4;cases a;intros;apply WFE_cons
  [inversion H4;intros;destruct;autobatch
  |inversion H5;intros;destruct;autobatch]]
|elim G in H2 0;simplify;intros;
 [inversion H2;intros;destruct;assumption
 |apply H2;inversion H3;simplify;intros;destruct;assumption]]
qed.

(*** lemmata relating subtyping and well-formedness ***)

lemma JS_to_WFE : ∀G,T,U.G ⊢ T ⊴ U → WFEnv G.
intros;elim H;assumption.
qed.

lemma JS_to_WFT : ∀G,T,U.G ⊢ T ⊴ U → WFType G T ∧ WFType G U.
intros;elim H
  [1,2:autobatch
  |elim H4;split;autobatch 
  |decompose;autobatch size=7
  |decompose;split
   [apply WFT_Forall;
    [assumption
    |apply (WFT_env_incl2 ?? H2) [reflexivity]
     simplify;intros 3;elim n
     [exists[apply t]
      reflexivity
     |exists[apply U1]
      assumption]]
   |autobatch]]
qed.

lemma JS_to_WFT1 : ∀G,T,U.G ⊢ T ⊴ U → WFType G T.
intros;elim (JS_to_WFT ? ? ? H);assumption;
qed.

lemma JS_to_WFT2 : ∀G,T,U.G ⊢ T ⊴ U → WFType G U.
intros;elim (JS_to_WFT ? ? ? H);assumption;
qed.
