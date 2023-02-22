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

include "nat/compare.ma".
include "nat/plus.ma".
include "list/list.ma".

notation > "'if' term 19 E 'then' term 19 T 'else' term 19 F 'fi'" 
non associative with precedence 90
for @{ match $E with [ true ⇒ $T | false ⇒ $F ] }.

inductive PT : Type ≝ 
  | Var : nat → PT
  | Lam : PT → PT
  | Appl : PT → PT → PT
  | Bang : PT → PT
  | Sect : PT → PT
  | LetB : PT → PT → PT
  | LetS : PT → PT → PT.

variant appl : PT → PT → PT ≝ Appl.
coercion appl 1.  
  
notation > "! term 90 t" non associative with precedence 90 for @{ 'bang $t }.
notation < "! term 90 t" non associative with precedence 90 for @{ 'bang $t }.
interpretation "bang" 'bang t = (Bang t). 
notation > "§ t" non associative with precedence 90 for @{ 'sect $t }.
notation < "§ t" non associative with precedence 90 for @{ 'sect $t }.
interpretation "sect" 'sect t = (Sect t).
notation > "Λ t" non associative with precedence 90 for @{ 'lam $t }.
notation < "Λ t" non associative with precedence 90 for @{ 'lam $t }.
interpretation "lam" 'lam t = (Lam t).
notation < "Λ \sup ! t" non associative with precedence 90 for @{ 'lamb $t}.
notation > "*Λ t" non associative with precedence 90 for @{ 'lamb $t}.
interpretation "lamb" 'lamb t = (Lam (LetB (Var (S O)) t)).
notation "𝟙" non associative with precedence 90 for @{ 'one }.
interpretation "one" 'one = (Var (S O)).  
notation "𝟚" non associative with precedence 90 for @{ 'two }.
interpretation "two" 'two = (Var (S (S O))).  
notation "𝟛" non associative with precedence 90 for @{ 'three }.
interpretation "three" 'three = (Var (S (S (S O)))).  
notation "𝟜" non associative with precedence 90 for @{ 'four }.
interpretation "four" 'four = (Var (S (S (S (S O))))).  
notation < "a ­b" left associative with precedence 65 for @{ 'appl $a $b }.  
interpretation "appl" 'appl a b = (Appl a b).
  
let rec lift (from:nat) (amount:nat) (what:PT) on what : PT ≝ 
  match what with
  [ Var n ⇒ if leb from n then Var (n+amount) else what fi
  | Lam t ⇒ Lam (lift (1+from) amount t)
  | Appl t1 t2 ⇒ Appl (lift from amount t1) (lift from amount t2)
  | Bang t ⇒ Bang (lift from amount t)
  | Sect t ⇒ Sect (lift from amount t)
  | LetB t1 t2 ⇒ LetB (lift from amount t1) (lift (1+from) amount t2) 
  | LetS t1 t2 ⇒ LetS (lift from amount t1) (lift (1+from) amount t2) ].

let rec subst (ww : PT) (fw:nat) (w:PT) on w : PT ≝
  match w with
  [ Var n ⇒  if eqb n fw then ww else if ltb fw n then Var (pred n) else w fi fi
  | Lam t ⇒ Lam (subst (lift 1 1 ww) (1+fw) t)
  | Appl t1 t2 ⇒ Appl (subst ww fw t1) (subst ww fw t2)
  | Bang t ⇒ Bang (subst ww fw t)
  | Sect t ⇒ Sect (subst ww fw t) 
  | LetB t1 t2 ⇒ LetB (subst ww fw t1) (subst (lift 1 1 ww) (1+fw) t2)
  | LetS t1 t2 ⇒ LetS (subst ww fw t1) (subst (lift 1 1 ww) (1+fw) t2) ]. 

definition path ≝ list bool.  
  
definition fire ≝ λt:PT.
  match t with
  [ Appl hd arg ⇒ 
      match hd with
      [ Lam bo ⇒ subst arg 1 bo
      | _ ⇒ t ]
  | LetB def bo ⇒ 
      match def with
      [ Bang t ⇒ subst t 1 bo
      | _ ⇒ t ]
  | LetS def bo ⇒ 
      match def with
      [ Sect t ⇒ subst t 1 bo
      | LetS def2 bo2 ⇒ LetS def2 (LetS bo2 bo)
      | _ ⇒ t ]
  | _ ⇒ t ].

let rec follow (p:path) (t:PT) (f : PT → PT) on p : PT ≝
  match p with
  [ nil ⇒ f t
  | cons b tl ⇒ 
      match t with
      [ Var _ ⇒ t
      | Lam t1 ⇒ if b then t else Lam (follow tl t1 f) fi
      | Appl t1 t2 ⇒ if b then Appl t1 (follow tl t2 f) else Appl (follow tl t1 f) t2 fi
      | Bang t1 ⇒ if b then t else Bang (follow tl t1 f) fi
      | Sect t1 ⇒ if b then t else Sect (follow tl t1 f) fi
      | LetB t1 t2 ⇒ if b then LetB t1 (follow tl t2 f) else LetB (follow tl t1 f) t2 fi 
      | LetS t1 t2 ⇒ if b then LetS t1 (follow tl t2 f) else LetS (follow tl t1 f) t2 fi ]].

definition reduce ≝ λp,t.follow p t fire.

let rec FO (w:nat) (t:PT) on t : nat ≝ 
  match t with
  [ Var n ⇒ if eqb w n then 1 else 0 fi 
  | Lam t ⇒ FO (1+w) t
  | Appl t1 t2 ⇒ FO w t1 + FO w t2
  | Bang t ⇒ FO w t
  | Sect t ⇒ FO w t
  | LetB t1 t2 ⇒ FO w t1 + FO (1+w) t2
  | LetS t1 t2 ⇒ FO w t1 + FO (1+w) t2 ].
  
let rec FOa (w:nat) (t:PT) on t : nat ≝ 
  match t with
  [ Var n ⇒ if ltb w n then 1 else 0 fi 
  | Lam t ⇒ FOa (1+w) t
  | Appl t1 t2 ⇒ FOa w t1 + FOa w t2
  | Bang t ⇒ FOa w t
  | Sect t ⇒ FOa w t
  | LetB t1 t2 ⇒ FOa w t1 + FOa (1+w) t2
  | LetS t1 t2 ⇒ FOa w t1 + FOa (1+w) t2 ].

inductive ctxe : Type ≝ 
  | Reg: ctxe
  | Ban: ctxe
  | Sec: ctxe
  | Err: ctxe.

let rec mapb (l : list ctxe) : list ctxe ≝ 
  match l with
  [ nil ⇒ nil ?
  | cons x xs ⇒ 
      match x with
      [ Ban ⇒ Reg
      | _ ⇒ Err ] :: mapb xs].

let rec maps (l : list ctxe) : list ctxe ≝ 
  match l with
  [ nil ⇒ nil ?
  | cons x xs ⇒ 
      match x with
      [ Ban ⇒ Reg
      | Sec ⇒ Reg
      | _ ⇒ Err ] :: maps xs].

inductive Tok : PT → list ctxe → Prop ≝ 
  | Tv : ∀n,C. nth ? (Err::C) Err n = Reg → Tok (Var n) C
  | Tl : ∀t,C. Tok t (Reg::C) → FO 1 t ≤ 1 → Tok (Lam t) C
  | Ta : ∀t1,t2,C. Tok t1 C → Tok t2 C → Tok (Appl t1 t2) C 
  | Tb : ∀t,C.FOa 0 t ≤ 1 → Tok t (mapb C)  → Tok (Bang t) C
  | Ts : ∀t,C.Tok t (maps C)  → Tok (Sect t) C
  | Tlb: ∀t1,t2,C. Tok t1 C → Tok t2 (Ban::C) → Tok (LetB t1 t2) C
  | Tls: ∀t1,t2,C. Tok t1 C → Tok t2 (Sec::C) → FO 1 t2 ≤ 1 → Tok (LetS t1 t2) C.
  
(* powerup! *)
include "decidable_kit/eqtype.ma".  
  
definition cmpC : ctxe → ctxe → bool ≝ 
  λc1,c2.
    match c1 with 
    [ Reg ⇒ match c2 with [ Reg ⇒ true | _ ⇒ false ] 
    | Ban ⇒ match c2 with [ Ban ⇒ true | _ ⇒ false ]
    | Sec ⇒ match c2 with [ Sec ⇒ true | _ ⇒ false ]
    | Err ⇒ match c2 with [ Err ⇒ true | _ ⇒ false ]].
    
lemma cmpCP: ∀x,y.eq_compatible ? x y (cmpC x y).
intros; apply prove_reflect; cases x; cases y; simplify; intro;
destruct H; try reflexivity; intro W; destruct W;
qed.

definition ctxe_eqType ≝ mk_eqType ?? cmpCP.   
  
let rec Tok_dec (C:list ctxe) (t:PT) on t : bool ≝
  match t with
  [ Var n ⇒ cmp ctxe_eqType (nth ? (Err::C) Err n) Reg
  | Lam t ⇒ andb (Tok_dec (Reg::C) t) (leb (FO 1 t) 1)
  | Appl t1 t2 ⇒ andb (Tok_dec C t1) (Tok_dec C t2) 
  | Bang t ⇒ andb (leb (FOa 0 t) 1) (Tok_dec (mapb C) t)
  | Sect t ⇒ Tok_dec (maps C) t
  | LetB t1 t2 ⇒ andb (Tok_dec C t1) (Tok_dec (Ban::C) t2)
  | LetS t1 t2 ⇒ andb (Tok_dec C t1) (andb (Tok_dec (Sec::C) t2) (leb (FO 1 t2) 1))
  ].
  
(* (constructor ?) tactic *)
notation "#" non associative with precedence 90 for @{ 'Tok }.
interpretation "Tv" 'Tok = Tv. interpretation "Tl" 'Tok = Tl.
interpretation "Ta" 'Tok = Ta. interpretation "Tb" 'Tok = Tb.
interpretation "Ts" 'Tok = Ts. interpretation "Tlb" 'Tok = Tlb.
interpretation "Tls" 'Tok = Tls.
  
lemma TokP : ∀t,C.reflect (Tok t C) (Tok_dec C t).
intros; apply prove_reflect; generalize in match C; elim t; intros;
[1,2,3,4,5,6,7: apply rule #; simplify in H H1 H2;
  [1: apply (b2pT ?? (cmpCP ??) H);
  |2,7: cases (b2pT ?? (andbP ??) H1); apply (b2pT ?? (lebP ??)); assumption;
  |3,6: cases (b2pT ?? (andbP ??) H1); autobatch depth=2;
  |4,5,9,10,13: cases (b2pT ?? (andbP ??) H2); autobatch depth=2;
  |8: autobatch depth=2;
  |11: cases (b2pT ?? (andbP ??) H2); cases (b2pT ?? (andbP ??) H4);
       apply (b2pT ?? (lebP ??)); assumption;
  |12,11: cases (b2pT ?? (andbP ??) H2); cases (b2pT ?? (andbP ??) H4); autobatch depth=2;]
|*: intro E; inversion E; clear E; intros; simplify in H;
    [1: destruct H3; destruct H2; rewrite > H1 in H; normalize in H; destruct H;
    |9: destruct H6; destruct H5; simplify in H1;
        cases (b2pF ?? (andbP ??) H1); split[2:apply (p2bT ?? (lebP ??) H4);] 
        lapply depth=0 (H (Reg::l)) as W; cases (Tok_dec (Reg::l) p) in W;
        intros; [reflexivity] cases (H5 ? H2); reflexivity; 
    |17: destruct H7; destruct H8; simplify in H2; apply (b2pF ?? (andbP ??) H2);
         lapply depth=0 (H l) as W1; lapply depth=0 (H1 l) as W2; 
         cases (Tok_dec l p) in W1; cases (Tok_dec l p1) in W2;
         intros; split; try reflexivity;
         [1,3: cases (H7 ? H5); reflexivity;|*: cases (H8 ? H3); reflexivity;]
    |25: destruct H6; destruct H5; simplify in H1;
         apply (b2pF ?? (andbP ??) H1); rewrite > (p2bT ?? (lebP ??) H2);
         split[reflexivity] lapply depth=0 (H (mapb l)) as W; 
         cases (Tok_dec (mapb l) p) in W; intros; [reflexivity] 
         cases (H5 ? H3); reflexivity;
    |33: destruct H5; destruct H4; simplify in H1; exact (H ? H1 H2);
    |41: destruct H8; destruct H6; destruct H7; clear H4 H6; simplify in H2;
         lapply depth=0 (H l) as W1; lapply depth=0 (H1 (Ban::l)) as W2;
         apply (b2pF ?? (andbP ??) H2); cases (Tok_dec l p) in W1; 
         cases (Tok_dec (Ban::l) p1) in W2; intros; split; try reflexivity;
         [1,3: cases (H4 ? H5); reflexivity;|*: cases (H6 ? H3); reflexivity;]
    |49: destruct H9; destruct H8; clear H6 H4; simplify in H2;
         apply (b2pF ?? (andbP ??) H2); clear H2; rewrite > (p2bT ?? (lebP ??) H7);
         rewrite > andb_sym; simplify; 
         lapply depth=0 (H l) as W1; lapply depth=0 (H1 (Sec::l)) as W2;
         cases (Tok_dec l p) in W1; cases (Tok_dec (Sec::l) p1) in W2;
         intros; split; try reflexivity;
         [1,3: cases (H2 ? H5); reflexivity;|*: cases (H4 ? H3); reflexivity;]
    |*: try solve[destruct H3]; try solve[destruct H4]; try solve[destruct H5];
        try solve[destruct H6]; try solve[destruct H7]; try solve[destruct H8]]]
qed.

definition two : PT ≝ *Λ(§Λ𝟚(𝟚𝟙)).
definition succ : PT ≝ Λ*Λ(LetS (𝟛 (!𝟙)) §(Λ𝟛 (𝟚 𝟙))).
definition three : PT ≝ *Λ(§Λ𝟚(𝟚(𝟚 𝟙))).

lemma two_Tok : Tok two [ ]. apply (b2pT ?? (TokP ??)); reflexivity; qed.
lemma succ_Tok : Tok succ [ ]. apply (b2pT ?? (TokP ??)); reflexivity; qed.
lemma three_Tok : Tok three [ ]. apply (b2pT ?? (TokP ??)); reflexivity; qed.

definition foldl ≝ 
  λA,B:Type.λf:A → B → B.
  let rec aux (acc: B) (l:list A) on l  ≝ 
    match l with
    [ nil ⇒  acc
    | cons x xs ⇒ aux (f x acc) xs]
  in 
    aux.

lemma obvious : ∃pl.foldl ?? reduce (succ two) pl = three.
unfold succ; unfold two; exists; 
[apply ([ ] :: ?);| simplify;]
[apply ([false;true;false] :: ?);| simplify;]
[apply ([false;true;false] :: ?);| simplify;]
[apply ([false;true] :: ?);| simplify;]
[apply ([false;true;false;false;true] :: ?);| simplify;]
[apply ([ ]);| simplify;]
reflexivity;
qed.