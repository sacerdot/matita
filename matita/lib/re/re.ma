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
include "basics/lists/list.ma".
include "basics/sets.ma".

definition word ≝ λS:DeqSet.list S.

inductive re (S: DeqSet) : Type[0] ≝
   z: re S
 | e: re S
 | s: S → re S
 | c: re S → re S → re S
 | o: re S → re S → re S
 | k: re S → re S.
 
(* notation < "a \sup ⋇" non associative with precedence 90 for @{ 'pk $a}.*)
notation "a ^ *" non associative with precedence 90 for @{ 'pk $a}.
interpretation "star" 'pk a = (k ? a).
interpretation "or" 'plus a b = (o ? a b).
           
notation "a · b" non associative with precedence 60 for @{ 'pc $a $b}.
interpretation "cat" 'pc a b = (c ? a b).

(* to get rid of \middot 
ncoercion c  : ∀S:DeqSet.∀p:re S.  re S →  re S   ≝ c  on _p : re ?  to ∀_:?.?.
*)

notation < "a" non associative with precedence 90 for @{ 'ps $a}.
notation > "` term 90 a" non associative with precedence 90 for @{ 'ps $a}.
interpretation "atom" 'ps a = (s ? a).

notation "ϵ" non associative with precedence 90 for @{ 'epsilon }.
interpretation "epsilon" 'epsilon = (e ?).

notation "`∅" non associative with precedence 90 for @{ 'empty }.
interpretation "empty" 'empty = (z ?).

let rec flatten (S : DeqSet) (l : list (word S)) on l : word S ≝ 
match l with [ nil ⇒ [ ] | cons w tl ⇒ w @ flatten ? tl ].

let rec conjunct (S : DeqSet) (l : list (word S)) (r : word S → Prop) on l: Prop ≝
match l with [ nil ⇒ True | cons w tl ⇒ r w ∧ conjunct ? tl r ]. 

(*
definition empty_lang ≝ λS.λw:word S.False.
notation "{}" non associative with precedence 90 for @{'empty_lang}.
interpretation "empty lang" 'empty_lang = (empty_lang ?).

definition sing_lang ≝ λS.λx,w:word S.x=w.
(* notation "{x}" non associative with precedence 90 for @{'sing_lang $x}.*)
interpretation "sing lang" 'singl x = (sing_lang ? x).

definition union : ∀S,l1,l2,w.Prop ≝ λS.λl1,l2.λw:word S.l1 w ∨ l2 w.
interpretation "union lang" 'union a b = (union ? a b). *)

definition cat : ∀S,l1,l2,w.Prop ≝ 
  λS.λl1,l2.λw:word S.∃w1,w2.w1 @ w2 = w ∧ l1 w1 ∧ l2 w2.
interpretation "cat lang" 'pc a b = (cat ? a b).

definition star ≝ λS.λl.λw:word S.∃lw.flatten ? lw = w ∧ conjunct ? lw l. 
interpretation "star lang" 'pk l = (star ? l).

let rec in_l (S : DeqSet) (r : re S) on r : word S → Prop ≝ 
match r with
[ z ⇒ ∅
| e ⇒ { [ ] }
| s x ⇒ { [x] }
| c r1 r2 ⇒ (in_l ? r1) · (in_l ? r2)
| o r1 r2 ⇒ (in_l ? r1) ∪ (in_l ? r2)
| k r1 ⇒ (in_l ? r1) ^*].

notation "\sem{term 19 E}" non associative with precedence 75 for @{'in_l $E}.
interpretation "in_l" 'in_l E = (in_l ? E).
interpretation "in_l mem" 'mem w l = (in_l ? l w).

lemma rsem_star : ∀S.∀r: re S. \sem{r^*} = \sem{r}^*.
// qed.

inductive pitem (S: DeqSet) : Type[0] ≝
   pz: pitem S
 | pe: pitem S
 | ps: S → pitem S
 | pp: S → pitem S
 | pc: pitem S → pitem S → pitem S
 | po: pitem S → pitem S → pitem S
 | pk: pitem S → pitem S.
 
definition pre ≝ λS.pitem S × bool.

interpretation "pstar" 'pk a = (pk ? a).
interpretation "por" 'plus a b = (po ? a b).
interpretation "pcat" 'pc a b = (pc ? a b).
notation < ".a" non associative with precedence 90 for @{ 'pp $a}.
notation > "`. term 90 a" non associative with precedence 90 for @{ 'pp $a}.
interpretation "ppatom" 'pp a = (pp ? a).

(* to get rid of \middot 
ncoercion pc : ∀S.∀p:pitem S. pitem S → pitem S  ≝ pc on _p : pitem ? to ∀_:?.?.
*)

interpretation "patom" 'ps a = (ps ? a).
interpretation "pepsilon" 'epsilon = (pe ?).
interpretation "pempty" 'empty = (pz ?).

let rec forget (S: DeqSet) (l : pitem S) on l: re S ≝
 match l with
  [ pz ⇒ `∅
  | pe ⇒ ϵ
  | ps x ⇒ `x
  | pp x ⇒ `x
  | pc E1 E2 ⇒ (forget ? E1) · (forget ? E2)
  | po E1 E2 ⇒ (forget ? E1) + (forget ? E2)
  | pk E ⇒ (forget ? E)^* ].
  
(* notation < "|term 19 e|" non associative with precedence 70 for @{'forget $e}.*)
interpretation "forget" 'norm a = (forget ? a).

let rec in_pl (S : DeqSet) (r : pitem S) on r : word S → Prop ≝ 
match r with
[ pz ⇒ ∅
| pe ⇒ ∅
| ps _ ⇒ ∅
| pp x ⇒ { [x] }
| pc r1 r2 ⇒ (in_pl ? r1) · \sem{forget ? r2} ∪ (in_pl ? r2)
| po r1 r2 ⇒ (in_pl ? r1) ∪ (in_pl ? r2)
| pk r1 ⇒ (in_pl ? r1) · \sem{forget ? r1}^*  ].

interpretation "in_pl" 'in_l E = (in_pl ? E).
interpretation "in_pl mem" 'mem w l = (in_pl ? l w).

(*
definition epsilon : ∀S:DeqSet.bool → word S → Prop
≝ λS,b.if b then { ([ ] : word S) } else ∅. 

interpretation "epsilon" 'epsilon = (epsilon ?).
notation < "ϵ b" non associative with precedence 90 for @{'app_epsilon $b}.
interpretation "epsilon lang" 'app_epsilon b = (epsilon ? b). *)

definition in_prl ≝ λS : DeqSet.λp:pre S. 
  if (\snd p) then \sem{\fst p} ∪ { ([ ] : word S) } else \sem{\fst p}.
  
interpretation "in_prl mem" 'mem w l = (in_prl ? l w).
interpretation "in_prl" 'in_l E = (in_prl ? E).

lemma sem_pre_true : ∀S.∀i:pitem S. 
  \sem{〈i,true〉} = \sem{i} ∪ { ([ ] : word S) }. 
// qed.

lemma sem_pre_false : ∀S.∀i:pitem S. 
  \sem{〈i,false〉} = \sem{i}. 
// qed.

lemma sem_cat: ∀S.∀i1,i2:pitem S. 
  \sem{i1 · i2} = \sem{i1} · \sem{|i2|} ∪ \sem{i2}.
// qed.

lemma sem_cat_w: ∀S.∀i1,i2:pitem S.∀w.
  \sem{i1 · i2} w = ((\sem{i1} · \sem{|i2|}) w ∨ \sem{i2} w).
// qed.

lemma sem_plus: ∀S.∀i1,i2:pitem S. 
  \sem{i1 + i2} = \sem{i1} ∪ \sem{i2}.
// qed.

lemma sem_plus_w: ∀S.∀i1,i2:pitem S.∀w. 
  \sem{i1 + i2} w = (\sem{i1} w ∨ \sem{i2} w).
// qed.

lemma sem_star : ∀S.∀i:pitem S.
  \sem{i^*} = \sem{i} · \sem{|i|}^*.
// qed.

lemma sem_star_w : ∀S.∀i:pitem S.∀w.
  \sem{i^*} w = (∃w1,w2.w1 @ w2 = w ∧ \sem{i} w1 ∧ \sem{|i|}^* w2).
// qed.

lemma append_eq_nil : ∀S.∀w1,w2:word S. w1 @ w2 = [ ] → w1 = [ ].
#S #w1 #w2 cases w1 // #a #tl normalize #H destruct qed.

lemma not_epsilon_lp : ∀S:DeqSet.∀e:pitem S. ¬ ([ ] ∈ e).
#S #e elim e normalize /2/  
  [#r1 #r2 * #n1 #n2 % * /2/ * #w1 * #w2 * * #H 
   >(append_eq_nil …H…) /2/
  |#r1 #r2 #n1 #n2 % * /2/
  |#r #n % * #w1 * #w2 * * #H >(append_eq_nil …H…) /2/
  ]
qed.

(* lemma 12 *)
lemma epsilon_to_true : ∀S.∀e:pre S. [ ] ∈ e → \snd e = true.
#S * #i #b cases b // normalize #H @False_ind /2/ 
qed.

lemma true_to_epsilon : ∀S.∀e:pre S. \snd e = true → [ ] ∈ e.
#S * #i #b #btrue normalize in btrue; >btrue %2 // 
qed.

definition lo ≝ λS:DeqSet.λa,b:pre S.〈\fst a + \fst b,\snd a ∨ \snd b〉.
notation "a ⊕ b" left associative with precedence 60 for @{'oplus $a $b}.
interpretation "oplus" 'oplus a b = (lo ? a b).

lemma lo_def: ∀S.∀i1,i2:pitem S.∀b1,b2. 〈i1,b1〉⊕〈i2,b2〉=〈i1+i2,b1∨b2〉.
// qed.

definition pre_concat_r ≝ λS:DeqSet.λi:pitem S.λe:pre S.
  match e with [ pair i1 b ⇒ 〈i · i1, b〉].
 
notation "i ◂ e" left associative with precedence 60 for @{'ltrif $i $e}.
interpretation "pre_concat_r" 'ltrif i e = (pre_concat_r ? i e).
  
definition eq_f1 ≝ λS.λa,b:word S → Prop.∀w.a w ↔ b w.
notation "A =1 B" non associative with precedence 45 for @{'eq_f1 $A $B}.
interpretation "eq f1" 'eq_f1 a b = (eq_f1 ? a b).

lemma eq_to_ex_eq: ∀S.∀A,B:word S → Prop. 
  A = B → A =1 B. 
#S #A #B #H >H /2/ qed.

(* lemma eqP_trans: ∀S.∀A,B,C:word S → Prop. 
  A =1 B → B =1 C → A =1 C. 
#S #A #B #C #eqAB #eqBC #w cases (eqAB w) cases (eqBC w) /4/
qed.  

lemma union_assoc: ∀S.∀A,B,C:word S → Prop. 
  A ∪ B ∪ C =1 A ∪ (B ∪ C).
#S #A #B #C #w % [* [* /3/ | /3/] | * [/3/ | * /3/]
qed.  *)

lemma sem_pre_concat_r : ∀S,i.∀e:pre S.
  \sem{i ◂ e} =1 \sem{i} · \sem{|\fst e|} ∪ \sem{e}.
#S #i * #i1 #b1 cases b1 /2/
>sem_pre_true >sem_cat >sem_pre_true /2/ 
qed.
 
definition lc ≝ λS:DeqSet.λbcast:∀S:DeqSet.pitem S → pre S.λe1:pre S.λi2:pitem S.
  match e1 with 
  [ pair i1 b1 ⇒ match b1 with 
    [ true ⇒ (i1 ◂ (bcast ? i2)) 
    | false ⇒ 〈i1 · i2,false〉
    ]
  ].
        
definition lift ≝ λS.λf:pitem S →pre S.λe:pre S. 
  match e with 
  [ pair i b ⇒ 〈\fst (f i), \snd (f i) ∨ b〉].

notation "a ▸ b" left associative with precedence 60 for @{'lc eclose $a $b}.
interpretation "lc" 'lc op a b = (lc ? op a b).

definition lk ≝ λS:DeqSet.λbcast:∀S:DeqSet.∀E:pitem S.pre S.λe:pre S.
  match e with 
  [ pair i1 b1 ⇒
    match b1 with 
    [true ⇒ 〈(\fst (bcast ? i1))^*, true〉
    |false ⇒ 〈i1^*,false〉
    ]
  ]. 

(*
lemma oplus_tt : ∀S: DeqSet.∀i1,i2:pitem S. 
  〈i1,true〉 ⊕ 〈i2,true〉  = 〈i1 + i2,true〉.
// qed.

lemma oplus_tf : ∀S: DeqSet.∀i1,i2:pitem S. 
  〈i1,true〉 ⊕ 〈i2,false〉  = 〈i1 + i2,true〉.
// qed.

lemma oplus_ft : ∀S: DeqSet.∀i1,i2:pitem S. 
  〈i1,false〉 ⊕ 〈i2,true〉  = 〈i1 + i2,true〉.
// qed.

lemma oplus_ff : ∀S: DeqSet.∀i1,i2:pitem S. 
  〈i1,false〉 ⊕ 〈i2,false〉  = 〈i1 + i2,false〉.
// qed. *)

(* notation < "a \sup ⊛" non associative with precedence 90 for @{'lk $op $a}.*)
interpretation "lk" 'lk op a = (lk ? op a).
notation "a^⊛" non associative with precedence 90 for @{'lk eclose $a}.

notation "•" non associative with precedence 60 for @{eclose ?}.

let rec eclose (S: DeqSet) (i: pitem S) on i : pre S ≝
 match i with
  [ pz ⇒ 〈 `∅, false 〉
  | pe ⇒ 〈 ϵ,  true 〉
  | ps x ⇒ 〈 `.x, false〉
  | pp x ⇒ 〈 `.x, false 〉
  | po i1 i2 ⇒ •i1 ⊕ •i2
  | pc i1 i2 ⇒ •i1 ▸ i2
  | pk i ⇒ 〈(\fst (•i))^*,true〉].
  
notation "• x" non associative with precedence 60 for @{'eclose $x}.
interpretation "eclose" 'eclose x = (eclose ? x).

lemma eclose_plus: ∀S:DeqSet.∀i1,i2:pitem S.
  •(i1 + i2) = •i1 ⊕ •i2.
// qed.

lemma eclose_dot: ∀S:DeqSet.∀i1,i2:pitem S.
  •(i1 · i2) = •i1 ▸ i2.
// qed.

lemma eclose_star: ∀S:DeqSet.∀i:pitem S.
  •i^* = 〈(\fst(•i))^*,true〉.
// qed.

definition reclose ≝ λS. lift S (eclose S). 
interpretation "reclose" 'eclose x = (reclose ? x).

(*
lemma epsilon_or : ∀S:DeqSet.∀b1,b2. epsilon S (b1 || b2) =1 ϵ b1 ∪ ϵ b2. 
#S #b1 #b2 #w % cases b1 cases b2 normalize /2/ * /2/ * ;
qed. *)

(*
lemma cupA : ∀S.∀a,b,c:word S → Prop.a ∪ b ∪ c = a ∪ (b ∪ c).
#S a b c; napply extP; #w; nnormalize; @; *; /3/; *; /3/; nqed.

nlemma cupC : ∀S. ∀a,b:word S → Prop.a ∪ b = b ∪ a.
#S a b; napply extP; #w; @; *; nnormalize; /2/; nqed.*)

(* theorem 16: 2 *)
lemma sem_oplus: ∀S:DeqSet.∀e1,e2:pre S.
  \sem{e1 ⊕ e2} =1 \sem{e1} ∪ \sem{e2}. 
#S * #i1 #b1 * #i2 #b2 #w %
  [cases b1 cases b2 normalize /2/ * /3/ * /3/
  |cases b1 cases b2 normalize /2/ * /3/ * /3/
  ]
qed.

lemma odot_true : 
  ∀S.∀i1,i2:pitem S.
  〈i1,true〉 ▸ i2 = i1 ◂ (•i2).
// qed.

lemma odot_true_bis : 
  ∀S.∀i1,i2:pitem S.
  〈i1,true〉 ▸ i2 = 〈i1 · \fst (•i2), \snd (•i2)〉.
#S #i1 #i2 normalize cases (•i2) // qed.

lemma odot_false: 
  ∀S.∀i1,i2:pitem S.
  〈i1,false〉 ▸ i2 = 〈i1 · i2, false〉.
// qed.

lemma LcatE : ∀S.∀e1,e2:pitem S.
  \sem{e1 · e2} = \sem{e1} · \sem{|e2|} ∪ \sem{e2}. 
// qed.

(*
nlemma cup_dotD : ∀S.∀p,q,r:word S → Prop.(p ∪ q) · r = (p · r) ∪ (q · r). 
#S p q r; napply extP; #w; nnormalize; @; 
##[ *; #x; *; #y; *; *; #defw; *; /7/ by or_introl, or_intror, ex_intro, conj;
##| *; *; #x; *; #y; *; *; /7/ by or_introl, or_intror, ex_intro, conj; ##]
nqed.

nlemma cup0 :∀S.∀p:word S → Prop.p ∪ {} = p.
#S p; napply extP; #w; nnormalize; @; /2/; *; //; *; nqed.*)

lemma erase_dot : ∀S.∀e1,e2:pitem S. |e1 · e2| = c ? (|e1|) (|e2|).
// qed.

lemma erase_plus : ∀S.∀i1,i2:pitem S.
  |i1 + i2| = |i1| + |i2|.
// qed.

lemma erase_star : ∀S.∀i:pitem S.|i^*| = |i|^*. 
// qed.

definition substract := λS.λp,q:word S → Prop.λw.p w ∧ ¬ q w.
interpretation "substract" 'minus a b = (substract ? a b).

(* nlemma cup_sub: ∀S.∀a,b:word S → Prop. ¬ (a []) → a ∪ (b - {[]}) = (a ∪ b) - {[]}.
#S a b c; napply extP; #w; nnormalize; @; *; /4/; *; /4/; nqed.

nlemma sub0 : ∀S.∀a:word S → Prop. a - {} = a.
#S a; napply extP; #w; nnormalize; @; /3/; *; //; nqed.

nlemma subK : ∀S.∀a:word S → Prop. a - a = {}.
#S a; napply extP; #w; nnormalize; @; *; /2/; nqed.

nlemma subW : ∀S.∀a,b:word S → Prop.∀w.(a - b) w → a w.
#S a b w; nnormalize; *; //; nqed. *)

lemma erase_bull : ∀S.∀i:pitem S. |\fst (•i)| = |i|.
#S #i elim i // 
  [ #i1 #i2 #IH1 #IH2 >erase_dot <IH1 >eclose_dot
    cases (•i1) #i11 #b1 cases b1 // <IH2 >odot_true_bis //
  | #i1 #i2 #IH1 #IH2 >eclose_plus >(erase_plus … i1) <IH1 <IH2
    cases (•i1) #i11 #b1 cases (•i2) #i21 #b2 //  
  | #i #IH >eclose_star >(erase_star … i) <IH cases (•i) //
  ]
qed.

lemma cat_ext_l: ∀S.∀A,B,C:word S →Prop. 
  A =1 C  → A · B =1 C · B.
#S #A #B #C #H #w % * #w1 * #w2 * * #eqw #inw1 #inw2
cases (H w1) /6/ 
qed.
  
lemma cat_ext_r: ∀S.∀A,B,C:word S →Prop. 
  B =1 C → A · B =1 A · C.
#S #A #B #C #H #w % * #w1 * #w2 * * #eqw #inw1 #inw2
cases (H w2) /6/ 
qed.
  
lemma distr_cat_r: ∀S.∀A,B,C:word S →Prop.
  (A ∪ B) · C =1  A · C ∪ B · C. 
#S #A #B #C #w %
  [* #w1 * #w2 * * #eqw * /6/ |* * #w1 * #w2 * * /6/] 
qed.

(*
lemma fix_star_aux: ∀S.∀A:word S → Prop.∀w1,w2.
  A w1 → A^* w2 → A^* (w1@w2).
#S #A #w1 #w2 #Aw1 * #l * #H #H1 
@(ex_intro *)
 
lemma fix_star: ∀S.∀A:word S → Prop. 
  A^* =1 A · A^* ∪ { [ ] }.
#S #A #w %
  [* #l generalize in match w; -w cases l [normalize #w * /2/]
   #w1 #tl #w * whd in ⊢ ((??%?)→?); #eqw whd in ⊢ (%→?); *
   #w1A #cw1 %1 @(ex_intro … w1) @(ex_intro … (flatten S tl))
   % /2/ whd @(ex_intro … tl) /2/
  |* [2: normalize #eqw <eqw @(ex_intro … (nil ?)) /2/]
   (* caso interessante *)
   cut (∀w1,w2.w=w1@w2 → cat S A A^* w2 → A^* w2) 
     [2:#H @(H … (nil ?)) //]
   elim w 
     [#w1 #w2 #H cases (nil_to_nil … (sym_eq … H)) #_ #H >H #_ 
      @(ex_intro … (nil ?)) /2/
     |#a #w1 #Hind * 
       [#w2 whd in ⊢ ((???%)→?); #eqw2 <eqw2 *
        #w3 * #w4 cases w3
         [* * whd in ⊢ ((??%?)→?); #H <H //
         |#b #w5 * * whd in ⊢ ((??%?)→?); #H destruct
          #H1 * #l * #H2 #H3 @(ex_intro … ((a::w5)::l)) %      
          normalize // /2/
         ]
       |#b #w2 #w3 whd in ⊢ ((???%)→?); #H destruct #H1
        @(Hind … w2) //
       ]
     ]
   ]
qed.
      
axiom star_epsilon: ∀S:DeqSet.∀A:word S → Prop.
  A^* ∪ { [ ] } =1 A^*.

lemma sem_eclose_star: ∀S:DeqSet.∀i:pitem S.
  \sem{〈i^*,true〉} =1 \sem{〈i,false〉}·\sem{|i|}^* ∪ { [ ] }.
/2/ qed.

(*
lemma sem_eclose_star: ∀S:DeqSet.∀i:pitem S.
  \sem{〈i^*,true〉} =1 \sem{〈i,true〉}·\sem{|i|}^* ∪ { [ ] }.
/2/ qed.

#S #i #b cases b 
  [>sem_pre_true >sem_star
  |/2/
  ] *)

(* this kind of results are pretty bad for automation;
   better not index them *)
lemma epsilon_cat_r: ∀S.∀A:word S →Prop.
   A · { [ ] } =1  A. 
#S #A #w %
  [* #w1 * #w2 * * #eqw #inw1 normalize #eqw2 <eqw //
  |#inA @(ex_intro … w) @(ex_intro … [ ]) /3/
  ]
qed-.

lemma epsilon_cat_l: ∀S.∀A:word S →Prop.
   { [ ] } · A =1  A. 
#S #A #w %
  [* #w1 * #w2 * * #eqw normalize #eqw2 <eqw <eqw2 //
  |#inA @(ex_intro … [ ]) @(ex_intro … w) /3/
  ]
qed-.


lemma distr_cat_r_eps: ∀S.∀A,C:word S →Prop.
  (A ∪ { [ ] }) · C =1  A · C ∪ C. 
#S #A #C @eqP_trans [|@distr_cat_r |@eqP_union_l @epsilon_cat_l]
qed.

(* axiom eplison_cut_l: ∀S.∀A:word S →Prop. 
   { [ ] } · A =1  A.
   
 axiom eplison_cut_r: ∀S.∀A:word S →Prop.
   A · { [ ] } =1  A. *)

(*
lemma eta_lp : ∀S.∀p:pre S.𝐋\p p = 𝐋\p 〈\fst p, \snd p〉.
#S p; ncases p; //; nqed.

nlemma epsilon_dot: ∀S.∀p:word S → Prop. {[]} · p = p. 
#S e; napply extP; #w; nnormalize; @; ##[##2: #Hw; @[]; @w; /3/; ##]
*; #w1; *; #w2; *; *; #defw defw1 Hw2; nrewrite < defw; nrewrite < defw1;
napply Hw2; nqed.*)

(* theorem 16: 1 → 3 *)
lemma odot_dot_aux : ∀S.∀e1:pre S.∀i2:pitem S.
   \sem{•i2} =1  \sem{i2} ∪ \sem{|i2|} →
   \sem{e1 ▸ i2} =1  \sem{e1} · \sem{|i2|} ∪ \sem{i2}.
#S * #i1 #b1 #i2 cases b1
  [2:#th >odot_false >sem_pre_false >sem_pre_false >sem_cat /2/
  |#H >odot_true >sem_pre_true @(eqP_trans … (sem_pre_concat_r …))
   >erase_bull @eqP_trans [|@(eqP_union_l … H)]
    @eqP_trans [|@eqP_union_l[|@union_comm ]]
    @eqP_trans [|@eqP_sym @union_assoc ] /3/ 
  ]
qed.

axiom star_fix : 
  ∀S.∀X:word S → Prop.(X - {[ ]}) · X^* ∪ {[ ]} =1 X^*.
  
axiom sem_fst: ∀S.∀e:pre S. \sem{\fst e} =1 \sem{e}-{[ ]}.

axiom sem_fst_aux: ∀S.∀e:pre S.∀i:pitem S.∀A. 
 \sem{e} =1 \sem{i} ∪ A → \sem{\fst e} =1 \sem{i} ∪ (A - {[ ]}).

(* theorem 16: 1 *)
theorem sem_bull: ∀S:DeqSet. ∀e:pitem S.  \sem{•e} =1 \sem{e} ∪ \sem{|e|}.
#S #e elim e 
  [#w normalize % [/2/ | * //]
  |/2/ 
  |#x normalize #w % [ /2/ | * [@False_ind | //]]
  |#x normalize #w % [ /2/ | * // ] 
  |#i1 #i2 #IH1 #IH2 >eclose_dot
   @eqP_trans [|@odot_dot_aux //] >sem_cat 
   @eqP_trans
     [|@eqP_union_r
       [|@eqP_trans [|@(cat_ext_l … IH1)] @distr_cat_r]]
   @eqP_trans [|@union_assoc]
   @eqP_trans [||@eqP_sym @union_assoc]
   @eqP_union_l //
  |#i1 #i2 #IH1 #IH2 >eclose_plus
   @eqP_trans [|@sem_oplus] >sem_plus >erase_plus 
   @eqP_trans [|@(eqP_union_l … IH2)]
   @eqP_trans [|@eqP_sym @union_assoc]
   @eqP_trans [||@union_assoc] @eqP_union_r
   @eqP_trans [||@eqP_sym @union_assoc]
   @eqP_trans [||@eqP_union_l [|@union_comm]]
   @eqP_trans [||@union_assoc] /3/
  |#i #H >sem_pre_true >sem_star >erase_bull >sem_star
   @eqP_trans [|@eqP_union_r [|@cat_ext_l [|@sem_fst_aux //]]]
   @eqP_trans [|@eqP_union_r [|@distr_cat_r]]
   @eqP_trans [|@union_assoc] @eqP_union_l >erase_star @star_fix 
  ]
qed.

definition lifted_cat ≝ λS:DeqSet.λe:pre S. 
  lift S (lc S eclose e).

notation "e1 ⊙ e2" left associative with precedence 70 for @{'odot $e1 $e2}.

interpretation "lifted cat" 'odot e1 e2 = (lifted_cat ? e1 e2).

lemma sem_odot_true: ∀S:DeqSet.∀e1:pre S.∀i. 
  \sem{e1 ⊙ 〈i,true〉} =1 \sem{e1 ▸ i} ∪ { [ ] }.
#S #e1 #i 
cut (e1 ⊙ 〈i,true〉 = 〈\fst (e1 ▸ i), \snd(e1 ▸ i) ∨ true〉) [//]
#H >H cases (e1 ▸ i) #i1 #b1 cases b1 
  [>sem_pre_true @eqP_trans [||@eqP_sym @union_assoc]
   @eqP_union_l /2/ 
  |/2/
  ]
qed.

lemma eq_odot_false: ∀S:DeqSet.∀e1:pre S.∀i. 
  e1 ⊙ 〈i,false〉 = e1 ▸ i.
#S #e1 #i  
cut (e1 ⊙ 〈i,false〉 = 〈\fst (e1 ▸ i), \snd(e1 ▸ i) ∨ false〉) [//]
cases (e1 ▸ i) #i1 #b1 cases b1 #H @H
qed.

lemma sem_odot: 
  ∀S.∀e1,e2: pre S. \sem{e1 ⊙ e2} =1 \sem{e1}· \sem{|\fst e2|} ∪ \sem{e2}.
#S #e1 * #i2 * 
  [>sem_pre_true 
   @eqP_trans [|@sem_odot_true]
   @eqP_trans [||@union_assoc] @eqP_union_r @odot_dot_aux //
  |>sem_pre_false >eq_odot_false @odot_dot_aux //
  ]
qed.

(*
nlemma dot_star_epsilon : ∀S.∀e:re S.𝐋 e · 𝐋 e^* ∪ {[]} =  𝐋 e^*.
#S e; napply extP; #w; nnormalize; @;
##[ *; ##[##2: #H; nrewrite < H; @[]; /3/] *; #w1; *; #w2; 
    *; *; #defw Hw1; *; #wl; *; #defw2 Hwl; @(w1 :: wl);
    nrewrite < defw; nrewrite < defw2; @; //; @;//;
##| *; #wl; *; #defw Hwl; ncases wl in defw Hwl; ##[#defw; #; @2; nrewrite < defw; //]
    #x xs defw; *; #Hx Hxs; @; @x; @(flatten ? xs); nrewrite < defw;
    @; /2/; @xs; /2/;##]
 nqed.

nlemma nil_star : ∀S.∀e:re S. [ ] ∈ e^*.
#S e; @[]; /2/; nqed.

nlemma cupID : ∀S.∀l:word S → Prop.l ∪ l = l.
#S l; napply extP; #w; @; ##[*]//; #; @; //; nqed.

nlemma cup_star_nil : ∀S.∀l:word S → Prop. l^* ∪ {[]} = l^*.
#S a; napply extP; #w; @; ##[*; //; #H; nrewrite < H; @[]; @; //] #;@; //;nqed.

nlemma rcanc_sing : ∀S.∀A,C:word S → Prop.∀b:word S .
  ¬ (A b) → A ∪ { (b) } = C → A = C - { (b) }.
#S A C b nbA defC; nrewrite < defC; napply extP; #w; @;
##[ #Aw; /3/| *; *; //; #H nH; ncases nH; #abs; nlapply (abs H); *]
nqed.
*)

(* theorem 16: 4 *)      
theorem sem_ostar: ∀S.∀e:pre S. 
  \sem{e^⊛} =1  \sem{e} · \sem{|\fst e|}^*.
#S * #i #b cases b
  [>sem_pre_true >sem_pre_true >sem_star >erase_bull
   @eqP_trans [|@eqP_union_r[|@cat_ext_l [|@sem_fst_aux //]]]
   @eqP_trans [|@eqP_union_r [|@distr_cat_r]]
   @eqP_trans [||@eqP_sym @distr_cat_r]
   @eqP_trans [|@union_assoc] @eqP_union_l
   @eqP_trans [||@eqP_sym @epsilon_cat_l] @star_fix 
  |>sem_pre_false >sem_pre_false >sem_star /2/
  ]
qed.
  
(*
nlet rec pre_of_re (S : DeqSet) (e : re S) on e : pitem S ≝ 
  match e with 
  [ z ⇒ pz ?
  | e ⇒ pe ?
  | s x ⇒ ps ? x
  | c e1 e2 ⇒ pc ? (pre_of_re ? e1) (pre_of_re ? e2)
  | o e1 e2 ⇒ po ? (pre_of_re ? e1) (pre_of_re ? e2)
  | k e1 ⇒ pk ? (pre_of_re ? e1)].

nlemma notFalse : ¬False. @; //; nqed.

nlemma dot0 : ∀S.∀A:word S → Prop. {} · A = {}.
#S A; nnormalize; napply extP; #w; @; ##[##2: *]
*; #w1; *; #w2; *; *; //; nqed.

nlemma Lp_pre_of_re : ∀S.∀e:re S. 𝐋\p (pre_of_re ? e) = {}.
#S e; nelim e; ##[##1,2,3: //]
##[ #e1 e2 H1 H2; nchange in match (𝐋\p (pre_of_re S (e1 e2))) with (?∪?);
    nrewrite > H1; nrewrite > H2; nrewrite > (dot0…); nrewrite > (cupID…);//
##| #e1 e2 H1 H2; nchange in match (𝐋\p (pre_of_re S (e1+e2))) with (?∪?);
    nrewrite > H1; nrewrite > H2; nrewrite > (cupID…); //
##| #e1 H1; nchange in match (𝐋\p (pre_of_re S (e1^* ))) with (𝐋\p (pre_of_re ??) · ?);
    nrewrite > H1; napply dot0; ##]
nqed.

nlemma erase_pre_of_reK : ∀S.∀e. 𝐋 |pre_of_re S e| = 𝐋 e.
#S A; nelim A; //; 
##[ #e1 e2 H1 H2; nchange in match (𝐋 (e1 · e2)) with (𝐋 e1·?);
    nrewrite < H1; nrewrite < H2; //
##| #e1 e2 H1 H2; nchange in match (𝐋 (e1 + e2)) with (𝐋 e1 ∪ ?);
    nrewrite < H1; nrewrite < H2; //
##| #e1 H1; nchange in match (𝐋  (e1^* )) with ((𝐋 e1)^* );
    nrewrite < H1; //]
nqed.     

(* corollary 17 *)
nlemma L_Lp_bull : ∀S.∀e:re S.𝐋 e = 𝐋\p (•pre_of_re ? e).
#S e; nrewrite > (bull_cup…); nrewrite > (Lp_pre_of_re…);
nrewrite > (cupC…); nrewrite > (cup0…); nrewrite > (erase_pre_of_reK…); //;
nqed.

nlemma Pext : ∀S.∀f,g:word S → Prop. f = g → ∀w.f w → g w.
#S f g H; nrewrite > H; //; nqed.
 
(* corollary 18 *)
ntheorem bull_true_epsilon : ∀S.∀e:pitem S. \snd (•e) = true ↔ [ ] ∈ |e|.
#S e; @;
##[ #defsnde; nlapply (bull_cup ? e); nchange in match (𝐋\p (•e)) with (?∪?);
    nrewrite > defsnde; #H; 
    nlapply (Pext ??? H [ ] ?); ##[ @2; //] *; //;

*)


