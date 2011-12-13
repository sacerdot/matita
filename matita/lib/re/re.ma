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

include "re/lang.ma".

inductive re (S: DeqSet) : Type[0] ≝
   z: re S
 | e: re S
 | s: S → re S
 | c: re S → re S → re S
 | o: re S → re S → re S
 | k: re S → re S.

interpretation "re epsilon" 'epsilon = (e ?).
interpretation "re or" 'plus a b = (o ? a b).
interpretation "re cat" 'middot a b = (c ? a b).
interpretation "re star" 'star a = (k ? a).

notation < "a" non associative with precedence 90 for @{ 'ps $a}.
notation > "` term 90 a" non associative with precedence 90 for @{ 'ps $a}.
interpretation "atom" 'ps a = (s ? a).

notation "`∅" non associative with precedence 90 for @{ 'empty }.
interpretation "empty" 'empty = (z ?).

let rec in_l (S : DeqSet) (r : re S) on r : word S → Prop ≝ 
match r with
[ z ⇒ ∅
| e ⇒ {ϵ}
| s x ⇒ {[x]}
| c r1 r2 ⇒ (in_l ? r1) · (in_l ? r2)
| o r1 r2 ⇒ (in_l ? r1) ∪ (in_l ? r2)
| k r1 ⇒ (in_l ? r1) ^*].

notation "\sem{term 19 E}" non associative with precedence 75 for @{'in_l $E}.
interpretation "in_l" 'in_l E = (in_l ? E).
interpretation "in_l mem" 'mem w l = (in_l ? l w).

lemma rsem_star : ∀S.∀r: re S. \sem{r^*} = \sem{r}^*.
// qed.


(* pointed items *)
inductive pitem (S: DeqSet) : Type[0] ≝
   pz: pitem S
 | pe: pitem S
 | ps: S → pitem S
 | pp: S → pitem S
 | pc: pitem S → pitem S → pitem S
 | po: pitem S → pitem S → pitem S
 | pk: pitem S → pitem S.
 
definition pre ≝ λS.pitem S × bool.

interpretation "pitem star" 'star a = (pk ? a).
interpretation "pitem or" 'plus a b = (po ? a b).
interpretation "pitem cat" 'middot a b = (pc ? a b).
notation < ".a" non associative with precedence 90 for @{ 'pp $a}.
notation > "`. term 90 a" non associative with precedence 90 for @{ 'pp $a}.
interpretation "pitem pp" 'pp a = (pp ? a).
interpretation "pitem ps" 'ps a = (ps ? a).
interpretation "pitem epsilon" 'epsilon = (pe ?).
interpretation "pitem empty" 'empty = (pz ?).

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

definition in_prl ≝ λS : DeqSet.λp:pre S. 
  if (\snd p) then \sem{\fst p} ∪ {ϵ} else \sem{\fst p}.
  
interpretation "in_prl mem" 'mem w l = (in_prl ? l w).
interpretation "in_prl" 'in_l E = (in_prl ? E).

lemma sem_pre_true : ∀S.∀i:pitem S. 
  \sem{〈i,true〉} = \sem{i} ∪ {ϵ}. 
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

lemma append_eq_nil : ∀S.∀w1,w2:word S. w1 @ w2 = ϵ → w1 = ϵ.
#S #w1 #w2 cases w1 // #a #tl normalize #H destruct qed.

lemma not_epsilon_lp : ∀S:DeqSet.∀e:pitem S. ¬ (ϵ ∈ e).
#S #e elim e normalize /2/  
  [#r1 #r2 * #n1 #n2 % * /2/ * #w1 * #w2 * * #H 
   >(append_eq_nil …H…) /2/
  |#r1 #r2 #n1 #n2 % * /2/
  |#r #n % * #w1 * #w2 * * #H >(append_eq_nil …H…) /2/
  ]
qed.

(* lemma 12 *)
lemma epsilon_to_true : ∀S.∀e:pre S. ϵ ∈ e → \snd e = true.
#S * #i #b cases b // normalize #H @False_ind /2/ 
qed.

lemma true_to_epsilon : ∀S.∀e:pre S. \snd e = true → ϵ ∈ e.
#S * #i #b #btrue normalize in btrue; >btrue %2 // 
qed.

definition lo ≝ λS:DeqSet.λa,b:pre S.〈\fst a + \fst b,\snd a ∨ \snd b〉.
notation "a ⊕ b" left associative with precedence 60 for @{'oplus $a $b}.
interpretation "oplus" 'oplus a b = (lo ? a b).

lemma lo_def: ∀S.∀i1,i2:pitem S.∀b1,b2. 〈i1,b1〉⊕〈i2,b2〉=〈i1+i2,b1∨b2〉.
// qed.

definition pre_concat_r ≝ λS:DeqSet.λi:pitem S.λe:pre S.
  match e with [ mk_Prod i1 b ⇒ 〈i · i1, b〉].
 
notation "i ◂ e" left associative with precedence 60 for @{'ltrif $i $e}.
interpretation "pre_concat_r" 'ltrif i e = (pre_concat_r ? i e).

lemma eq_to_ex_eq: ∀S.∀A,B:word S → Prop. 
  A = B → A =1 B. 
#S #A #B #H >H /2/ qed.

lemma sem_pre_concat_r : ∀S,i.∀e:pre S.
  \sem{i ◂ e} =1 \sem{i} · \sem{|\fst e|} ∪ \sem{e}.
#S #i * #i1 #b1 cases b1 [2: @eq_to_ex_eq //] 
>sem_pre_true >sem_cat >sem_pre_true /2/ 
qed.
 
definition lc ≝ λS:DeqSet.λbcast:∀S:DeqSet.pitem S → pre S.λe1:pre S.λi2:pitem S.
  match e1 with 
  [ mk_Prod i1 b1 ⇒ match b1 with 
    [ true ⇒ (i1 ◂ (bcast ? i2)) 
    | false ⇒ 〈i1 · i2,false〉
    ]
  ].
        
definition lift ≝ λS.λf:pitem S →pre S.λe:pre S. 
  match e with 
  [ mk_Prod i b ⇒ 〈\fst (f i), \snd (f i) ∨ b〉].

notation "a ▸ b" left associative with precedence 60 for @{'lc eclose $a $b}.
interpretation "lc" 'lc op a b = (lc ? op a b).

definition lk ≝ λS:DeqSet.λbcast:∀S:DeqSet.∀E:pitem S.pre S.λe:pre S.
  match e with 
  [ mk_Prod i1 b1 ⇒
    match b1 with 
    [true ⇒ 〈(\fst (bcast ? i1))^*, true〉
    |false ⇒ 〈i1^*,false〉
    ]
  ]. 

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

lemma erase_dot : ∀S.∀e1,e2:pitem S. |e1 · e2| = c ? (|e1|) (|e2|).
// qed.

lemma erase_plus : ∀S.∀i1,i2:pitem S.
  |i1 + i2| = |i1| + |i2|.
// qed.

lemma erase_star : ∀S.∀i:pitem S.|i^*| = |i|^*. 
// qed.

lemma erase_bull : ∀S.∀i:pitem S. |\fst (•i)| = |i|.
#S #i elim i // 
  [ #i1 #i2 #IH1 #IH2 >erase_dot <IH1 >eclose_dot
    cases (•i1) #i11 #b1 cases b1 // <IH2 >odot_true_bis //
  | #i1 #i2 #IH1 #IH2 >eclose_plus >(erase_plus … i1) <IH1 <IH2
    cases (•i1) #i11 #b1 cases (•i2) #i21 #b2 //  
  | #i #IH >eclose_star >(erase_star … i) <IH cases (•i) //
  ]
qed.
  
lemma sem_eclose_star: ∀S:DeqSet.∀i:pitem S.
  \sem{〈i^*,true〉} =1 \sem{〈i,false〉}·\sem{|i|}^* ∪ {ϵ}.
/2/ qed.

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

lemma sem_fst: ∀S.∀e:pre S. \sem{\fst e} =1 \sem{e}-{[ ]}.
#S * #i * 
  [>sem_pre_true normalize in ⊢ (??%?); #w % 
    [/3/ | * * // #H1 #H2 @False_ind @(absurd …H1 H2)]
  |>sem_pre_false normalize in ⊢ (??%?); #w % [ /3/ | * // ]
  ]
qed.

lemma item_eps: ∀S.∀i:pitem S. \sem{i} =1 \sem{i}-{[ ]}.
#S #i #w % 
  [#H whd % // normalize @(not_to_not … (not_epsilon_lp …i)) //
  |* //
  ]
qed.
  
lemma sem_fst_aux: ∀S.∀e:pre S.∀i:pitem S.∀A. 
 \sem{e} =1 \sem{i} ∪ A → \sem{\fst e} =1 \sem{i} ∪ (A - {[ ]}).
#S #e #i #A #seme
@eqP_trans [|@sem_fst]
@eqP_trans [||@eqP_union_r [|@eqP_sym @item_eps]]
@eqP_trans [||@distribute_substract] 
@eqP_substract_r //
qed.

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
   @eqP_trans [||@union_assoc] /2/
  |#i #H >sem_pre_true >sem_star >erase_bull >sem_star
   @eqP_trans [|@eqP_union_r [|@cat_ext_l [|@sem_fst_aux //]]]
   @eqP_trans [|@eqP_union_r [|@distr_cat_r]]
   @eqP_trans [|@union_assoc] @eqP_union_l >erase_star 
   @eqP_sym @star_fix_eps 
  ]
qed.

definition lifted_cat ≝ λS:DeqSet.λe:pre S. 
  lift S (lc S eclose e).

notation "e1 ⊙ e2" left associative with precedence 70 for @{'odot $e1 $e2}.

interpretation "lifted cat" 'odot e1 e2 = (lifted_cat ? e1 e2).

lemma odot_true_b : ∀S.∀i1,i2:pitem S.∀b. 
  〈i1,true〉 ⊙ 〈i2,b〉 = 〈i1 · (\fst (•i2)),\snd (•i2) ∨ b〉.
#S #i1 #i2 #b normalize in ⊢ (??%?); cases (•i2) // 
qed.

lemma odot_false_b : ∀S.∀i1,i2:pitem S.∀b.
  〈i1,false〉 ⊙ 〈i2,b〉 = 〈i1 · i2 ,b〉.
// 
qed.
  
lemma erase_odot:∀S.∀e1,e2:pre S.
  |\fst (e1 ⊙ e2)| = |\fst e1| · (|\fst e2|).
#S * #i1 * * #i2 #b2 // >odot_true_b // 
qed.

lemma ostar_true: ∀S.∀i:pitem S.
  〈i,true〉^⊛ = 〈(\fst (•i))^*, true〉.
// qed.

lemma ostar_false: ∀S.∀i:pitem S.
  〈i,false〉^⊛ = 〈i^*, false〉.
// qed.
  
lemma erase_ostar: ∀S.∀e:pre S.
  |\fst (e^⊛)| = |\fst e|^*.
#S * #i * // qed.

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

(* theorem 16: 4 *)      
theorem sem_ostar: ∀S.∀e:pre S. 
  \sem{e^⊛} =1  \sem{e} · \sem{|\fst e|}^*.
#S * #i #b cases b
  [>sem_pre_true >sem_pre_true >sem_star >erase_bull
   @eqP_trans [|@eqP_union_r[|@cat_ext_l [|@sem_fst_aux //]]]
   @eqP_trans [|@eqP_union_r [|@distr_cat_r]]
   @eqP_trans [||@eqP_sym @distr_cat_r]
   @eqP_trans [|@union_assoc] @eqP_union_l
   @eqP_trans [||@eqP_sym @epsilon_cat_l] @eqP_sym @star_fix_eps 
  |>sem_pre_false >sem_pre_false >sem_star /2/
  ]
qed.
  
